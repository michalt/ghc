{-# LANGUAGE CPP #-}
-- ----------------------------------------------------------------------------
-- | Handle conversion of CmmData to LLVM code.
--

module LlvmCodeGen.Data (
        genLlvmData, genData, cvtForMangler
    ) where

#include "HsVersions.h"

import GhcPrelude

import Llvm
import LlvmCodeGen.Base
import LlvmMangler ( ManglerStr )

import BlockId
import CLabel
import Cmm
import DynFlags
import Platform

import FastString
import Outputable
import qualified Data.ByteString.Char8 as B

-- ----------------------------------------------------------------------------
-- * Constants
--

-- | The string appended to a variable name to create its structure type alias
structStr :: LMString
structStr = fsLit "_struct"

-- ----------------------------------------------------------------------------
-- * Top level
--

-- | Pass a CmmStatic section to an equivalent Llvm code.
genLlvmData :: (Section, CmmStatics) -> LlvmM LlvmData
genLlvmData (sec, Statics lbl xs) = do
    label <- strCLabel_llvm lbl
    static <- mapM genData xs
    lmsec <- llvmSection sec
    let types   = map getStatType static

        strucTy = LMStruct types
        tyAlias = LMAlias ((label `appendFS` structStr), strucTy)

        struct         = Just $ LMStaticStruc static tyAlias
        link           = if (externallyVisibleCLabel lbl)
                            then ExternallyVisible else Internal
        align          = case sec of
                            Section CString _ -> Just 1
                            _                 -> Nothing
        const          = if isSecConstant sec then Constant else Global
        varDef         = LMGlobalVar label tyAlias link lmsec align const
        globDef        = LMGlobal varDef struct

    return ([globDef], [tyAlias])

-- | Format the section type part of a Cmm Section
llvmSectionType :: Platform -> SectionType -> FastString
llvmSectionType p t = case t of
    Text                    -> fsLit ".text"
    ReadOnlyData            -> case platformOS p of
                                 OSMinGW32 -> fsLit ".rdata"
                                 _         -> fsLit ".rodata"
    RelocatableReadOnlyData -> case platformOS p of
                                 OSMinGW32 -> fsLit ".rdata$rel.ro"
                                 _         -> fsLit ".data.rel.ro"
    ReadOnlyData16          -> case platformOS p of
                                 OSMinGW32 -> fsLit ".rdata$cst16"
                                 _         -> fsLit ".rodata.cst16"
    Data                    -> fsLit ".data"
    UninitialisedData       -> fsLit ".bss"
    CString                 -> case platformOS p of
                                 OSMinGW32 -> fsLit ".rdata$str"
                                 _         -> fsLit ".rodata.str"
    (OtherSection _)        -> panic "llvmSectionType: unknown section type"

-- | Format a Cmm Section into a LLVM section name
llvmSection :: Section -> LlvmM LMSection
llvmSection (Section t suffix) = do
  dflags <- getDynFlags
  let splitSect = gopt Opt_SplitSections dflags
      platform  = targetPlatform dflags
  if not splitSect
  then return Nothing
  else do
    lmsuffix <- strCLabel_llvm suffix
    let result sep = Just (concatFS [llvmSectionType platform t
                                    , fsLit sep, lmsuffix])
    case platformOS platform of
      OSMinGW32 -> return (result "$")
      _         -> return (result ".")

-- ----------------------------------------------------------------------------
-- * Generate static data
--

-- | Handle static data
genData :: CmmStatic -> LlvmM LlvmStatic

genData (CmmString str) = do
    let v  = map (\x -> LMStaticLit $ LMIntLit (fromIntegral x) i8) str
        ve = v ++ [LMStaticLit $ LMIntLit 0 i8]
    return $ LMStaticArray ve (LMArray (length ve) i8)

genData (CmmUninitialised bytes)
    = return $ LMUninitType (LMArray bytes i8)

genData (CmmStaticLit lit)
    = genStaticLit lit

-- | Generate Llvm code for a static literal.
--
-- Will either generate the code or leave it unresolved if it is a 'CLabel'
-- which isn't yet known.
genStaticLit :: CmmLit -> LlvmM LlvmStatic
genStaticLit (CmmInt i w)
    = return $ LMStaticLit (LMIntLit i (LMInt $ widthInBits w))

genStaticLit (CmmFloat r w)
    = return $ LMStaticLit (LMFloatLit (fromRational r) (widthToLlvmFloat w))

genStaticLit (CmmVec ls)
    = do sls <- mapM toLlvmLit ls
         return $ LMStaticLit (LMVectorLit sls)
  where
    toLlvmLit :: CmmLit -> LlvmM LlvmLit
    toLlvmLit lit = do
      slit <- genStaticLit lit
      case slit of
        LMStaticLit llvmLit -> return llvmLit
        _ -> panic "genStaticLit"

-- Leave unresolved, will fix later
genStaticLit cmm@(CmmLabel l) = do
    var <- getGlobalPtr =<< strCLabel_llvm l
    dflags <- getDynFlags
    let ptr = LMStaticPointer var
        lmty = cmmToLlvmType $ cmmLitType dflags cmm
    return $ LMPtoI ptr lmty

genStaticLit (CmmLabelOff label off) = do
    dflags <- getDynFlags
    var <- genStaticLit (CmmLabel label)
    let offset = LMStaticLit $ LMIntLit (toInteger off) (llvmWord dflags)
    return $ LMAdd var offset

genStaticLit (CmmLabelDiffOff l1 l2 off) = do
    dflags <- getDynFlags
    var1 <- genStaticLit (CmmLabel l1)
    var2 <- genStaticLit (CmmLabel l2)
    let var = LMSub var1 var2
        offset = LMStaticLit $ LMIntLit (toInteger off) (llvmWord dflags)
    return $ LMAdd var offset

genStaticLit (CmmBlock b) = genStaticLit $ CmmLabel $ infoTblLbl b

genStaticLit (CmmHighStackMark)
    = panic "genStaticLit: CmmHighStackMark unsupported!"
    

-- | Convert a CmmStatic into a byte string for the LLVM mangler.
-- The mangler will insert the ManglerStr representations of the
-- CmmStatic at return points of a cpscall.
cvtForMangler :: CmmStatics -> LlvmM ManglerStr
cvtForMangler (Statics _ datum) =
        mapM cvtStatic datum
    where
        cvtStatic :: CmmStatic -> LlvmM (B.ByteString -> B.ByteString)
        cvtStatic (CmmStaticLit lit) = cvtLit lit
        
        -- XXX these are not expected to appear at return points at the moment.
        cvtStatic (CmmUninitialised _) = error "cvtStatic -- uninit unhandled"
        cvtStatic (CmmString _) = error "cvtStatic -- string unhandled"
        
        
        cvtLit _ = return $ test $ B.pack "## todo: some other CmmLit for " 
        
        some bstr _ = bstr
        
        test bstr lab = B.concat [
                bstr,
                lab,
                B.pack "\n"
            ]
        
        -- eol = "\n"
        -- 
        -- emitInfo label (Statics _ statics) = 
        --     -- TODO(kavon): maybe put an alignment directive first?
        --     B.concat $ (map staticToByteStr statics) ++ [label]
        --     
        -- staticToByteStr :: CmmStatic -> B.ByteString
        -- staticToByteStr (CmmUninitialised sz) = let
        --         width = gcd sz 8
        --         zeroes = take (sz `div` width) ['0','0'..]
        --         name = szName width
        --     in
        --         B.pack $ name ++ (intersperse ',' zeroes) ++ eol
        -- 
        -- staticToByteStr (CmmStaticLit (CmmLabelDiffOff _ _ _)) = B.pack "# label diff static\n"
        --         
        -- staticToByteStr _ = B.pack "# todo: other static\n"
        --         
        -- -- TODO(kavon): does this change on ARM?
        -- -- translate a size (in bytes) to its assembly directive, followed by a space.
        -- szName :: Int -> String
        -- szName 1 = ".byte "
        -- szName 2 = ".value "
        -- szName 4 = ".long "
        -- szName 8 = ".quad "
        -- szName _ = error "szName -- invalid byte width"
        
        
