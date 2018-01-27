-- -----------------------------------------------------------------------------
-- | GHC LLVM Mangler
--
-- This script processes the assembly produced by LLVM, rewriting all symbols
-- of type @function to @object. This keeps them from going through the PLT,
-- which would be bad due to tables-next-to-code. On x86_64,
-- it also rewrites AVX instructions that require alignment to their
-- unaligned counterparts, since the stack is only 16-byte aligned but these
-- instructions require 32-byte alignment.
--

module LlvmMangler ( llvmFixupAsm, ManglerInfo, ManglerStr ) where

import GhcPrelude

import DynFlags ( DynFlags, targetPlatform )
import Platform ( platformArch, Arch(..) )
import ErrUtils ( withTiming )
import Outputable ( text )

import Control.Exception
import qualified Data.ByteString.Char8 as B
import System.IO
import Compiler.Hoopl
import Compiler.Hoopl.Internals ( uniqueToLbl )
import Data.Maybe ( fromMaybe )

type ManglerStr = B.ByteString
type ManglerInfo = Maybe (LabelMap ManglerStr)

-- | Read in assembly file and process
llvmFixupAsm :: DynFlags -> LabelMap ManglerStr -> FilePath -> FilePath -> IO ()
llvmFixupAsm dflags gcInfo f1 f2 = {-# SCC "llvm_mangler" #-}
    withTiming (pure dflags) (text "LLVM Mangler") id $
    withBinaryFile f1 ReadMode $ \r -> withBinaryFile f2 WriteMode $ \w -> do
        go r w
        hClose r
        hClose w
        return ()
  where
    doRewrite a = rewriteLine dflags (labRewrites gcInfo) rewrites a
    
    go :: Handle -> Handle -> IO ()
    go r w = do
      e_l <- try $ B.hGetLine r ::IO (Either IOError B.ByteString)
      let writeline a = B.hPutStrLn w (doRewrite a) >> go r w
      case e_l of
        Right l -> writeline l
        Left _  -> return ()

-- | These are the non-label rewrites that the mangler will perform
rewrites :: [Rewrite]
rewrites = [rewriteSymType, rewriteAVX]

-- | These are the label-based rewrites that the mangler will perform
labRewrites :: LabelMap ManglerStr -> [Rewrite]
labRewrites info = [addInfoTable info]

type Rewrite = DynFlags -> B.ByteString -> Maybe B.ByteString

-- XXX(kavon): debug only delete me later
withComment :: String -> B.ByteString -> B.ByteString
withComment com line = B.concat [B.pack $ wrap com, line]
    where
        wrap c = "## comment -- " ++ c ++ "\n"

-- | This rewrite looks for return points of a llvm.cpscall and adds GC info
-- above that label.
addInfoTable :: LabelMap ManglerStr -> Rewrite
addInfoTable info _ line = do
        labName <- B.stripPrefix labPrefix line
        (i, _) <- B.readInt labName
        statics <- mapLookup (toKey i) info
        return $ withComment ("found statics for: " ++ show i) line
        -- return $ emitInfo line statics

    where
        labPrefix = B.pack "L" -- TODO(kavon): check if this changes on different platforms.
        toKey = uniqueToLbl . intToUnique
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
            

-- | Rewrite a line of assembly source with the given rewrites,
-- taking the first rewrite that applies for each kind of rewrite (label and non-label).
rewriteLine :: DynFlags -> [Rewrite] -> [Rewrite] -> B.ByteString -> B.ByteString
rewriteLine dflags labRewrites rewrites l =
  -- We disable .subsections_via_symbols on darwin and ios, as the llvm code
  -- gen uses prefix data for the info table.  This however does not prevent
  -- llvm from generating .subsections_via_symbols, which in turn with
  -- -dead_strip, strips the info tables, and therefore breaks ghc.
  | isSubsectionsViaSymbols l =
    (B.pack "## no .subsection_via_symbols for ghc. We need our info tables!")
  | otherwise =
    case (maybNewSym, maybNewRest) of
        (Nothing, Nothing) -> l -- avoid concat
        (newS, newR)       -> cat (fromMaybe symbol newS) (fromMaybe rest newR)
  where
    cat sym rst = B.concat $ [sym, B.pack "\t", rst]

    findRwOf txt rws = firstJust $ map (\rw -> rw dflags txt) rws

    (symbol, rest) = splitLine l
    maybNewSym = findRwOf symbol labRewrites  -- check for new label part
    maybNewRest = findRwOf rest rewrites      -- check for new non-label part

    firstJust :: [Maybe a] -> Maybe a
    firstJust (jx@(Just _):_) = jx
    firstJust []         = Nothing
    firstJust (_:rest)   = firstJust rest

-- | This rewrites @.type@ annotations of function symbols to @%object@.
-- This is done as the linker can relocate @%functions@ through the
-- Procedure Linking Table (PLT). This is bad since we expect that the
-- info table will appear directly before the symbol's location. In the
-- case that the PLT is used, this will be not an info table but instead
-- some random PLT garbage.
rewriteSymType :: Rewrite
rewriteSymType _ l
  | isType l  = Just $ rewrite '@' $ rewrite '%' l
  | otherwise = Nothing
  where
    isType = B.isPrefixOf (B.pack ".type")

    rewrite :: Char -> B.ByteString -> B.ByteString
    rewrite prefix = replaceOnce funcType objType
      where
        funcType = prefix `B.cons` B.pack "function"
        objType  = prefix `B.cons` B.pack "object"

-- | This rewrites aligned AVX instructions to their unaligned counterparts on
-- x86-64. This is necessary because the stack is not adequately aligned for
-- aligned AVX spills, so LLVM would emit code that adjusts the stack pointer
-- and disable tail call optimization. Both would be catastrophic here so GHC
-- tells LLVM that the stack is 32-byte aligned (even though it isn't) and then
-- rewrites the instructions in the mangler.
rewriteAVX :: Rewrite
rewriteAVX dflags s
  | not isX86_64 = Nothing
  | isVmovdqa s  = Just $ replaceOnce (B.pack "vmovdqa") (B.pack "vmovdqu") s
  | isVmovap s   = Just $ replaceOnce (B.pack "vmovap") (B.pack "vmovup") s
  | otherwise    = Nothing
  where
    isX86_64 = platformArch (targetPlatform dflags) == ArchX86_64
    isVmovdqa = B.isPrefixOf (B.pack "vmovdqa")
    isVmovap = B.isPrefixOf (B.pack "vmovap")

-- | @replaceOnce match replace bs@ replaces the first occurrence of the
-- substring @match@ in @bs@ with @replace@.
replaceOnce :: B.ByteString -> B.ByteString -> B.ByteString -> B.ByteString
replaceOnce matchBS replaceOnceBS = loop
  where
    loop :: B.ByteString -> B.ByteString
    loop cts =
        case B.breakSubstring matchBS cts of
          (hd,tl) | B.null tl -> hd
                  | otherwise -> hd `B.append` replaceOnceBS `B.append`
                                 B.drop (B.length matchBS) tl

-- | This function splits a line of assembly code into the label and the
-- rest of the code.
splitLine :: B.ByteString -> (B.ByteString, B.ByteString)
splitLine l = (symbol, B.dropWhile isSpace rest)
  where
    isSpace ' ' = True
    isSpace '\t' = True
    isSpace _ = False
    (symbol, rest) = B.span (not . isSpace) l
