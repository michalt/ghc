-- Cmm representations using Hoopl's Graph CmmNode e x.
{-# LANGUAGE CPP, GADTs #-}

module Cmm (
     -- * Cmm top-level datatypes
     CmmProgram, CmmGroup, CmmGroupPlus, GenCmmGroup,
     CmmDecl, CmmDeclPlus, GenCmmDecl(..),
     CmmGraph, GenCmmGraph(..),
     CmmBlock, CmmRetTy,
     RawCmmDecl, RawCmmDeclPlus, RawCmmGroup, RawCmmGroupPlus,
     Section(..), SectionType(..), CmmStatics(..), CmmStatic(..),
     isSecConstant,

     -- ** Blocks containing lists
     GenBasicBlock(..), blockId,
     ListGraph(..), pprBBlock,

     -- * Info Tables
     CmmTopInfo(..), CmmStackInfo(..), CmmInfoTable(..), topInfoTable,
     ClosureTypeInfo(..),
     C_SRT(..), needsSRT,
     ProfilingInfo(..), ConstrDescription,
     discardRetTy, discardRetTys, toCmmPlus, addRetTy,

     -- * Statements, expressions and types
     module CmmNode,
     module CmmExpr,
  ) where

import GhcPrelude

import CLabel
import BlockId
import CmmNode
import SMRep
import CmmExpr
import Hoopl.Block
import Hoopl.Collections
import Hoopl.Graph
import Hoopl.Label
import Outputable

import Data.Word        ( Word8 )

#include "HsVersions.h"

-----------------------------------------------------------------------------
--  Cmm, GenCmm
-----------------------------------------------------------------------------

-- A CmmProgram is a list of CmmGroups
-- A CmmGroup is a list of top-level declarations

-- When object-splitting is on, each group is compiled into a separate
-- .o file. So typically we put closely related stuff in a CmmGroup.
-- Section-splitting follows suit and makes one .text subsection for each
-- CmmGroup.

type CmmProgram = [CmmGroup]

type GenCmmGroup d h g = [GenCmmDecl d h g]

type CmmGroupPlus = GenCmmGroup CmmStatics (CmmTopInfo, CmmRetTy) CmmGraph
type CmmGroup = GenCmmGroup CmmStatics CmmTopInfo CmmGraph

type RawCmmGroup = GenCmmGroup CmmStatics (LabelMap CmmStatics) CmmGraph
type RawCmmGroupPlus = GenCmmGroup CmmStatics (LabelMap CmmStatics, CmmRetTy) CmmGraph

type CmmRetTy = Maybe [CmmType]

-----------------------------------------------------------------------------
--  CmmDecl, GenCmmDecl
-----------------------------------------------------------------------------

-- GenCmmDecl is abstracted over
--   d, the type of static data elements in CmmData
--   h, the static info preceding the code of a CmmProc
--   g, the control-flow graph of a CmmProc
--
-- We expect there to be two main instances of this type:
--   (a) C--, i.e. populated with various C-- constructs
--   (b) Native code, populated with data/instructions

-- | A top-level chunk, abstracted over the type of the contents of
-- the basic blocks (Cmm or instructions are the likely instantiations).
data GenCmmDecl d h g
  = CmmProc     -- A procedure
     h                 -- Extra header such as the info table
     CLabel            -- Entry label
     [GlobalReg]       -- Registers live on entry. Note that the set of live
                       -- registers will be correct in generated C-- code, but
                       -- not in hand-written C-- code. However,
                       -- splitAtProcPoints calculates correct liveness
                       -- information for CmmProcs.
     g                 -- Control-flow graph for the procedure's code

  | CmmData     -- Static data
        Section
        d

type CmmDeclPlus = GenCmmDecl CmmStatics (CmmTopInfo, CmmRetTy) CmmGraph
type CmmDecl = GenCmmDecl CmmStatics CmmTopInfo CmmGraph

type RawCmmDecl
   = GenCmmDecl
        CmmStatics
        (LabelMap CmmStatics)
        CmmGraph
        
type RawCmmDeclPlus
   = GenCmmDecl
        CmmStatics
        (LabelMap CmmStatics, CmmRetTy)
        CmmGraph

-----------------------------------------------------------------------------
--     Graphs
-----------------------------------------------------------------------------

type CmmGraph = GenCmmGraph CmmNode
data GenCmmGraph n = CmmGraph { g_entry :: BlockId, g_graph :: Graph n C C }
type CmmBlock = Block CmmNode C C

-----------------------------------------------------------------------------
--     Info Tables
-----------------------------------------------------------------------------

data CmmTopInfo   = TopInfo { info_tbls  :: LabelMap CmmInfoTable
                            , stack_info :: CmmStackInfo }

topInfoTable :: GenCmmDecl a CmmTopInfo (GenCmmGraph n) -> Maybe CmmInfoTable
topInfoTable (CmmProc infos _ _ g) = mapLookup (g_entry g) (info_tbls infos)
topInfoTable _                     = Nothing

data CmmStackInfo
   = StackInfo {
       arg_space :: ByteOff,
               -- number of bytes of arguments on the stack on entry to the
               -- the proc.  This is filled in by StgCmm.codeGen, and used
               -- by the stack allocator later.
       updfr_space :: Maybe ByteOff,
               -- XXX: this never contains anything useful, but it should.
               -- See comment in CmmLayoutStack.
       do_layout :: Bool
               -- Do automatic stack layout for this proc.  This is
               -- True for all code generated by the code generator,
               -- but is occasionally False for hand-written Cmm where
               -- we want to do the stack manipulation manually.
  }

-- | Info table as a haskell data type
data CmmInfoTable
  = CmmInfoTable {
      cit_lbl  :: CLabel, -- Info table label
      cit_rep  :: SMRep,
      cit_prof :: ProfilingInfo,
      cit_srt  :: C_SRT
    }

data ProfilingInfo
  = NoProfilingInfo
  | ProfilingInfo [Word8] [Word8] -- closure_type, closure_desc

-- C_SRT is what StgSyn.SRT gets translated to...
-- we add a label for the table, and expect only the 'offset/length' form

data C_SRT = NoC_SRT
           | C_SRT !CLabel !WordOff !StgHalfWord {-bitmap or escape-}
           deriving (Eq)

needsSRT :: C_SRT -> Bool
needsSRT NoC_SRT       = False
needsSRT (C_SRT _ _ _) = True

-----------------------------------------------------------------------------
--        Adding and removing return type information in the header.
-----------------------------------------------------------------------------

addRetTy :: GenCmmDecl d h g -> CmmRetTy -> GenCmmDecl d (h, CmmRetTy) g
addRetTy (CmmProc h lab live g) retTy =
    (CmmProc (h, retTy) lab live g)
addRetTy (CmmData s d) _ = CmmData s d

-- adds dummy return type info to the given group
toCmmPlus :: GenCmmGroup d h g -> GenCmmGroup d (h, CmmRetTy) g
toCmmPlus group = map (flip addRetTy Nothing) group

discardRetTys :: GenCmmGroup d (h, CmmRetTy) g -> GenCmmGroup d h g
discardRetTys group = map discardRetTy group

discardRetTy :: GenCmmDecl d (h, CmmRetTy) g -> GenCmmDecl d h g
discardRetTy (CmmProc (h, _) lab live g) = CmmProc h lab live g
discardRetTy (CmmData s d) = CmmData s d

-----------------------------------------------------------------------------
--              Static Data
-----------------------------------------------------------------------------

data SectionType
  = Text
  | Data
  | ReadOnlyData
  | RelocatableReadOnlyData
  | UninitialisedData
  | ReadOnlyData16      -- .rodata.cst16 on x86_64, 16-byte aligned
  | CString
  | OtherSection String
  deriving (Show)

-- | Should a data in this section be considered constant
isSecConstant :: Section -> Bool
isSecConstant (Section t _) = case t of
    Text                    -> True
    ReadOnlyData            -> True
    RelocatableReadOnlyData -> True
    ReadOnlyData16          -> True
    CString                 -> True
    Data                    -> False
    UninitialisedData       -> False
    (OtherSection _)        -> False

data Section = Section SectionType CLabel

data CmmStatic
  = CmmStaticLit CmmLit
        -- a literal value, size given by cmmLitRep of the literal.
  | CmmUninitialised Int
        -- uninitialised data, N bytes long
  | CmmString [Word8]
        -- string of 8-bit values only, not zero terminated.

data CmmStatics
   = Statics
       CLabel      -- Label of statics
       [CmmStatic] -- The static data itself

-- -----------------------------------------------------------------------------
-- Basic blocks consisting of lists

-- These are used by the LLVM and NCG backends, when populating Cmm
-- with lists of instructions.

data GenBasicBlock i = BasicBlock BlockId [i]

-- | The branch block id is that of the first block in
-- the branch, which is that branch's entry point
blockId :: GenBasicBlock i -> BlockId
blockId (BasicBlock blk_id _ ) = blk_id

newtype ListGraph i = ListGraph [GenBasicBlock i]

instance Outputable instr => Outputable (ListGraph instr) where
    ppr (ListGraph blocks) = vcat (map ppr blocks)

instance Outputable instr => Outputable (GenBasicBlock instr) where
    ppr = pprBBlock

pprBBlock :: Outputable stmt => GenBasicBlock stmt -> SDoc
pprBBlock (BasicBlock ident stmts) =
    hang (ppr ident <> colon) 4 (vcat (map ppr stmts))
