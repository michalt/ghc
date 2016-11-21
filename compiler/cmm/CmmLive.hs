{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CmmLive
    ( CmmLocalLive
    , cmmLocalLiveness
    , cmmGlobalLiveness
    , liveLattice
    , gen_kill
    , removeDeadAssignments
    )
where

import DynFlags
import BlockId
import Cmm
import PprCmmExpr ()
import Hoopl
import UniqSupply
import PprCmm ()

import Maybes
import Outputable

-----------------------------------------------------------------------------
-- Calculating what variables are live on entry to a basic block
-----------------------------------------------------------------------------

-- | The variables live on entry to a block
type CmmLive r = RegSet r
type CmmLocalLive = CmmLive LocalReg

-- | The dataflow lattice
liveLattice :: Ord r => DataflowLattice (CmmLive r)
{-# SPECIALIZE liveLattice :: DataflowLattice (CmmLive LocalReg) #-}
{-# SPECIALIZE liveLattice :: DataflowLattice (CmmLive GlobalReg) #-}
liveLattice = DataflowLattice emptyRegSet add
  where
    add (OldFact old) (NewFact new) =
        let !join = plusRegSet old new
        in changedIf (sizeRegSet join > sizeRegSet old) join

-- | A mapping from block labels to the variables live on entry
type BlockEntryLiveness r = BlockEnv (CmmLive r)

-----------------------------------------------------------------------------
-- | Calculated liveness info for a CmmGraph
-----------------------------------------------------------------------------

cmmLocalLiveness :: DynFlags -> CmmGraph -> BlockEntryLiveness LocalReg
cmmLocalLiveness dflags graph =
    check $ analyzeCmmBwd liveLattice (xferLive dflags) graph mapEmpty
  where
    entry = g_entry graph
    check facts =
        noLiveOnEntry entry (expectJust "check" $ mapLookup entry facts) facts

cmmGlobalLiveness :: DynFlags -> CmmGraph -> BlockEntryLiveness GlobalReg
cmmGlobalLiveness dflags graph =
    analyzeCmmBwd liveLattice (xferLive dflags) graph mapEmpty

-- | On entry to the procedure, there had better not be any LocalReg's live-in.
noLiveOnEntry :: BlockId -> CmmLive LocalReg -> a -> a
noLiveOnEntry bid in_fact x =
  if nullRegSet in_fact then x
  else pprPanic "LocalReg's live-in to graph" (ppr bid <+> ppr in_fact)

gen_kill
    :: (DefinerOfRegs r n, UserOfRegs r n)
    => DynFlags -> n -> CmmLive r -> CmmLive r
gen_kill dflags node set =
    let !afterKill = foldRegsDefd dflags deleteFromRegSet set node
    in foldRegsUsed dflags extendRegSet afterKill node
{-# INLINE gen_kill #-}

xferLive
    :: forall r.
       ( UserOfRegs r (CmmNode O O)
       , DefinerOfRegs r (CmmNode O O)
       , UserOfRegs r (CmmNode O C)
       , DefinerOfRegs r (CmmNode O C)
       )
    => DynFlags -> TransferFun (CmmLive r)
xferLive dflags (BlockCC eNode middle xNode) fBase =
    let joined = gen_kill dflags xNode $! joinOutFacts liveLattice xNode fBase
        !result = foldNodesBwdOO (gen_kill dflags) middle joined
    in mapSingleton (entryLabel eNode) result
{-# SPECIALIZE xferLive :: DynFlags -> TransferFun (CmmLive LocalReg) #-}
{-# SPECIALIZE xferLive :: DynFlags -> TransferFun (CmmLive GlobalReg) #-}



foldOO
    :: forall f.
       (CmmNode O O -> f -> UniqSM (Block CmmNode O O, f))
    -> Block CmmNode O O
    -> f
    -> UniqSM (Block CmmNode O O, f)
foldOO rewriteOO initBlock initFacts = go initBlock initFacts
  where
    go (BCons node1 block1) fact1 = (rewriteOO node1 `comp` go block1) fact1
    go (BSnoc block1 node1) fact1 = (go block1 `comp` rewriteOO node1) fact1
    go (BCat blockA1 blockB1) fact1 = (go blockA1 `comp` go blockB1) fact1
    go (BMiddle node) fact1 = rewriteOO node fact1
    go BNil fact = return (BNil, fact)

    comp rew1 rew2 = \f1 -> do
        (b, f2) <- rew2 f1
        (a, !f3) <- rew1 f2
        let !c = joinOO a b
        return (c, f3)
    {-# INLINE comp #-}

    joinOO BNil b = b
    joinOO b BNil = b
    joinOO (BMiddle n) b = blockCons n b
    joinOO b (BMiddle n) = blockSnoc b n
    joinOO b1 b2 = BCat b1 b2

-- FIXME: Question: Should we have a separate argument for transfer functions
-- and for rewrites? How should they be combined? Should we run the transfer on
-- the removed block????
removeDeadAssignments
    :: DynFlags -> CmmGraph -> UniqSM (CmmGraph, BlockEnv (CmmLive LocalReg))
removeDeadAssignments dflags cmmGraph = do
    -- trace ("\n###before\n" ++ showSDocUnsafe (ppr cmmGraph) ++ "\n") $ return ()
    (g,  f) <- rewriteCmmBwd liveLattice rewriteCC cmmGraph emptyBlockMap
    -- trace ("\n###after\n" ++ showSDocUnsafe (ppr g) ++ "\n") $ return ()
    return (g, f)
  where
    rewriteCC
        :: Block CmmNode C C
        -> FactBase (CmmLive LocalReg)
        -> UniqSM (Block CmmNode C C, FactBase (CmmLive LocalReg))
    rewriteCC (BlockCC eNode middle1 xNode) factBase = do
        let facts1 = gen_kill dflags xNode $! joinOutFacts liveLattice xNode factBase
        (middle2, !facts2) <-  foldOO rewriteNode middle1 facts1
        return (BlockCC eNode middle2 xNode, mapSingleton (entryLabel eNode) facts2)

    rewriteNode node facts1 =
        case isDead node facts1 of
            True -> return (BNil, facts1)
            False -> do
                let !facts2 = gen_kill dflags node facts1
                return (BMiddle node, facts2)

    isDead :: CmmNode O O -> (CmmLive LocalReg) -> Bool
    isDead (CmmAssign (CmmLocal reg) _) live
        | not (reg `elemRegSet` live) = True -- trace ("### killing " ++ showSDocUnsafe (ppr a)) True
    isDead (CmmAssign lhs (CmmReg rhs))   _ | lhs == rhs = True
    isDead (CmmStore lhs (CmmLoad rhs _)) _ | lhs == rhs = True
    isDead _ _ = False
