{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CmmLive
    ( CmmLocalLive
    , cmmLocalLiveness
    , cmmGlobalLiveness
    , liveLattice
    , gen_kill
    )
where

import DynFlags
import BlockId
import Cmm
import PprCmmExpr ()
import Hoopl
import UniqSupply

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


-- IDEA:
-- * define `cat` function for composition (as below)
-- * return BNil when deleting a CmmNode (so this fold is general for every
--   transformation that goes CmmNode -> CmmNode!)
-- * make sure to inline `cat`
-- * profit!
fold
    :: (forall e x. CmmNode e x -> Fact f x -> (CmmNode e x, f))
    -> Block CmmNode e x
    -> Fact f x
    -> UniqSM (Block CmmNodee e x, f)
fold rewrite_node initBlock initFacts = go initBlock initFacts
  where
    go BNil fact = return (block, fact)
    go (BlockCC entry middle exit) fact1 = do
        (exit2, fact2) <- rewrite_node exit fact1
        (middle2, fact3) <- fold rewrite_node middle fact2
        (entry2, fact4) <- rewrite_node entry fact3
        return $! undefined
    go (BlockCO node1 block1) fact1 = do
        (node2, block2, fact2) <- (rewrite_node node1 `cat` go rewrite_node block1) fact1
        (blockCons node2 block2, fact2)
        case mnode2 of
            Just (node2, fact3) -> return $! BlockCO node2 fact3
            Nothing -> block2

    cat :: (f -> UniqSM a) -> (f -> UniqSM b) -> UniqSM (a, b, f)
    cat rew1 rew2 f1 = do
        (a, f2) <- rew2 f1
        (b, f3) <- rew1 f2
        return (a, b, f3)

removeDeadAssignments
    :: forall r.
       ( UserOfRegs r (CmmNode O O)
       , DefinerOfRegs r (CmmNode O O)
       , UserOfRegs r (CmmNode O C)
       , DefinerOfRegs r (CmmNode O C)
       )
    => CmmGraph -> UniqSM (CmmGraph, BlockEnv (CmmLive r))
removeDeadAssignments cmmGraph =
    rewriteBwd liveLattice rewriteFun cmmGraph emptyBlockMap
  where
    rewriteFun :: Block CmmNode C C -> FactBase f -> UniqSM (Block CmmNode C C, FactBase f)
    rewriteFun = undefined


    -- getNode :: CmmNode O O -> f -> Maybe (CmmNode O O)
    -- getNode (CmmAssign (CmmLocal reg) _) live
    --     | not (reg `elemRegSet` live) = Nothing
    -- getNode (CmmAssign lhs (CmmReg rhs)) _ | lhs == rhs = Nothing
    -- getNode (CmmStore lhs (CmmLoad rhs _)) _ | lhs == rhs = Nothing
    -- getNode node _ = Just node


    -- How should an interface based on a fold over a block look like???
    --
    -- We should have
    --   do_node :: node -> fact -> (node, fact)
    -- then the fold is
    --   facts = process last node
    --   go block blockWithLastNode factsAfterLastNode
    --
    --   go currentBlock accBlock accFacts
    --   go (Block node block) =
    --     let (newBlock1, newFacts1) = go block accBlock accFacts
    --         newBlock2 = if useful node facts then node <> block else block
    --         newFacts2 = analyze node
    --     in (newBlock2, 



{-
    go BNil f = f
    go (BlockCO n b) f = ftr n $! go b f
    go (BlockCC l b n) f = ftr l $! go b $! ltr n f
    go (BlockOC b n) f = go b $! ltr n f
    go (BMiddle n) f = mtr n f
    go (BCat b1 b2) f = go b1 $! go b2 f
    go (BSnoc h n) f = go h $! mtr n f
    go (BCons n t) f = mtr n $! go t f

    middle :: CmmNode O O -> Fact O CmmLive -> CmmReplGraph O O
    middle (CmmAssign (CmmLocal reg') _) live
            | not (reg' `elemRegSet` live)
            = return $ Just emptyGraph
    -- XXX maybe this should be somewhere else...
    middle (CmmAssign lhs (CmmReg rhs))   _ | lhs == rhs
            = return $ Just emptyGraph
    middle (CmmStore lhs (CmmLoad rhs _)) _ | lhs == rhs
            = return $ Just emptyGraph
    middle _ _ = return Nothing

    nothing :: CmmNode e x -> Fact x CmmLive -> CmmReplGraph e x
    nothing _ _ = return Nothing
-}
