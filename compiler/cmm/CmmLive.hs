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

import Debug.Trace

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
    :: forall f.
       (CmmNode C O -> Fact O f -> UniqSM (CmmNode C O, f))
    -> (CmmNode O O -> Fact O f -> UniqSM (Block CmmNode O O, f))
    -> (CmmNode O C -> Fact C f -> UniqSM (CmmNode O C, f))
    -> Block CmmNode C C
    -> FactBase f
    -> UniqSM (Block CmmNode C C, f)
fold rewriteCO rewriteOO rewriteOC initBlock initFacts = go initBlock initFacts
  where
    go :: forall e x. Block CmmNode e x -> Fact x f -> UniqSM (Block CmmNode e x, f)
    go (BlockCC nodeE1 block1 nodeX1) fact1 = do
        (!nodeX2, fact2) <- rewriteOC nodeX1 fact1
        (!block2, fact3) <- go block1 fact2
        (!nodeE2, !fact4) <- rewriteCO nodeE1 fact3
        return (BlockCC nodeE2 block2 nodeX2, fact4)

    go (BlockCO node1 block1) fact1 = do
        (!node2, !block2, !fact2) <- (rewriteCO node1 `cat` go block1) fact1
        return (BlockCO node2 block2, fact2)

    go (BlockOC block1 node1) fact1 = do
        (!block2, !node2, !fact2) <- (go block1 `cat` rewriteOC node1) fact1
        return (BlockOC block2 node2, fact2)

    go (BCons node1 block1) fact1 = do
        (blockFromNode, block2, !fact2) <- (rewriteOO node1 `cat` go block1) fact1
        let !result = blockJoinOO blockFromNode block2
        return (result, fact2)

    go (BSnoc block1 node1) fact1 = do
        (block2, blockFromNode, !fact2) <- (go block1 `cat` rewriteOO node1) fact1
        let !result = blockJoinOO block2 blockFromNode
        return (result, fact2)

    go (BCat blockA1 blockB1) fact1 = do
        (blockA2, blockB2, !fact2) <- (go blockA1 `cat` go blockB1) fact1
        let !result = blockJoinOO blockA2 blockB2
        return (result, fact2)

    go (BMiddle node) fact1 = rewriteOO node fact1

    go BNil fact = return (BNil, fact)

    cat :: (f2 -> UniqSM (a, f3)) -> (f1 -> UniqSM (b, f2)) -> f1 -> UniqSM (a, b, f3)
    cat rew1 rew2 = \f1 -> do
        (b, f2) <- rew2 f1
        (a, f3) <- rew1 f2
        return (a, b, f3)
    {-# INLINE cat #-}

    blockJoinOO BNil b = b
    blockJoinOO b BNil = b
    blockJoinOO (BMiddle n) b = blockCons n b
    blockJoinOO b (BMiddle n) = blockSnoc b n
    blockJoinOO b1 b2 = BCat b1 b2


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
       -- ( UserOfRegs r (CmmNode O O)
       -- , DefinerOfRegs r (CmmNode O O)
       -- , UserOfRegs r (CmmNode O C)
       -- , DefinerOfRegs r (CmmNode O C)
       -- )
    -- => DynFlags -> CmmGraph -> UniqSM (CmmGraph, BlockEnv (CmmLive r))
removeDeadAssignments dflags cmmGraph = do
    trace ("\n###before\n" ++ showSDocUnsafe (ppr cmmGraph) ++ "\n") $ return ()
    (g,  f) <- rewriteBwd liveLattice rewriteCC cmmGraph emptyBlockMap
    trace ("\n###after\n" ++ showSDocUnsafe (ppr g) ++ "\n") $ return ()
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
    isDead a@(CmmAssign (CmmLocal reg) _) live
        | not (reg `elemRegSet` live) = trace ("### killing " ++ showSDocUnsafe (ppr a)) True
    isDead (CmmAssign lhs (CmmReg rhs))   _ | lhs == rhs = True
    isDead (CmmStore lhs (CmmLoad rhs _)) _ | lhs == rhs = True
    isDead node _ = False


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
