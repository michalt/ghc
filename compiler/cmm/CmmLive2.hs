{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CmmLive2
    ( CmmLocalLive
    , cmmLocalLiveness
    , cmmGlobalLiveness
    , gen_kill
    )
where

import DynFlags
import BlockId
import Cmm
import PprCmmExpr ()

import Maybes
import Outputable

import Compiler.Hoopl
       (O, C, Block(..), FactBase, entryLabel, lastNode)

import Hoopl.Dataflow2

import qualified CmmLive as CmmLiveOld

-- | The variables live on entry to a block.
type CmmLive r = RegSet r
type CmmLocalLive = CmmLive LocalReg

type BlockEntryLiveness r = BlockEnv (CmmLive r)

-- | The dataflow lattice
liveLattice
    :: Ord r
    => DataflowLattice2 (CmmLive r)
liveLattice = DataflowLattice2 emptyRegSet add
  where
    add (OldFact old) (NewFact new) =
        let join = plusRegSet old new
         in changedIf (sizeRegSet join > sizeRegSet old) join
{-# SPECIALISE liveLattice :: DataflowLattice2 (CmmLive LocalReg) #-}
{-# SPECIALISE liveLattice :: DataflowLattice2 (CmmLive GlobalReg) #-}

cmmLocalLiveness :: DynFlags -> CmmGraph -> BlockEntryLiveness LocalReg
cmmLocalLiveness dflags graph =
    checkOld $ cmmLocalLiveness_ dflags graph
  where
    checkOld result
      | doAssertions = let old = CmmLiveOld.cmmLocalLiveness dflags graph
                        in if result == old
                               then result
                               else pprPanic "live2" (ppr result $$ ppr old)
      | otherwise    = result

cmmGlobalLiveness :: DynFlags -> CmmGraph -> BlockEntryLiveness GlobalReg
cmmGlobalLiveness dflags graph =
    checkOld $ cmmGlobalLiveness_ dflags graph
  where
    checkOld result
      | doAssertions = let old = CmmLiveOld.cmmGlobalLiveness dflags graph
                        in if old == result
                               then result
                               else pprPanic "live2" (ppr result $$ ppr old)
      | otherwise    = result

cmmLocalLiveness_ :: DynFlags -> CmmGraph -> BlockEntryLiveness LocalReg
cmmLocalLiveness_ dflags graph =
    check $ analyze Bwd liveLattice (xferLive dflags) graph mapEmpty
  where
    entry = g_entry graph
    check facts =
        noLiveOnEntry entry (expectJust "check" $ mapLookup entry facts) facts

cmmGlobalLiveness_ :: DynFlags -> CmmGraph -> BlockEntryLiveness GlobalReg
cmmGlobalLiveness_ dflags graph =
    analyze Bwd liveLattice (xferLive dflags) graph mapEmpty

-- | On entry to the procedure, there had better not be any LocalReg's live-in.
noLiveOnEntry :: BlockId -> CmmLive LocalReg -> a -> a
noLiveOnEntry bid in_fact x =
    if nullRegSet in_fact
        then x
        else pprPanic "LocalReg's live-in to graph" (ppr bid <+> ppr in_fact)

gen_kill :: (DefinerOfRegs r a, UserOfRegs r a, Outputable r)
          => DynFlags -> a -> CmmLive r -> CmmLive r
gen_kill dflags a set
    | doAssertions = if result == old
                        then result
                        else pprPanic "gen_kill" (ppr result $$ ppr old)
    | otherwise = result
  where
    result = gen_kill_ dflags a set
    old = CmmLiveOld.gen_kill dflags a set
{-# INLINE gen_kill #-}

gen_kill_
    :: (DefinerOfRegs r a, UserOfRegs r a)
    => DynFlags -> a -> CmmLive r -> CmmLive r
gen_kill_ dflags a set =
    let !afterKill = foldRegsDefd dflags deleteFromRegSet set a
    in foldRegsUsed dflags extendRegSet afterKill a
{-# INLINE gen_kill_ #-}


xferLive
    :: forall r.
       ( UserOfRegs r (CmmNode O O)
       , DefinerOfRegs r (CmmNode O O)
       , UserOfRegs r (CmmNode O C)
       , DefinerOfRegs r (CmmNode O C)
       )
    => DynFlags -> TransferFun Block CmmNode (CmmLive r)
xferLive dflags = transferFun
  where
    transferFun
        :: Block CmmNode C C
        -> FactBase (CmmLive r)
        -> FactBase (CmmLive r)
    transferFun block facts =
        let joined = joinOutFacts liveLattice (lastNode block) facts
            !result =
                foldBlockNodesB3Strict
                    (flip const, gen_kill_ dflags, gen_kill_ dflags)
                    block
                    joined
        in mapSingleton (entryLabel block) result
{-# SPECIALIZE xferLive
        :: DynFlags -> TransferFun Block CmmNode (CmmLive LocalReg) #-}
{-# SPECIALIZE xferLive
        :: DynFlags -> TransferFun Block CmmNode (CmmLive GlobalReg) #-}
