{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Hoopl.Dataflow2
  ( DataflowLattice2(..)
  , Direction(..)
  , Fact
  , JoinFun
  , JoinedFact(..)
  , NewFact(..)
  , OldFact(..)
  , TransferFun
  , analyze
  , changedIf
  , foldBlockNodesB3Strict
  , joinOutFacts
  , mkFactBase
  , doAssertions  -- temporary
  ) where

import           Data.Array
import           Data.Maybe
import           Data.List

import           Cmm            (CmmGraph, CmmNode, g_entry, g_graph)
import           Compiler.Hoopl (Block (..), Body, C, FactBase, Graph' (GMany), IndexedCO,
                                 Label, LabelMap, LabelsPtr, MaybeO (..),
                                 NonLocal, O, entryLabel, lookupFact, mapEmpty,
                                 mapFindWithDefault, mapFoldWithKey, mapInsert,
                                 mapInsertWith, mapKeys, mapLookup, mapNull,
                                 postorder_dfs_from, successors)

doAssertions :: Bool
doAssertions = True

data JoinedFact a
    = Changed !a
    | NotChanged !a
    deriving (Eq, Ord)

getJoined :: JoinedFact a -> a
getJoined (Changed a) = a
getJoined (NotChanged a) = a

changedIf :: Bool -> a -> JoinedFact a
changedIf True = Changed
changedIf False = NotChanged

data DataflowLattice2 a = DataflowLattice2
    { fact_bot2 :: a
    , fact_join2 :: JoinFun a
    }

newtype OldFact a = OldFact a

newtype NewFact a = NewFact a

type JoinFun a = OldFact a -> NewFact a -> JoinedFact a

-- Note that it's actually important that the transfer function returns a
-- FactBase (or more generally a set of (label, fact) pairs) - if we have a
-- conditional jump, we should record that one of the edges will have different
-- fact (depending on the condition!).
type TransferFun b (n :: * -> * -> *) f = (b n C C -> FactBase f -> FactBase f)

data Direction = Fwd | Bwd

analyze
    :: forall f.
       Direction
    -> DataflowLattice2 f
    -> TransferFun Block CmmNode f
    -> CmmGraph
    -> FactBase f
    -> FactBase f
analyze dir lat transfer cmmGraph initFact =
    let entry = g_entry cmmGraph
        hooplGraph = g_graph cmmGraph
        blockMap =
            case hooplGraph of
                GMany NothingO bm NothingO -> bm
        entries = if mapNull initFact then [entry] else mapKeys initFact
    in fixpointAnal dir lat transfer entries blockMap initFact

fixpointAnal
    :: forall f n.
       NonLocal n
    => Direction
    -> DataflowLattice2 f
    -> TransferFun Block n f
    -> [Label]
    -> LabelMap (Block n C C)
    -> FactBase f
    -> FactBase f
fixpointAnal direction lattice do_block entries blockmap =
    loop start
  where
    blocks = sortBlocks direction entries blockmap
    num_blocks = length blocks
    block_arr = {-# SCC "block_arr" #-} listArray (0, num_blocks - 1) blocks
    start = {-# SCC "start" #-} [0 .. num_blocks - 1]
    dep_blocks = {-# SCC "dep_blocks" #-} mkDepBlocks direction blocks
    join = fact_join2 lattice
    loop
        :: IntHeap -- blocks still to analyse
        -> LabelMap f -- current factbase (increases monotonically)
        -> FactBase f
    loop []              !fbase1 = fbase1
    loop (index : todo1) !fbase1 =
        let block = block_arr ! index
            out_facts = do_block block fbase1
            -- For each of the outgoing edges, we join it with the current
            -- information in fbase1 and (if something changed) we update
            -- FactBase and add the block to the worklist.
            (todo2, fbase2) =
                mapFoldWithKey
                    (updateFact join dep_blocks) (todo1, fbase1) out_facts
        in loop todo2 fbase2

type IntHeap = [Int]

insertIntHeap :: Int -> [Int] -> [Int]
insertIntHeap x [] = [x]
insertIntHeap x (y : ys)
    | x < y = x : y : ys
    | x == y = x : ys
    | otherwise = y : insertIntHeap x ys

sortBlocks
    :: NonLocal n
    => Direction -> [Label] -> LabelMap (Block n C C) -> [Block n C C]
sortBlocks direction entries blockmap =
    case direction of
        Fwd -> fwd
        Bwd -> reverse fwd
  where
    fwd = forwardBlockList entries blockmap

forwardBlockList
    :: (NonLocal n, LabelsPtr entry)
    => entry -> Body n -> [Block n C C]
forwardBlockList entries blks = postorder_dfs_from blks entries

-- | Constructs a mapping from a label L to the indexes of blocks that need to
-- be re-analyzed if the facts for L change.
mkDepBlocks
    :: NonLocal n
    => Direction -> [Block n C C] -> LabelMap [Int]
mkDepBlocks Fwd blocks = go blocks 0 mapEmpty
  where
    go [] !_ m = m
    go (b:bs) !n m = go bs (n + 1) $! mapInsert (entryLabel b) [n] m
mkDepBlocks Bwd blocks = go blocks 0 mapEmpty
  where
    go [] !_ m = m
    go (b:bs) !n m = go bs (n + 1) $! go' (successors b) m
      where
        go' [] m = m
        go' (l:ls) m = go' ls (mapInsertWith (++) l [n] m)

updateFact
    :: JoinFun f
    -> LabelMap [Int]
    -> Label
    -> f -- out fact
    -> (IntHeap, FactBase f)
    -> (IntHeap, FactBase f)
updateFact fact_join dep_blocks lbl new_fact (todo, fbase) =
    case lookupFact lbl fbase of
        Nothing ->
            let !z = mapInsert lbl new_fact fbase
            in (changed, z)
        Just old_fact ->
            case fact_join (OldFact old_fact) (NewFact new_fact) of
                (NotChanged _) -> (todo, fbase)
                (Changed f) ->
                    let !z = mapInsert lbl f fbase
                    in (changed, z)
  where
    changed = foldr insertIntHeap todo $ mapFindWithDefault [] lbl dep_blocks

joinOutFacts
    :: (NonLocal a)
    => DataflowLattice2 f -> a O C -> FactBase f -> f
joinOutFacts lat n f = foldl' join (fact_bot2 lat) facts
  where
    join new old = getJoined $! fact_join2 lat (OldFact old) (NewFact new)
    facts =
        [ fromJust fact
        | s <- successors n
        , let fact = lookupFact s f
        , isJust fact
        ]

mkFactBase
    :: forall f.
       DataflowLattice2 f -> [(Label, f)] -> FactBase f
mkFactBase lattice = foldl' add mapEmpty
  where
    join = fact_join2 lattice

    add map (lbl, f) =
        let !newFact =
                case mapLookup lbl map of
                    Nothing -> f
                    Just f' -> getJoined $ join (OldFact f') (NewFact f)
        in mapInsert lbl newFact map

-- Represents the fact that for blocks/nodes that are closed on exit, we can
-- have different facts for different labels, whereas in the cases that are open
-- on exit, we have only a single fact.
type family   Fact x f :: *
type instance Fact C f = FactBase f
type instance Fact O f = f

foldBlockNodesB3Strict
    :: forall a b c.
       (CmmNode C O -> b -> c, CmmNode O O -> b -> b, CmmNode O C -> a -> b)
    -> (forall e x. Block CmmNode e x -> IndexedCO x a b -> IndexedCO e c b)
foldBlockNodesB3Strict (ftr, mtr, ltr) = go
  where
    -- NB. eta-expand go, GHC can't do this by itself.  See #5809.
    go :: forall e x. Block CmmNode e x -> IndexedCO x a b -> IndexedCO e c b
    go BNil f = f
    go (BlockCO n b) f = ftr n $! go b f
    go (BlockCC l b n) f = ftr l $! go b $! ltr n f
    go (BlockOC b n) f = go b $! ltr n f
    go (BMiddle n) f = mtr n f
    go (BCat b1 b2) f = go b1 $! go b2 f
    go (BSnoc h n) f = go h $! mtr n f
    go (BCons n t) f = mtr n $! go t f
{-# INLINE foldBlockNodesB3Strict #-}
