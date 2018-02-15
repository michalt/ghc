module Main where

import Hoopl.Block
import Hoopl.Collections
import Hoopl.Graph
import Hoopl.Label

import Data.Maybe

data TestBlock e x = TB { label_ :: Label, successors_ :: [Label] }
    deriving (Eq, Show)

instance NonLocal TestBlock where
  entryLabel = label_
  successors = successors_

test_diamond :: LabelMap (TestBlock C C)
test_diamond = mapFromList $ map (\b -> (label_ b, b)) blocks
  where
    blocks =
        [ TB (mkHooplLabel 0) [(mkHooplLabel 1)]
        , TB (mkHooplLabel 1) [(mkHooplLabel 2), (mkHooplLabel 3)]
        , TB (mkHooplLabel 2) [(mkHooplLabel 4)]
        , TB (mkHooplLabel 3) [(mkHooplLabel 4)]
        , TB (mkHooplLabel 4) []
        ]

main :: IO ()
main = do
    let postorder_diamond =
            postorder_dfs_from
                test_diamond
                (fromJust $ mapLookup (mkHooplLabel 0) test_diamond)
    putStrLn (show $ map label_ postorder_diamond)
