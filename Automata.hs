---------------------------------------------------------------------------      
-- Regina Burd, Nova Fallen
-- CIS 552 Project

module Automata where

import Data.List as List

import Data.List.NonEmpty as NonEmpty

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Data.Map (Map)
import qualified Data.Map as Map 

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool) 

import Alpha

type QState = Int

type QStates = Set QState

class Automata a where
  decideString :: a -> String -> Maybe Bool


stateBijections :: QStates -> QStates -> [Map QState QState]
stateBijections s1 s2 = let xs = Set.toList s1 
                            perms = List.permutations (Set.toList s2) in 
                            Map.fromList <$> (fmap (\perm -> List.zip xs perm) perms)

testBijections :: Test
testBijections = "bijections" ~: 
  let states1 = Set.fromList [1,2,3] in
  let states2 = Set.fromList [4,5,6] in
    TestList[
        stateBijections (Set.singleton 0) (Set.singleton 0)
          ~?= [Map.fromList [(0,0)]],
        stateBijections states1 states2 ~?= [Map.fromList [(1,4),(2,5),(3,6)],
                                             Map.fromList [(1,5),(2,4),(3,6)],
                                             Map.fromList [(1,6),(2,5),(3,4)],
                                             Map.fromList [(1,5),(2,6),(3,4)],
                                             Map.fromList [(1,6),(2,4),(3,5)],
                                             Map.fromList [(1,4),(2,6),(3,5)]]
    ] 

test :: IO ()
test = do
    runTestTT $ TestList [testBijections]
    return ()

