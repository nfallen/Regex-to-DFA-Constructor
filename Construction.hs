module Construction where

import Regex
import Automata

import Data.Map (Map)
import qualified Data.Map as Map 

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  

--TODO: how to define alphabet here 

thompsonConstruction :: RegExp -> DFA
thompsonConstruction regexp = let nfa = thompsonNfaConstruction regexp
                              in dfaConstruction nfa

thompsonNfaConstruction :: RegExp -> NFA
thompsonNfaConstruction = undefined

singleCharThompson :: Char -> NFA --TODO: Change type signature to DFA when DFA converter is implemented 
singleCharThompson char = 
  let ab = Set.singleton char
      singleStates = Set.fromList [0,1]
      singleTransition = Map.fromList [((0, Just char), Set.singleton 1)]
      singleAccept = Set.singleton 1
  in NFA {nstart = 0, 
          nstates = singleStates, 
          naccept = singleAccept,
          ntransition = singleTransition, 
          nalphabet = ab}

testSingleCharThompson :: Test
testSingleCharThompson = TestList [
  singleCharThompson 'a' ~?= NFA {
    nstart = 0,
    nstates = Set.fromList [0,1],
    naccept = Set.singleton 1,
    ntransition = Map.fromList [((0,Just 'a'), Set.singleton 1)],
    nalphabet = Set.singleton 'a'
  }]

unionThompson :: NFA -> NFA -> NFA
unionThompson n1 n2 = 
  let ab = Set.union (nalphabet n1) (nalphabet n2)
      lastStateN1 = Set.size (nstates n1)
      firstStateN2 = lastStateN1 + 1
      lastStateN2 = lastStateN1 + Set.size (nstates n2)
      lastStateUnion = lastStateN2 + 1
      st0 = Set.union 
             (fmap (+1) (nstates n1)) 
             (fmap (+ firstStateN2) (nstates n2))
      st1 = Set.insert lastStateUnion st0
      states = Set.insert 0 st1
      incN1T = fmap (fmap (+1)) $ 
                 Map.mapKeys (\(a,b) -> (a + 1,b)) (ntransition n1)
      incN2T = fmap (fmap (+ firstStateN2)) $
                 Map.mapKeys (\(a,b) -> (a + firstStateN2,b)) (ntransition n2)
      ut0 = Map.union incN1T incN2T
      ut1 = Map.insert (0, Nothing) (Set.fromList [1, firstStateN2]) ut0
      ut2 = Map.insert (lastStateN1, Nothing) (Set.singleton lastStateUnion) ut1
      transitions = Map.insert (lastStateN2, Nothing) (Set.singleton lastStateUnion) ut2
      accepts = Set.singleton lastStateUnion
  in NFA {nstart = 0, 
          nstates = states,
          naccept = accepts,
          ntransition = transitions, 
          nalphabet = ab}

testUnionThompson :: Test
testUnionThompson = TestList [
  unionThompson (singleCharThompson 'a') (singleCharThompson 'b') ~?= 
    NFA {
      nstart = 0,
      nstates = Set.fromList [0,1,2,3,4,5],
      naccept = Set.singleton 5,
      ntransition = Map.fromList [((0,Nothing), Set.fromList [1,3]),
                                  ((1, Just 'a'), (Set.singleton 2)),
                                  ((3, Just 'b'), (Set.singleton 4)),
                                  ((2,Nothing), (Set.singleton 5)),
                                  ((4,Nothing), (Set.singleton 5))],
      nalphabet = Set.fromList "ab"
    }]

concatThompson :: Set Char -> RegExp -> NFA
concatThompson ab (Seq r1 r2) = undefined 

kleeneThompson :: Set Char -> RegExp -> NFA
kleeneThompson ab (Star r) = undefined 

brzozowskiConstruction :: RegExp -> DFA
brzozowskiConstruction = undefined

dfaConstruction :: NFA -> DFA 
dfaConstruction = undefined 

main :: IO ()
main = do
    runTestTT $ TestList [ testSingleCharThompson, testUnionThompson]
    return ()