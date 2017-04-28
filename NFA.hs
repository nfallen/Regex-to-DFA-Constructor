module NFA where

import Automata

import Control.Monad

import Control.Monad.State

import Data.Maybe

import Data.List as List

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Data.Map (Map)
import qualified Data.Map as Map 

import Debug.Trace

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool) 

-- The NFA transition function has epsilon transitions
-- and one state/symbol pair can map to multiple next states.
type Ntransition = Map (QState, Maybe Char) (Set QState)

data NFA = NFA { nstart :: QState,
                 nstates :: QStates,
                 naccept :: QStates,
                 ntransition :: Ntransition,
                 nalphabet :: Set Char
               } deriving (Show)

emptySetNfa ab = NFA {nstart = 0,
                   nstates = Set.singleton 0,
                   naccept = Set.empty,
                   ntransition = Map.empty,
                   nalphabet = ab}

emptyStringNfa ab = NFA {nstart = 0,
                      nstates = Set.fromList [0,1],
                      naccept = Set.singleton 0,
                      ntransition = Map.fromList 
                        [((0,Just s),Set.singleton 1) | s <- Set.toList ab],
                      nalphabet = ab}

-- takes in a set of states, returns the ones that are unseen 
-- and updates the state to have seen all of them
unseenQStates :: Set QState -> State (Set QState) (Set QState)
unseenQStates qs = do
  seen <- get
  let unseen = Set.difference qs seen
  put (Set.union seen unseen)
  return unseen

oneStepReachable :: NFA -> Set QState -> Maybe Char -> Set QState
oneStepReachable nfa qs mc = 
  do
  q <- qs
  case Map.lookup (q, mc) (ntransition nfa) of
    Just nqs -> nqs
    Nothing  -> Set.empty

epsilonReachable :: NFA -> Set QState -> Set QState
epsilonReachable nfa qs = 
  let (_, rqs) = runState (eReachable nfa qs) Set.empty in rqs
  where eReachable :: NFA -> Set QState -> State (Set QState) ()
        eReachable nfa qs
          | qs == Set.empty = return ()
          | otherwise = do
              uqs <- unseenQStates qs
              let eqs = oneStepReachable nfa uqs Nothing
              eReachable nfa eqs

testEpsilonReachable :: Test
testEpsilonReachable = TestList [
  epsilonReachable (singleCharNfa 'a') (Set.singleton 0) ~?= (Set.singleton 0),
  epsilonReachable (unionNfa (singleCharNfa 'a') (singleCharNfa 'b')) 
    (Set.fromList [0,4])
    ~?= Set.fromList [0,1,3,4,5],
  epsilonReachable (concatNfa 
                   (unionNfa (singleCharNfa 'a') (singleCharNfa 'b')) 
                   (singleCharNfa 'b'))
    (Set.singleton 0)
    ~?= Set.fromList [0,1,3],
  epsilonReachable (concatNfa 
                   (unionNfa (singleCharNfa 'a') (singleCharNfa 'b')) 
                   (singleCharNfa 'b'))
    (Set.fromList [0,5])
    ~?= Set.fromList [0,1,3,5,6],
  epsilonReachable (kleeneNfa (singleCharNfa 'a')) (Set.fromList [0]) 
    ~?= Set.fromList [0,1,3]]

symbolReachable :: NFA -> Set QState -> Char -> Set QState
symbolReachable nfa qs c = oneStepReachable nfa qs (Just c)

testSymbolReachable :: Test
testSymbolReachable = TestList [
  symbolReachable (singleCharNfa 'a') (Set.singleton 0) 'a' ~?= (Set.singleton 1),
  symbolReachable (unionNfa (singleCharNfa 'a') (singleCharNfa 'b')) 
    (Set.fromList [1,3]) 'a'
    ~?= Set.fromList [2]]

acceptsSomeState :: NFA -> Set QState -> Bool
acceptsSomeState nfa qs = any accept (Set.toList qs) where
                          accept q = Set.member q $ naccept nfa
  
instance Automata NFA where
  decideString nfa s = decideStringFromQState nfa s (Set.singleton (nstart nfa)) where
    decideStringFromQState :: NFA -> String -> Set QState -> Maybe Bool
    decideStringFromQState nfa [] qs  = 
      Just $ acceptsSomeState nfa (epsilonReachable nfa qs)
    decideStringFromQState nfa (c:cs) qs 
      | Set.member c (nalphabet nfa) = 
          -- get all states reachable by epsilon transitions from current set of states
          let eqs' = epsilonReachable nfa qs
          -- now compute states reachable from the new set of states by reading the next symbol
          in let qs' = symbolReachable nfa eqs' c
          in decideStringFromQState nfa cs qs'
      | otherwise                    = Nothing

testNfa1 = kleeneNfa (singleCharNfa 'a')
testNfa2 = unionNfa (singleCharNfa 'a') (singleCharNfa 'b')
testNfa3 = concatNfa (singleCharNfa 'a') (singleCharNfa 'b')
testNfa4 = (kleeneNfa (concatNfa 
                        (singleCharNfa 'a')
                        (singleCharNfa 'b')))

testDecideStringNfa :: Test
testDecideStringNfa = TestList [
  decideString (singleCharNfa 'a') "a" ~?= Just True,
  decideString (singleCharNfa 'a') "aa" ~?= Just False,
  decideString (singleCharNfa 'a') "b" ~?= Nothing,
  decideString testNfa1 "" ~?= Just True,
  decideString testNfa1 "a" ~?= Just True,
  decideString testNfa1 "aaa" ~?= Just True,
  decideString testNfa2 "a" ~?= Just True,
  decideString testNfa2 "b" ~?= Just True,
  decideString testNfa2 "ab" ~?= Just False,
  decideString testNfa3 "ab" ~?= Just True,
  decideString testNfa3 "b" ~?= Just False,
  decideString testNfa3 "abb" ~?= Just False,
  decideString testNfa3 "aab" ~?= Just False,
  decideString testNfa4 "" ~?= Just True,
  decideString testNfa4 "a" ~?= Just False,
  decideString testNfa4 "ababab" ~?= Just True,
  decideString testNfa4 "b" ~?= Just False]

-- We implement NFA equality as exact equality
instance Eq NFA where
  (==) n1 n2 = 
    nalphabet n1 == nalphabet n2
    && nstates n1 == nstates n2
    && naccept n1 == naccept n2
    && ntransition n1 == ntransition n2
    && nstart n1 == nstart n2

singleCharNfa :: Char -> NFA 
singleCharNfa char = 
  let ab = Set.singleton char
      singleQStates = Set.fromList [0,1]
      singleTransition = Map.fromList [((0, Just char), Set.singleton 1)]
      singleAccept = Set.singleton 1
  in NFA {nstart = 0, 
          nstates = singleQStates, 
          naccept = singleAccept,
          ntransition = singleTransition, 
          nalphabet = ab}

testSingleCharNfa :: Test
testSingleCharNfa = TestList [
  singleCharNfa 'a' ~?= NFA {
    nstart = 0,
    nstates = Set.fromList [0,1],
    naccept = Set.singleton 1,
    ntransition = Map.fromList [((0,Just 'a'), Set.singleton 1)],
    nalphabet = Set.singleton 'a'
  }]

unionNfa :: NFA -> NFA -> NFA
unionNfa n1 n2 
    | n1 == n2 = n1 
    | n1 == (emptySetNfa (Set.empty :: Set Char)) = n2 
    | n2 == (emptySetNfa (Set.empty :: Set Char)) = n1 
    | otherwise = let ab = Set.union (nalphabet n1) (nalphabet n2)
                      lastQStateN1 = Set.size (nstates n1)
                      firstQStateN2 = lastQStateN1 + 1
                      lastQStateN2 = lastQStateN1 + Set.size (nstates n2)
                      lastQStateUnion = lastQStateN2 + 1
                      s0 = Set.union 
                            (fmap (+1) (nstates n1)) 
                            (fmap (+ firstQStateN2) (nstates n2))
                      s1 = Set.insert lastQStateUnion s0
                      states = Set.insert 0 s1
                      incN1T = fmap (fmap (+1)) $ 
                                Map.mapKeys (\(a,b) -> (a + 1,b)) (ntransition n1)
                      incN2T = fmap (fmap (+ firstQStateN2)) $
                                Map.mapKeys (\(a,b) -> (a + firstQStateN2,b)) (ntransition n2)
                      u0 = Map.union incN1T incN2T
                      u1 = Map.insert (0, Nothing) (Set.fromList [1, firstQStateN2]) u0
                      u2 = Map.insert (lastQStateN1, Nothing) (Set.singleton lastQStateUnion) u1
                      transitions = Map.insert 
                                      (lastQStateN2, Nothing) 
                                      (Set.singleton lastQStateUnion) 
                                      u2
                      accepts = Set.singleton lastQStateUnion
                      in NFA {nstart = 0, 
                              nstates = states,
                              naccept = accepts,
                              ntransition = transitions, 
                              nalphabet = ab}

testUnionNfa :: Test
testUnionNfa = TestList [
  unionNfa (singleCharNfa 'a') (singleCharNfa 'b') ~?= 
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

concatNfa :: NFA -> NFA -> NFA
concatNfa n1 n2 =
  let ab = Set.union (nalphabet n1) (nalphabet n2)
      firstQStateN2 = (Set.size (nstates n1))
      lastQStateN1 = firstQStateN2 - 1
      states = Set.union 
                (nstates n1)
                (fmap (+ firstQStateN2) (nstates n2))
      incN2T = fmap (fmap (+ firstQStateN2)) $
                 Map.mapKeys (\(a,b) -> (a + firstQStateN2,b)) (ntransition n2)
      t0 = Map.union (ntransition n1) incN2T
      transitions = Map.insert (lastQStateN1, Nothing) (Set.singleton firstQStateN2) t0
      accepts = Set.singleton $ (Set.size states) - 1
  in NFA {nstart = 0, 
          nstates = states,
          naccept = accepts,
          ntransition = transitions, 
          nalphabet = ab}

testConcatNfa :: Test
testConcatNfa = TestList [
  concatNfa (singleCharNfa 'a') (singleCharNfa 'b') ~?= 
    NFA {
      nstart = 0,
      nstates = Set.fromList [0,1,2,3],
      naccept = Set.singleton 3,
      ntransition = Map.fromList [((0, Just 'a'), (Set.singleton 1)),
                                  ((2, Just 'b'), (Set.singleton 3)),
                                  ((1,Nothing), (Set.singleton 2))],
      nalphabet = Set.fromList "ab"
    },
  (concatNfa 
    (unionNfa (singleCharNfa 'a') (singleCharNfa 'b')) 
    (singleCharNfa 'b')) ~?=
    NFA {
      nstart = 0,
      nstates = Set.fromList [0,1,2,3,4,5,6,7],
      naccept = Set.singleton 7,
      ntransition = Map.fromList [((0,Nothing), Set.fromList [1,3]),
                                  ((1, Just 'a'), (Set.singleton 2)),
                                  ((3, Just 'b'), (Set.singleton 4)),
                                  ((6, Just 'b'), (Set.singleton 7)),
                                  ((2,Nothing), (Set.singleton 5)),
                                  ((4,Nothing), (Set.singleton 5)),
                                  ((5,Nothing), (Set.singleton 6))],
      nalphabet = Set.fromList "ab"
    }]

kleeneNfa :: NFA -> NFA
kleeneNfa n = 
  let lastQStateN = Set.size (nstates n)
      lastQStateKleene = lastQStateN + 1
      states = Set.insert 0 $ Set.insert lastQStateKleene $ fmap (+1) (nstates n)
      incNT = fmap (fmap (+1)) $ 
                 Map.mapKeys (\(a,b) -> (a + 1,b)) (ntransition n)
      t0 = Map.insert (0, Nothing) (Set.fromList [1, lastQStateKleene]) incNT
      transitions = Map.insert (lastQStateN, Nothing) 
                               (Set.fromList [1, lastQStateKleene])
                               t0
      accepts = Set.singleton lastQStateKleene
    in NFA {nstart = 0,
            nstates = states,
            naccept = accepts,
            ntransition = transitions,
            nalphabet = nalphabet n}

testKleeneNfa :: Test
testKleeneNfa = TestList [
  kleeneNfa (singleCharNfa 'a') ~?= 
    NFA {
      nstart = 0,
      nstates = Set.fromList [0,1,2,3],
      naccept = Set.singleton 3,
      ntransition = Map.fromList [((0,Nothing), Set.fromList [1,3]),
                                  ((1,Just 'a'), Set.fromList [2]),
                                  ((2,Nothing), Set.fromList [1,3])],
      nalphabet = Set.fromList "a"},
  kleeneNfa (concatNfa (singleCharNfa 'a') (singleCharNfa 'b')) ~?= 
     NFA {nstart = 0, 
          nstates = Set.fromList [0,1,2,3,4,5],
          naccept = Set.fromList [5],
          ntransition = Map.fromList [((0,Nothing),Set.fromList [1,5]),
                                      ((1,Just 'a'),Set.fromList [2]),
                                      ((2,Nothing),Set.fromList [3]),
                                      ((3,Just 'b'),Set.fromList [4]),
                                      ((4,Nothing),Set.fromList [1,5])],
          nalphabet = Set.fromList "ab"}] 

main :: IO ()
main = do
    runTestTT $ TestList [testSingleCharNfa,
                          testUnionNfa,
                          testConcatNfa,
                          testKleeneNfa,
                          testEpsilonReachable,
                          testSymbolReachable,
                          testDecideStringNfa]
    return ()