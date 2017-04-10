---------------------------------------------------------------------------      
-- Regina Burd, Nova Fallen
-- CIS 552 Project

module Automata where

import Data.List as List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map 

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool) 

-- TODO: limit exports

type State = Int

type Dtransition = Map (State, Char) State

-- The NFA transition function has epsilon transitions
-- and one state/symbol pair can map to multiple next states.
type Ntransition = Map (State, Maybe Char) (Set State)

type States = Map State Bool

data DFA = DFA {dstart :: State, dstates :: States, dtransition :: Dtransition, dalphabet :: Set Char}

data NFA = NFA {nstart :: State, nstates :: States, ntransition :: Ntransition, nalphabet :: Set Char}

-- DFA that accepts all strings
acceptDFA :: Set Char -> DFA
acceptDFA ab = DFA {dstart = 0, dstates = Map.singleton 0 True, dtransition = Map.empty, dalphabet = ab}

-- DFA that rejects all strings
rejectDFA :: Set Char -> DFA
rejectDFA ab = DFA {dstart = 0, dstates = Map.singleton 0 False, dtransition = Map.empty, dalphabet = ab}

stateBijections :: States -> States -> [Map State State]
stateBijections s1 s2 = let xs = Map.keys s1 
                            perms = List.permutations (Map.keys s2) in 
                            Map.fromList <$> (fmap (\perm -> zip xs perm) perms)

testBijections :: Test
testBijections = "bijections" ~: 
  let states1 = Map.fromList [(1, True),(2, False),(3, True)] in
  let states2 = Map.fromList [(4, True),(5, False),(6, True)] in
    TestList[
        stateBijections (Map.fromList [(0, True)]) (Map.fromList [(0, True)]) 
          ~?= [Map.fromList [(0,0)]],
        stateBijections states1 states2 ~?= [Map.fromList [(1,4),(2,5),(3,6)],
                                             Map.fromList [(1,5),(2,4),(3,6)],
                                             Map.fromList [(1,6),(2,5),(3,4)],
                                             Map.fromList [(1,5),(2,6),(3,4)],
                                             Map.fromList [(1,6),(2,4),(3,5)],
                                             Map.fromList [(1,4),(2,6),(3,5)]]
    ] 

startStateSame :: Map State State -> DFA -> DFA -> Bool
startStateSame m d1 d2 = case (Map.lookup (dstart d1) m) of 
                            Just q2 -> (dstart d1) == q2
                            _ ->  False

testStartStateSame :: Test
testStartStateSame = "start state same" ~: 
  let ab = Set.fromList ['0', '1']
      d1 = acceptDFA ab
      d2 = rejectDFA ab
      m = Map.fromList [(0,0)]
      in TestList[
        startStateSame m d1 d1 ~?= True,
        startStateSame m d1 d2 ~?= True
      ]

transitionsSame :: Map State State -> DFA -> DFA -> Bool
transitionsSame m d1 d2 = all (\q -> all (\s -> equivTransition q s m) (dalphabet d1)) (Map.keys m)
  where equivTransition q1 s m = case Map.lookup q1 m of 
          Just q2 ->
            case (Map.lookup (q1,s) (dtransition d1), Map.lookup (q2,s) (dtransition d2)) of
              (Nothing, Nothing) -> True
              (Just qn1, Just qn2) -> 
                case Map.lookup qn1 m of
                  Just qn1' -> qn1' == qn2
                  Nothing -> False
              _ -> False
          _ -> False

testTransitionsSame :: Test
testTransitionsSame = "transitions same" ~: 
  let ab = Set.fromList ['0', '1']
      d1 = acceptDFA ab
      d2 = rejectDFA ab
      m = Map.fromList [(0,0)]
      in TestList[
        transitionsSame m d1 d1 ~?= True,
        transitionsSame m d1 d2 ~?= True
      ]

acceptStatesSame :: Map State State -> DFA -> DFA -> Bool
acceptStatesSame m d1 d2 = all (\(q1,q2) -> equivAccept q1 q2) (Map.toList m)
  where equivAccept q1 q2 = case (Map.lookup q1 (dstates d1), Map.lookup q2 (dstates d2)) of
                              (Just b1, Just b2) -> b1 == b2
                              _ -> False

testAcceptStatesSame :: Test
testAcceptStatesSame = "accept states same" ~: 
  let ab = Set.fromList ['0', '1']
      d1 = acceptDFA ab
      d2 = rejectDFA ab
      m = Map.fromList [(0,0)]
      in TestList[
        acceptStatesSame m d1 d1 ~?= True,
        acceptStatesSame m d2 d2 ~?= True,
        acceptStatesSame m d1 d2 ~?= False
      ]

isomorphicDFA :: DFA -> DFA -> Bool 
isomorphicDFA d1 d2 = 
  (dalphabet d1) == (dalphabet d2)
  && Map.size (dstates d1) == Map.size (dstates d2)
  && Map.size (dtransition d1) == Map.size (dtransition d2)
  && any isIsomorphicMapping (stateBijections (dstates d1) (dstates d2))
  where isIsomorphicMapping :: Map State State -> Bool
        isIsomorphicMapping m = startStateSame m d1 d2 
                                && transitionsSame m d1 d2 
                                && acceptStatesSame m d1 d2

-- TODO: more tests!
testIsomorphicDFA :: Test
testIsomorphicDFA = "isomorphic DFA" ~: 
  let ab = Set.fromList ['0', '1']
      d1 = acceptDFA ab
      d2 = rejectDFA ab
      in TestList[
        isomorphicDFA d1 d1 ~?= True,
        isomorphicDFA d2 d2 ~?= True,
        isomorphicDFA d1 d2 ~?= False,
        isomorphicDFA d2 d1 ~?= False
      ]

main :: IO ()
main = do
    runTestTT $ TestList [testBijections, 
                          testStartStateSame,
                          testTransitionsSame, 
                          testAcceptStatesSame, 
                          testIsomorphicDFA]
    return ()

