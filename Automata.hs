---------------------------------------------------------------------------      
-- Regina Burd, Nova Fallen
-- CIS 552 Project

module Automata where

import Control.Monad

import Data.Maybe

import Data.List as List

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

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

data NFA = NFA {
                 nstart :: State,
                 nstates :: States,
                 ntransition :: Ntransition,
                 nalphabet :: Set Char
               } deriving (Show)

data DFA = DFA {
                 dstart :: State, 
                 dstates :: States, 
                 dtransition :: Dtransition, 
                 dalphabet :: Set Char
               } deriving (Show)

-- DFA that accepts all strings
sigmaStarDFA :: Set Char -> DFA
sigmaStarDFA ab = DFA {dstart = 0, dstates = Map.singleton 0 True, dtransition = Map.empty, dalphabet = ab}

-- DFA that rejects all strings
emptySetDFA :: Set Char -> DFA
emptySetDFA ab = DFA {dstart = 0, dstates = Map.singleton 0 False, dtransition = Map.empty, dalphabet = ab}

-- DFA that accepts only the empty string
emptyStringDFA :: Set Char -> DFA
emptyStringDFA ab = DFA {dstart = 0, 
                         dstates = Map.fromList [(0,True),(1,False)],
                         dtransition = Map.fromList [((0,s),1) | s <- Set.toList ab],
                         dalphabet = ab}

class Automata a where
  decideString :: a -> String -> Maybe Bool

instance Automata DFA where
  decideString dfa s = decideStringFromState dfa s (dstart dfa) where
    decideStringFromState dfa (c:cs) q 
      | Set.member c (dalphabet dfa) = case Map.lookup (q,c) (dtransition dfa) of 
                                         Just q'  -> decideStringFromState dfa cs q'
                                         Nothing  -> decideStringFromState dfa cs q
      | otherwise                    = Nothing
    decideStringFromState dfa [] q   = Map.lookup q (dstates dfa)

-- TODO: more tests
testDecideStringDFA :: Test
testDecideStringDFA = "DFA decides strings correctly" ~:
  let ab = Set.fromList "a" in
  TestList[
    decideString (emptySetDFA ab) "a" ~?= Just False,
    decideString (emptyStringDFA ab) "a" ~?= Just False,
    decideString (emptyStringDFA ab) "" ~?= Just True,
    decideString (sigmaStarDFA ab) "" ~?= Just True,
    decideString (sigmaStarDFA ab) "aaaaa" ~?= Just True,
    decideString (sigmaStarDFA ab) "bbb" ~?= Nothing
  ]

-- TODO: write tests for this
instance Automata NFA where
  decideString nfa s = decideStringFromState nfa s (Set.singleton (nstart nfa)) where
    decideStringFromState :: NFA -> String -> Set State -> Maybe Bool
    decideStringFromState nfa (c:cs) qs 
      | Set.member c (nalphabet nfa) = 
          -- add all states reachable from the current set of states by reading the next symbol
          let qs' = do
                    q <- qs
                    case Map.lookup (q, Just c) (ntransition nfa) of 
                      Just nqs -> nqs
                      Nothing  -> Set.empty
          -- additionally add the states reachable by epsilon transitions from this new set of states
          in let eqs' = do
                        q <- qs'
                        case Map.lookup (q, Nothing) (ntransition nfa) of
                          Just nqs -> nqs
                          Nothing  -> Set.empty
          in decideStringFromState nfa cs (Set.union qs' eqs')
      | otherwise                    = Nothing
    decideStringFromState nfa [] qs  = any id <$> accepts where 
                                       accepts :: Maybe [Bool]
                                       accepts = mapM (\q -> Map.lookup q $ nstates nfa) (Set.toList qs)

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
      d1 = sigmaStarDFA ab
      d2 = emptySetDFA ab
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
      d1 = sigmaStarDFA ab
      d2 = emptySetDFA ab
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
      d1 = sigmaStarDFA ab
      d2 = emptySetDFA ab
      m = Map.fromList [(0,0)]
      in TestList[
        acceptStatesSame m d1 d1 ~?= True,
        acceptStatesSame m d2 d2 ~?= True,
        acceptStatesSame m d1 d2 ~?= False
      ]
-- We implement DFA equality as isomorphism.
instance Eq DFA where
  (==) d1 d2 = 
    dalphabet d1 == dalphabet d2
    && Map.size (dstates d1) == Map.size (dstates d2)
    && Map.size (dtransition d1) == Map.size (dtransition d2)
    && any isIsomorphicMapping (stateBijections (dstates d1) (dstates d2))
    where isIsomorphicMapping :: Map State State -> Bool
          isIsomorphicMapping m = startStateSame m d1 d2 
                                  && transitionsSame m d1 d2 
                                  && acceptStatesSame m d1 d2

-- TODO: more tests!
testEqDFA :: Test
testEqDFA = "test isomorphic DFA" ~: 
  let ab = Set.fromList ['0', '1']
      d1 = sigmaStarDFA ab
      d2 = emptySetDFA ab
      in TestList[
        d1 == d1 ~?= True,
        d2 == d2 ~?= True,
        d1 == d2 ~?= False,
        d2 == d1 ~?= False
      ]

main :: IO ()
main = do
    runTestTT $ TestList [testDecideStringDFA,
                          testBijections, 
                          testStartStateSame,
                          testTransitionsSame, 
                          testAcceptStatesSame, 
                          testEqDFA]
    return ()

