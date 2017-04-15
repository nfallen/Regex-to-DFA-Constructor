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

type States = Set State

data NFA = NFA {
                 nstart :: State,
                 nstates :: States,
                 naccept :: States,
                 ntransition :: Ntransition,
                 nalphabet :: Set Char
               } deriving (Show)

data DFA = DFA {
                 dstart :: State, 
                 dstates :: States, 
                 daccept :: States,
                 dtransition :: Dtransition, 
                 dalphabet :: Set Char
               } deriving (Show)

-- DFA that accepts all strings
sigmaStarDfa :: Set Char -> DFA
sigmaStarDfa ab = DFA {dstart = 0, 
                       dstates = Set.singleton 0,
                       daccept = Set.singleton 0,
                       dtransition = Map.empty,
                       dalphabet = ab}

-- DFA that rejects all strings
emptySetDfa :: Set Char -> DFA
emptySetDfa ab = DFA {dstart = 0,
                      dstates = Set.singleton 0,
                      daccept = Set.empty,
                      dtransition = Map.empty,
                      dalphabet = ab}

-- DFA that accepts only the empty string
emptyStringDfa :: Set Char -> DFA
emptyStringDfa ab = DFA {dstart = 0, 
                         dstates = Set.fromList [0,1],
                         daccept = Set.singleton 0,
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
    decideStringFromState dfa [] q   = Just (Set.member q (daccept dfa))

-- TODO: more tests
testDecideStringDfa :: Test
testDecideStringDfa = "DFA decides strings correctly" ~:
  let ab = Set.fromList "a" in
  TestList[
    decideString (emptySetDfa ab) "a" ~?= Just False,
    decideString (emptyStringDfa ab) "a" ~?= Just False,
    decideString (emptyStringDfa ab) "" ~?= Just True,
    decideString (sigmaStarDfa ab) "" ~?= Just True,
    decideString (sigmaStarDfa ab) "aaaaa" ~?= Just True,
    decideString (sigmaStarDfa ab) "bbb" ~?= Nothing
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
    decideStringFromState nfa [] qs  = Just $ any accepts (Set.toList qs) where
                                       accepts q = Set.member q $ naccept nfa

stateBijections :: States -> States -> [Map State State]
stateBijections s1 s2 = let xs = Set.toList s1 
                            perms = List.permutations (Set.toList s2) in 
                            Map.fromList <$> (fmap (\perm -> zip xs perm) perms)

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

startStateSame :: Map State State -> DFA -> DFA -> Bool
startStateSame m d1 d2 = case (Map.lookup (dstart d1) m) of 
                            Just q2 -> (dstart d1) == q2
                            _ ->  False

testStartStateSame :: Test
testStartStateSame = "start state same" ~: 
  let ab = Set.fromList ['0', '1']
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
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
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
      m = Map.fromList [(0,0)]
      in TestList[
        transitionsSame m d1 d1 ~?= True,
        transitionsSame m d1 d2 ~?= True
      ]

acceptStatesSame :: Map State State -> DFA -> DFA -> Bool
acceptStatesSame m d1 d2 = all (\(q1,q2) -> equivAccept q1 q2) (Map.toList m)
  where equivAccept q1 q2 = Set.member q1 (daccept d1) == Set.member q2 (daccept d2)

testAcceptStatesSame :: Test
testAcceptStatesSame = "accept states same" ~: 
  let ab = Set.fromList ['0', '1']
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
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
    && Set.size (dstates d1) == Set.size (dstates d2)
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
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
      in TestList[
        d1 == d1 ~?= True,
        d2 == d2 ~?= True,
        d1 == d2 ~?= False,
        d2 == d1 ~?= False
      ]

-- We implement NFA equality as exact equality
instance Eq NFA where
  (==) n1 n2 = 
    nalphabet n1 == nalphabet n2
    && nstates n1 == nstates n2
    && naccept n1 == naccept n2
    && ntransition n1 == ntransition n2
    && nstart n1 == nstart n2

main :: IO ()
main = do
    runTestTT $ TestList [testDecideStringDfa,
                          testBijections, 
                          testStartStateSame,
                          testTransitionsSame, 
                          testAcceptStatesSame, 
                          testEqDFA]
    return ()

