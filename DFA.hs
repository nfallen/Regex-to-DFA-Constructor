{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

module DFA where

import Alpha

import Automata

import Control.Monad

import Data.List.NonEmpty as NonEmpty

import Data.Maybe

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import GHC.Generics (Generic)
import Control.DeepSeq

import Data.Map (Map)
import qualified Data.Map as Map 

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool) 

-- / Map of transition from state and character input to new state
type Dtransition = Map (QState, Char) QState

-- / The DFA data type consists of a start state, a set of all states, 
--   a set of accept states, a mapping of all transitions between states,
--   and an alphabet 
data DFA = DFA {
                 dstart :: QState, 
                 dstates :: QStates, 
                 daccept :: QStates,
                 dtransition :: Dtransition, 
                 dalphabet :: Alpha
               } deriving (Show, Generic, NFData)

-- DFA that accepts all strings
sigmaStarDfa :: Alpha -> DFA
sigmaStarDfa ab = DFA {dstart = 0, 
                       dstates = Set.singleton 0,
                       daccept = Set.singleton 0,
                       dtransition = Map.fromList $
                                        [((0,s),0) | s <- NonEmpty.toList ab],
                       dalphabet = ab}

-- DFA that rejects all strings
emptySetDfa :: Alpha -> DFA
emptySetDfa ab = DFA {dstart = 0,
                      dstates = Set.singleton 0,
                      daccept = Set.empty,
                      dtransition = Map.empty,
                      dalphabet = ab}

-- DFA that accepts only the empty string
emptyStringDfa :: Alpha -> DFA
emptyStringDfa ab = DFA {dstart = 0, 
                         dstates = Set.fromList [0,1],
                         daccept = Set.singleton 0,
                         dtransition = Map.fromList $
                                        [((0,s),1) | s <- NonEmpty.toList ab] 
                                        ++ [((1,s),1) | s <- NonEmpty.toList ab],
                         dalphabet = ab}

-- DFAs for testing purposes
excessDFA = DFA {dstart = 0, 
                    dstates = Set.fromList [0,1,2,3,4,5], 
                    daccept = Set.fromList [2,3,4], 
                    dtransition = Map.fromList [((0,'0'),1),
                                                ((0,'1'),2),
                                                ((1,'0'),0),
                                                ((1,'1'),3),
                                                ((2,'0'),4),
                                                ((2,'1'),5),
                                                ((3,'0'),4),
                                                ((3,'1'),5),
                                                ((4,'0'),4),
                                                ((4,'1'),5),
                                                ((5,'0'),5),
                                                ((5,'1'),5)], 
                    dalphabet = NonEmpty.fromList "01"}


-- DFA with an unreachable state
unreachableDFA = DFA {dstart = 0,
                      dstates = Set.fromList [0,1],
                      daccept = Set.empty,
                      dtransition = Map.fromList[((1,'a'),0),((1,'b'),0)],
                      dalphabet = NonEmpty.fromList "ab"} 

-- a second DFA with an unreachable state 
unreachableDFA2 =  DFA {dstart = 0, 
                        dstates = Set.fromList [0,1,2,3,4,5,6],
                        daccept = Set.fromList [2,3,4],
                        dtransition = Map.fromList [((0,'0'),1),
                                                    ((0,'1'),2),
                                                    ((1,'0'),0),
                                                    ((1,'1'),3),
                                                    ((2,'0'),4),
                                                    ((2,'1'),5),
                                                    ((3,'0'),4),
                                                    ((3,'1'),5),
                                                    ((4,'0'),4),
                                                    ((4,'1'),5),
                                                    ((5,'0'),5),
                                                    ((5,'1'),5),
                                                    ((6,'1'),5),
                                                    ((6,'0'),6)],
                        dalphabet = NonEmpty.fromList "01"}      

-- / This function adds state q to the set of states in dfa 
withQState :: QState -> DFA -> DFA
withQState q dfa = dfa { dstates = Set.insert q (dstates dfa) }

-- / This function assigns the states in set qs as accept states in dfa 
withAccepts :: Set QState -> DFA -> DFA
withAccepts qs dfa = dfa { daccept = qs }

-- / This function adds transition (qs, q') to dfa
withTransition :: (QState, Char) -> QState -> DFA -> DFA
withTransition qc q' dfa = dfa { dtransition = Map.insert qc q' (dtransition dfa) }

-- defines decideString function for the DFA instance of the Automata class that determins whether string
-- is accepted by a DFA
instance Automata DFA where
  decideString dfa s
    | any (\c -> notElem c (dalphabet dfa)) s = Nothing
    | otherwise = decideStringFromQState dfa s (dstart dfa)
    where
      decideStringFromQState dfa (c:cs) q =
        case Map.lookup (q,c) (dtransition dfa) of 
          Just q'  -> decideStringFromQState dfa cs q'
          Nothing  -> decideStringFromQState dfa cs q
      decideStringFromQState dfa [] q = Just (Set.member q (daccept dfa))

testDecideStringDfa :: Test
testDecideStringDfa = "DFA decides strings correctly" ~:
  let ab = NonEmpty.fromList "ab" in
  TestList[
    decideString (emptySetDfa ab) "a" ~?= Just False,
    decideString (emptyStringDfa ab) "a" ~?= Just False,
    decideString (emptyStringDfa ab) "" ~?= Just True,
    decideString (sigmaStarDfa ab) "" ~?= Just True,
    decideString (sigmaStarDfa ab) "aaaaa" ~?= Just True,
    decideString (sigmaStarDfa ab) "bbbc" ~?= Nothing
  ]

-- We implement DFA equality as isomorphism.
instance Eq DFA where
  (==) d1 d2 = 
    dalphabet d1 == dalphabet d2
    && Set.size (dstates d1) == Set.size (dstates d2)
    && Map.size (dtransition d1) == Map.size (dtransition d2)
    && any isIsomorphicMapping (stateBijections (dstates d1) (dstates d2))
    where isIsomorphicMapping :: Map QState QState -> Bool
          isIsomorphicMapping m = startQStateSame m d1 d2 
                                  && transitionsSame m d1 d2 
                                  && acceptQStatesSame m d1 d2

-- / Determines if state that d1 start state is mapped to is the d2 start state
startQStateSame :: Map QState QState -> DFA -> DFA -> Bool
startQStateSame m d1 d2 = case (Map.lookup (dstart d1) m) of 
                            Just q2 -> (dstart d2) == q2
                            _ ->  False

testStartQStateSame :: Test
testStartQStateSame = "start state same" ~: 
  let ab = NonEmpty.fromList "01"
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
      m = Map.fromList [(0,0)]
      in TestList[
        startQStateSame m d1 d1 ~?= True,
        startQStateSame m d1 d2 ~?= True
      ]

-- / Determines whether DFAs d1 and d2 have the same transitions
transitionsSame :: Map QState QState -> DFA -> DFA -> Bool
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
  let ab = NonEmpty.fromList "01"
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
      m = Map.fromList [(0,0)]
      in TestList[
        transitionsSame m d1 d1 ~?= True,
        transitionsSame m d1 d2 ~?= False
      ]

-- / Determines whether accept state sets of d1 and d2 are equivalent 
acceptQStatesSame :: Map QState QState -> DFA -> DFA -> Bool
acceptQStatesSame m d1 d2 = all (\(q1,q2) -> equivAccept q1 q2) (Map.toList m)
  where equivAccept q1 q2 = Set.member q1 (daccept d1) == Set.member q2 (daccept d2)

testAcceptQStatesSame :: Test
testAcceptQStatesSame = "accept states same" ~: 
  let ab = NonEmpty.fromList "01"
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
      m = Map.fromList [(0,0)]
      in TestList[
        acceptQStatesSame m d1 d1 ~?= True,
        acceptQStatesSame m d2 d2 ~?= True,
        acceptQStatesSame m d1 d2 ~?= False
      ]

testEqDFA :: Test
testEqDFA = "test isomorphic DFA" ~: 
  let ab = NonEmpty.fromList "01"
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
      in TestList[
        d1 == d1 ~?= True,
        d2 == d2 ~?= True,
        d1 == d2 ~?= False,
        d2 == d1 ~?= False,
        excessDFA == excessDFA ~?= True,
        DFA {dstart = 0, 
             dstates = Set.fromList [0,1], 
             daccept = Set.fromList [1], 
             dtransition = Map.fromList [((0,'1'),1),
                                         ((1,'1'),1)], 
             dalphabet = return '1'}
        == DFA {dstart = 0, 
             dstates = Set.fromList [0,1], 
             daccept = Set.fromList [0,1], 
             dtransition = Map.fromList [((0,'1'),1),
                                     ((1,'1'),1)], 
             dalphabet = return '1'}
          ~?= False,
        DFA {dstart = 0, 
             dstates = Set.fromList [0,1,2,3],
             daccept = Set.fromList [2],
             dtransition = Map.fromList [((0,'a'),1),
                                         ((0,'b'),3),
                                         ((1,'a'),3),
                                         ((1,'b'),2),
                                         ((2,'a'),3),
                                         ((2,'b'),3),
                                         ((3,'a'),3),
                                         ((3,'b'),3)],
             dalphabet = NonEmpty.fromList "ab"}
        == DFA {dstart = 0, 
                dstates = Set.fromList [0,1,2,3],
                daccept = Set.fromList [3],
                dtransition = Map.fromList [((0,'a'),1),
                                        ((0,'b'),2),
                                        ((1,'a'),2),
                                        ((1,'b'),3),
                                        ((2,'a'),2),
                                        ((2,'b'),2),
                                        ((3,'a'),2),
                                        ((3,'b'),2)],
                dalphabet = NonEmpty.fromList "ab"}
          ~?= True
      ]

test :: IO ()
test = do
    runTestTT $ TestList [testDecideStringDfa,
                          testStartQStateSame,
                          testTransitionsSame, 
                          testAcceptQStatesSame, 
                          testEqDFA]
    return ()