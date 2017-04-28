module DFA where

import Alpha

import Automata

import Control.Monad

import Data.List.NonEmpty as NonEmpty

import Data.Maybe

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Data.Map (Map)
import qualified Data.Map as Map 

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool) 

type Dtransition = Map (QState, Char) QState

data DFA = DFA {
                 dstart :: QState, 
                 dstates :: QStates, 
                 daccept :: QStates,
                 dtransition :: Dtransition, 
                 dalphabet :: Alpha
               } deriving (Show)

-- DFA that accepts all strings
sigmaStarDfa :: Alpha -> DFA
sigmaStarDfa ab = DFA {dstart = 0, 
                       dstates = Set.singleton 0,
                       daccept = Set.singleton 0,
                       dtransition = Map.empty,
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
                         dtransition = Map.fromList [((0,s),1) | s <- NonEmpty.toList ab],
                         dalphabet = ab}

withQState :: QState -> DFA -> DFA
withQState q dfa = dfa { dstates = Set.insert q (dstates dfa) }

withAccepts :: Set QState -> DFA -> DFA
withAccepts qs dfa = dfa { daccept = qs }

withTransition :: (QState, Char) -> QState -> DFA -> DFA
withTransition qc q' dfa = dfa { dtransition = Map.insert qc q' (dtransition dfa) }

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

-- TODO: more tests
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

startQStateSame :: Map QState QState -> DFA -> DFA -> Bool
startQStateSame m d1 d2 = case (Map.lookup (dstart d1) m) of 
                            Just q2 -> (dstart d1) == q2
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
        transitionsSame m d1 d2 ~?= True
      ]

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

-- TODO: more tests!
testEqDFA :: Test
testEqDFA = "test isomorphic DFA" ~: 
  let ab = NonEmpty.fromList "01"
      d1 = sigmaStarDfa ab
      d2 = emptySetDfa ab
      in TestList[
        d1 == d1 ~?= True,
        d2 == d2 ~?= True,
        d1 == d2 ~?= False,
        d2 == d1 ~?= False
      ]

main :: IO ()
main = do
    runTestTT $ TestList [testDecideStringDfa,
                          testStartQStateSame,
                          testTransitionsSame, 
                          testAcceptQStatesSame, 
                          testEqDFA]
    return ()