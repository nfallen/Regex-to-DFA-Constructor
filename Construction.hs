module Construction where

import Regex
import Automata
import DFA
import NFA

import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map 

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Text.Parsec as P hiding (Empty, State)

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  

thompsonConstruction :: RegExp -> DFA
thompsonConstruction Empty = emptyStringDfa (Set.empty)
thompsonConstruction Void = emptySetDfa (Set.empty)
thompsonConstruction (Var s) = case (P.parse regexParser "" s) of 
                                    Left err -> emptySetDfa (Set.empty) --creates the void dfa upon invalid string input
                                    Right regexp -> thompsonConstruction regexp 
thompsonConstruction regexp = let nfa = thompsonNfaConstruction regexp
                              in dfaConstruction nfa

thompsonNfaConstruction :: RegExp -> NFA
thompsonNfaConstruction (Char c) =  let (x:xs) = Set.toList c in
                                    unionNfa (singleCharNfa x) (thompsonNfaConstruction (Char (Set.fromList xs)))
thompsonNfaConstruction (Alt r1 r2) = unionNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Seq r1 r2) = concatNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Star r) = kleeneNfa (thompsonNfaConstruction r)

brzozowskiConstruction :: RegExp -> DFA
brzozowskiConstruction = undefined

data DFASt = DFASt { currentState :: Int, 
                     corrStates  :: Map (Set QState) QState,
                     getDfa :: DFA } deriving (Eq, Show)

lookupUpdate :: NFA -> Set QState -> State DFASt QState
lookupUpdate nfa nq = do
   dst <- get
   let m = corrStates dst
   let dq = 1 + currentState dst
   let dfa = getDfa dst
   case Map.lookup nq m of
     Nothing  -> put DFASt { currentState = dq,
                             corrStates = Map.insert nq dq m,
                             getDfa = withQState dq (acceptStates nfa nq) dfa}
                 >> dfaStateConstruction nfa nq 
                 >> return dq
     Just dq' -> return dq'

addTransition :: NFA -> (Set QState, Char) -> State DFASt ()
addTransition nfa (nq, c) = do
  let reachable (nq,c) = epsilonReachable nfa (symbolReachable nfa nq c)
  let nq' = reachable (nq,c)
  dq <- lookupUpdate nfa nq
  dq' <- lookupUpdate nfa nq'
  dst <- get
  put dst { getDfa = withTransition (dq,c) dq' (getDfa dst)}
  return ()

dfaStateConstruction :: NFA -> Set QState -> State DFASt ()
dfaStateConstruction nfa nq = do
  let alpha = Set.toList $ nalphabet nfa
  let pairs = (\c -> (nq,c)) <$> alpha
  sequence_ (addTransition nfa <$> pairs)
  dst <- get
  return ()

dfaConstruction :: NFA -> DFA 
dfaConstruction nfa = 
  let initStateSet = epsilonReachable nfa $ Set.singleton (nstart nfa)
      initDfaSt = DFASt {
                    currentState = 0,
                    corrStates = Map.singleton initStateSet 0,
                    getDfa = if Set.member 0 (naccept nfa) 
                          then sigmaStarDfa (nalphabet nfa)
                          else emptySetDfa (nalphabet nfa)}
      (_, dst) = runState (dfaStateConstruction nfa initStateSet) initDfaSt 
  in getDfa dst

testDfaConstruction :: Test 
testDfaConstruction = TestList [
  dfaConstruction (singleCharNfa 'a') ~?= 
    DFA {dstart = 0, 
         dstates = Set.fromList [0,1,2],
         daccept = Set.fromList [1],
         dtransition = Map.fromList [((0,'a'),1),((1,'a'),2),((2,'a'),2)],
         dalphabet = Set.fromList "a"},
  dfaConstruction (unionNfa (singleCharNfa 'a') (singleCharNfa 'b')) ~?= 
    DFA {dstart = 0,
         dstates = Set.fromList [0,1,2,3],
         daccept = Set.fromList [1,3],
         dtransition = Map.fromList [((0,'a'),1),
                                     ((0,'b'),3),
                                     ((1,'a'),2),
                                     ((1,'b'),2),
                                     ((2,'a'),2),
                                     ((2,'b'),2),
                                     ((3,'a'),2),
                                     ((3,'b'),2)],
         dalphabet = Set.fromList "ab"}]

main :: IO ()
main = do
    runTestTT $ TestList [testDfaConstruction]
    return ()
