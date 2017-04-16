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
thompsonConstruction regexp = let nfa = thompsonNfaConstruction regexp
                              in dfaConstruction nfa

thompsonNfaConstruction :: RegExp -> NFA

thompsonNfaConstruction Empty = emptyStringNfa (Set.empty)
thompsonNfaConstruction Void = emptySetNfa (Set.empty :: Set Char)
thompsonNfaConstruction (Var s) = case (P.parse regexParser "" s) of 
                                    Left err -> emptySetNfa (Set.empty :: Set Char) --creates the void dfa upon invalid string input
                                    Right regexp -> thompsonNfaConstruction regexp 
thompsonNfaConstruction (Char c) =  unionList clist   where clist = Set.toList c
thompsonNfaConstruction (Alt r1 r2) = unionNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Seq r1 r2) = concatNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Star r) = kleeneNfa (thompsonNfaConstruction r)

unionList (x:xs) = unionNfa (singleCharNfa x) (thompsonNfaConstruction (Char (Set.fromList xs)))   
unionList [] = emptySetNfa (Set.empty :: Set Char)

testThompsonNfaConstruction :: Test
testThompsonNfaConstruction = TestList [
  thompsonNfaConstruction (Char $ Set.singleton 'a') ~?= 
    NFA {
    nstart = 0,
    nstates = Set.fromList [0,1],
    naccept = Set.singleton 1,
    ntransition = Map.fromList [((0,Just 'a'), Set.singleton 1)],
    nalphabet = Set.singleton 'a'
  },
  thompsonNfaConstruction (Star (Seq (Char $ Set.singleton 'a') (Char $ Set.singleton 'b'))) ~?= 
    NFA {
      nstart = 0,
      nstates = Set.fromList [0,1,2,3,4,5],
      naccept = Set.singleton 5,
      ntransition = Map.fromList [((0,Nothing), Set.fromList [1,5]),
                                  ((1,Nothing), Set.fromList [2,4]),
                                  ((2, Just 'a'), (Set.singleton 3)),
                                  ((4, Just 'b'), (Set.singleton 5)),
                                  ((4, Nothing), (Set.fromList [5,1])),
                                  ((3,Nothing), (Set.singleton 4))],
      nalphabet = Set.fromList "ab"
    },
    thompsonNfaConstruction (Alt (Star (Seq (Char $ Set.singleton 'a') (Char $ Set.singleton 'b'))) 
                  (Star (Seq (Char $ Set.singleton 'a') (Char $ Set.singleton 'b')))) ~?= 
    NFA {
      nstart = 0,
      nstates = Set.fromList [0,1,2,3,4,5],
      naccept = Set.singleton 5,
      ntransition = Map.fromList [((0,Nothing), Set.fromList [1,5]),
                                  ((1,Nothing), Set.fromList [2,4]),
                                  ((2, Just 'a'), (Set.singleton 3)),
                                  ((4, Just 'b'), (Set.singleton 5)),
                                  ((4, Nothing), (Set.fromList [5,1])),
                                  ((3,Nothing), (Set.singleton 4))],
      nalphabet = Set.fromList "ab"
    },
    thompsonNfaConstruction (Alt (Char $ Set.singleton 'a') (Char $ Set.singleton 'b')) ~?=
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
    runTestTT $ TestList [testDfaConstruction, testThompsonNfaConstruction]
    return ()
