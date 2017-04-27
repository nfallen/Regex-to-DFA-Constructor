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

import Debug.Trace

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  

thompsonConstruction :: RegExp -> DFA
thompsonConstruction regexp = let nfa = thompsonNfaConstruction regexp
                              in dfaConstruction nfa

thompsonNfaConstruction :: RegExp -> NFA
thompsonNfaConstruction Empty = emptyStringNfa (defaultAlpha)
thompsonNfaConstruction Void = emptySetNfa (defaultAlpha)
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

data DFASt a = DFASt { qStateCounter :: Int, 
                       qCorr  :: Map a QState,
                       getDfa :: DFA } deriving (Eq, Show)

lookupUpdate :: (Ord a, Show a) => a -> State (DFASt a) (QState, Bool)
lookupUpdate nq = do
   dst <- get
   let m = qCorr dst
   let dq = qStateCounter dst
   let dfa = getDfa dst
   case Map.lookup nq m of
     Nothing  -> put DFASt { qStateCounter = dq + 1,
                             qCorr = Map.insert nq dq m,
                             getDfa = withQState dq dfa}
                 >> trace ("\ncreating state " ++ show dq ++ " with nfa states " ++ show nq) (return ())
                 >> trace ("\nmap contains: " ++ show m) (return ())
                 >> return (dq, True)
     Just dq' -> return (dq', False)

addTransition :: NFA -> (Set QState, Char) -> State (DFASt (Set QState)) (Maybe (Set QState))
addTransition nfa (nq, c) = do
  let reachable (nq,c) = epsilonReachable nfa (symbolReachable nfa nq c)
  let nq' = reachable (nq,c)
  (dq, _) <- lookupUpdate nq
  (dq', isNew) <- lookupUpdate nq'
  trace ("\nreachable states are " ++ show nq' ++ " and state in DFA is " ++ show dq ++ "and isNew is " ++ show isNew) (return ())
  dst <- get
  put dst { getDfa = withTransition (dq,c) dq' (getDfa dst)}
  trace ("\nputting transition (" ++ show dq ++ "," ++ show c ++ ") ->" ++ show dq') (return ())
  if isNew
    then trace ("\nreturning Just " ++ show nq') (return $ Just nq')
    else trace ("\nreturning Nothing " ++ show nq') (return Nothing)

dfaStateConstruction :: NFA -> Maybe (Set QState) -> State (DFASt (Set QState)) ()
dfaStateConstruction nfa Nothing = trace ("\n got Nothing ") (return ())
dfaStateConstruction nfa (Just nq) = do
      dst <- get
      trace ("\nstate set is " ++ show nq) (return ())
      let alpha = Set.toList $ nalphabet nfa
      let qCharPairs = (\c -> (nq,c)) <$> alpha
      nq's <- sequence $ addTransition nfa <$> qCharPairs
      trace ("\nnqs are: " ++ show nq's) (return ())
      sequence_ $ dfaStateConstruction nfa <$> nq's
      return ()

getAcceptStates :: NFA -> Map (Set QState) QState -> [QState]
getAcceptStates nfa qCorr = do
  nq <- Map.keys qCorr
  if acceptsSomeState nfa nq 
  then case (Map.lookup nq qCorr) of
    Just dq -> return dq
    Nothing -> []
  else []

dfaConstruction :: NFA -> DFA 
dfaConstruction nfa = 
  let initStateSet = Just $ epsilonReachable nfa $ Set.singleton (nstart nfa)
      initDfa = DFA {
        dstart = 0, 
        dstates = Set.empty, 
        daccept = Set.empty,
        dtransition = Map.empty, 
        dalphabet = nalphabet nfa }
      initDfaSt = DFASt {
                    qStateCounter = 0,
                    qCorr = Map.empty,
                    getDfa = initDfa}
      dst = execState (dfaStateConstruction nfa initStateSet) initDfaSt
      accepts = Set.fromList $ getAcceptStates nfa (qCorr dst)
  in withAccepts accepts (getDfa dst)

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

-- return True when r matches the empty string
nullable :: RegExp -> Bool
nullable Empty  = True
nullable (Star _) = True
nullable _      = False

-- |  Takes a regular expression `r` and a character `c`,
-- and computes a new regular expression that accepts word `w` if `cw` is
-- accepted by `r`.
deriv :: RegExp -> Char -> RegExp
deriv Empty c                = Void
deriv (Char cs) c            = if Set.member c cs then Empty else Void
deriv (Alt Empty r2) c       = deriv r2 c
deriv (Alt r1 Empty) c       = deriv r1 c
deriv (Alt r1 r2) c          = rAlt (deriv r1 c) (deriv r2 c)
deriv (Seq Empty r2) c       = deriv r2 c
deriv (Seq r1 Empty) c       = deriv r1 c
deriv (Seq sr@(Star _) r2) c = rAlt (deriv sr c `rSeq` r2) (deriv r2 c)
deriv (Seq r1 r2) c          = deriv r1 c `rSeq` r2
deriv (Star r) c             = deriv r c `rSeq` rStar r
deriv Void _ = Void

brzozowskiStateConstruction :: RegExp -> State (DFASt (RegExp)) ()
brzozowskiStateConstruction r = undefined

brzozowskiConstruction :: RegExp -> DFA
brzozowskiConstruction = undefined

main :: IO ()
main = do
    runTestTT $ TestList [testDfaConstruction, testThompsonNfaConstruction]
    return ()
