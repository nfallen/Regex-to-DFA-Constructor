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
                                    Left err -> emptySetNfa (Set.empty :: Set Char) --creates the void nfa upon invalid string input
                                    Right regexp -> thompsonNfaConstruction regexp 
thompsonNfaConstruction (Char c) =  unionList clist where clist = Set.toList c
thompsonNfaConstruction (Alt r1 r2) = unionNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Seq r1 r2) = concatNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Star r) = kleeneNfa (thompsonNfaConstruction r)

unionList (x:xs) = unionNfa (singleCharNfa x) (thompsonNfaConstruction (rChar $ Set.fromList xs))   
unionList [] = emptySetNfa (Set.empty :: Set Char)

testThompsonNfaConstruction :: Test
testThompsonNfaConstruction = TestList [
  thompsonNfaConstruction (rChar $ Set.singleton 'a') ~?= 
    NFA {
    nstart = 0,
    nstates = Set.fromList [0,1],
    naccept = Set.singleton 1,
    ntransition = Map.fromList [((0,Just 'a'), Set.singleton 1)],
    nalphabet = Set.singleton 'a'
  },
  thompsonNfaConstruction (rStar (rSeq (rChar $ Set.singleton 'a') (rChar $ Set.singleton 'b'))) ~?= 
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
    thompsonNfaConstruction (rAlt (rStar (rSeq (rChar $ Set.singleton 'a') (rChar $ Set.singleton 'b'))) 
                  (rStar (rSeq (rChar $ Set.singleton 'a') (rChar $ Set.singleton 'b')))) ~?= 
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
    thompsonNfaConstruction (rAlt (rChar $ Set.singleton 'a') (rChar $ Set.singleton 'b')) ~?=
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

lookupUpdate :: Ord a => a -> State (DFASt a) (QState, Bool)
lookupUpdate x = do
   dst <- get
   let m = qCorr dst
   let dq = qStateCounter dst
   let dfa = getDfa dst
   case Map.lookup x m of
     Nothing  -> put DFASt { qStateCounter = dq + 1,
                             qCorr = Map.insert x dq m,
                             getDfa = withQState dq dfa}
                 >> return (dq, True)
     Just dq' -> return (dq', False)

getAcceptStates :: Ord a => (a -> Bool) -> Map a QState -> Set QState
getAcceptStates pred qCorr = 
  let statesList = do
      x <- Map.keys qCorr
      if pred x
      then case (Map.lookup x qCorr) of
        Just dq -> return dq
        Nothing -> []
      else []
    in Set.fromList statesList

addTransition :: Ord a => (a -> Char -> a) -> (a, Char) -> State (DFASt (a)) (Maybe a)
addTransition next (x, c) = do
  let x' = next x c
  (dq, _) <- lookupUpdate x
  (dq', isNew) <- lookupUpdate x'
  dst <- get
  put dst { getDfa = withTransition (dq,c) dq' (getDfa dst)}
  if isNew
    then return $ Just x'
    else return Nothing

dfaStateConstruction :: NFA -> Maybe (Set QState) -> State (DFASt (Set QState)) ()
dfaStateConstruction nfa Nothing = return ()
dfaStateConstruction nfa (Just nq) = do
      dst <- get
      let alpha = Set.toList $ nalphabet nfa
      let qCharPairs = (\c -> (nq,c)) <$> alpha
      let next nq c = epsilonReachable nfa (symbolReachable nfa nq c)
      nq's <- sequence $ addTransition next <$> qCharPairs
      sequence_ $ dfaStateConstruction nfa <$> nq's
      return ()

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
      accepts = getAcceptStates (\nq -> acceptsSomeState nfa nq) (qCorr dst)
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

brzozowskiStateConstruction :: [Char] -> Maybe RegExp -> State (DFASt (RegExp)) ()
brzozowskiStateConstruction alpha Nothing  = return ()
brzozowskiStateConstruction alpha (Just r) = do     
  dst <- get
  let qCharPairs = (\c -> (r,c)) <$> alpha
  derivs <- sequence $ addTransition deriv <$> qCharPairs
  sequence_ $ brzozowskiStateConstruction alpha <$> derivs
  return ()

brzozowskiConstruction :: RegExp -> DFA
brzozowskiConstruction = undefined

main :: IO ()
main = do
    runTestTT $ TestList [testDfaConstruction, testThompsonNfaConstruction]
    return ()
