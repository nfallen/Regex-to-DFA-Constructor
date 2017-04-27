module Construction where

import Regex
import Automata
import DFA
import NFA

import Data.List
import qualified Data.List as List
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

dfaMinimization :: DFA -> DFA
dfaMinimization d = mergePair (deleteUnreachable d (Set.toList (dstates d))) 
                              $ allPairs $ Set.toList $ dstates d

-- TODO: more tests
testdfaMinimization :: Test
testdfaMinimization = "Resulting DFA is minimized" ~:
  TestList[
    
  ]

deleteUnreachable :: DFA -> [Automata.State] -> DFA
deleteUnreachable d [] = d
deleteUnreachable d @states(x:xs) = if ((not $ inwardTransition x $ dtransition d) && not (x == dstart d)) 
                                    then deleteUnreachable (DFA {dstart = dstart d,
                                                                 dstates = Set.delete x (dstates d),
                                                                 daccept = daccept d,  
                                                                 dtransition = Map.fromList $ deleteKey x $ Map.toList $ dtransition d, 
                                                                 dalphabet = dalphabet d }) xs 
                                    else deleteUnreachable d xs 

-- TODO: more tests
testdeleteUnreachable :: Test
testdeleteUnreachable = "Unreachable states deleted from resulting DFA" ~:
  TestList[
    
  ]


deleteKey :: Automata.State -> [((Automata.State, Char), Automata.State)] -> [((Automata.State, Char), Automata.State)] 
deleteKey k translist = List.filter (\((a,b),c) -> not (a == k)) translist 

replaceInwardTransitions :: Automata.State -> Automata.State-> [((Automata.State, Char), Automata.State)] -> [((Automata.State, Char), Automata.State)] 
replaceInwardTransitions k1 k2 translist = List.map (\((a,b),c) -> ((a,b),k2)) 
                                           $ List.filter (\((a,b),c) -> (c == k1)) translist                                  

inwardTransition :: Automata.State -> Dtransition -> Bool 
inwardTransition s transmap = elem s (Map.elems transmap)  

allPairs :: [Automata.State] -> [(Automata.State,Automata.State)]
allPairs states = [(s1,s2) | s1 <- states, s2 <- states, s1 < s2]

mergePair :: DFA -> [(Automata.State,Automata.State)] -> DFA
mergePair d [] = d 
mergePair d (x:xs) =  let newd = mergeIndistinct d (fst x) (snd x) in
                          if (newd == d) 
                          then mergePair d xs -- try next pair in dfa d
                          else mergePair newd xs 

mergeIndistinct :: DFA -> Automata.State -> Automata.State -> DFA
mergeIndistinct d x1 x2 = if indistinct d x1 x2 
                          then  DFA {dstart = dstart d,
                                     dstates = Set.delete x2 (dstates d),
                                     daccept = daccept d,  
                                     dtransition = Map.union (Map.fromList (deleteKey x2 (Map.toList (dtransition d))))
                                                   $ Map.fromList $ replaceInwardTransitions x2 x1 $ Map.toList $ dtransition d, 
                                     dalphabet = dalphabet d}
                          else d 

indistinct :: DFA -> Automata.State -> Automata.State -> Bool
indistinct d1 s1 s2 = if (((Set.member s1 $ daccept d1) && not (Set.member s2 $ daccept d1)) ||
                               ((Set.member s2 $ daccept d1) && not (Set.member s1 $ daccept d1)))
                      then False
                      else transitionsDistinct d1 s1 s2 where
                           transitionsDistinct :: DFA -> Automata.State -> Automata.State -> Bool 
                           transitionsDistinct d1 s1 s2 = iterateAlphabet alist d1 s1 s2 
                                                                 where alist = Set.toList $ dalphabet d1 

iterateAlphabet :: [Char] -> DFA -> Automata.State -> Automata.State -> Bool
iterateAlphabet (x:xs) d1 s1 s2 = case (Map.lookup (s1,x) (dtransition d1)) of 
                                        Just a -> case (Map.lookup (s2,x) (dtransition d1)) of 
                                                          Just b -> a == b && iterateAlphabet xs d1 s1 s2 
                                                          _ -> False 
                                        _ -> False  
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
