module Construction where

import Regex
import Alpha
import Automata
import DFA
import NFA

import Data.List
import qualified Data.List as List

import Data.List.NonEmpty as NonEmpty

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
thompsonNfaConstruction r = construction r (alpha r) where
  construction Empty ab = emptyStringNfa ab
  construction Void  ab = emptySetNfa ab
  construction (Char cs) ab = foldr1 (\n1 n2 -> unionNfa n1 n2) (singleCharNfa <$> cs)
  construction (Alt r1 r2) ab = unionNfa (construction r1 ab) (construction r2 ab) 
  construction (Seq r1 r2) ab = concatNfa (construction r1 ab) (construction r2 ab) 
  construction (Star r) ab = kleeneNfa (construction r ab)

testThompsonNfaConstruction :: Test
testThompsonNfaConstruction = "thompson construction of NFA from regex" ~: 
  TestList [
    thompsonNfaConstruction (rChar "a") ~?= 
      NFA {
      nstart = 0,
      nstates = Set.fromList [0,1],
      naccept = Set.singleton 1,
      ntransition = Map.fromList [((0,Just 'a'), Set.singleton 1)],
      nalphabet = return 'a'
    },
    thompsonNfaConstruction (rStar (rSeq (rChar "a") (rChar "b"))) ~?= 
      NFA {
        nstart = 0,
        nstates = Set.fromList [0,1,2,3,4,5],
        naccept = Set.singleton 5,
        ntransition = Map.fromList [((0, Nothing), Set.fromList [1,5]),
                                    ((1, Just 'a'), Set.singleton 2),
                                    ((2, Nothing), (Set.singleton 3)),
                                    ((3, Just 'b'), (Set.singleton 4)),
                                    ((4, Nothing), (Set.fromList [1,5]))],
        nalphabet = NonEmpty.fromList "ab"
      },
      thompsonNfaConstruction (rAlt (rChar "a") (rChar "b")) ~?=
        NFA {
          nstart = 0,
          nstates = Set.fromList [0,1,2,3,4,5],
          naccept = Set.singleton 5,
          ntransition = Map.fromList [((0,Nothing), Set.fromList [1,3]),
                                      ((1, Just 'a'), (Set.singleton 2)),
                                      ((3, Just 'b'), (Set.singleton 4)),
                                      ((2,Nothing), (Set.singleton 5)),
                                      ((4,Nothing), (Set.singleton 5))],
          nalphabet = NonEmpty.fromList "ab"
        },
      thompsonNfaConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b"))) ~?= 
        NFA {
          nstart = 0, 
          nstates = Set.fromList [0,1,2,3,4,5,6,7,8,9,10,11],
          naccept = Set.fromList [11],
          ntransition = Map.fromList [((0,Nothing), Set.fromList [1,7]),
                                      ((1,Nothing), Set.fromList [2,6]),
                                      ((2,Just 'a'), Set.fromList [3]),
                                      ((3,Nothing), Set.fromList [4]),
                                      ((4,Just 'b'), Set.fromList [5]),
                                      ((5,Nothing), Set.fromList [2,6]),
                                      ((6,Nothing), Set.fromList [11]),
                                      ((7,Nothing), Set.fromList [8,10]),
                                      ((8,Just 'b'), Set.fromList [9]),
                                      ((9,Nothing), Set.fromList [8,10]),
                                      ((10,Nothing), Set.fromList [11])], 
          nalphabet = NonEmpty.fromList "ab"}]

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
      let alpha = nalphabet nfa
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
testDfaConstruction = "DFA correctly constructed from NFA" ~:
  TestList [
    dfaConstruction (singleCharNfa 'a') ~?= 
      DFA {dstart = 0, 
           dstates = Set.fromList [0,1,2],
           daccept = Set.fromList [1],
           dtransition = Map.fromList [((0,'a'),1),((1,'a'),2),((2,'a'),2)],
           dalphabet = return 'a'},
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
           dalphabet = NonEmpty.fromList "ab"}]

dfaMinimization :: DFA -> DFA
dfaMinimization d = mergePair (deleteUnreachable d (Set.toList (dstates d))) 
                              $ allPairs $ Set.toList $ dstates d

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

unreachableDFA = DFA {dstart = 0,
                      dstates = Set.fromList [0,1],
                      daccept = Set.empty,
                      dtransition = Map.fromList[((1,'a'),0),((1,'b'),0)],
                      dalphabet = NonEmpty.fromList "ab"} 

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

-- TODO: more tests
testDfaMinimization :: Test
testDfaMinimization = "Resulting DFA is minimized" ~:
  TestList[
    dfaMinimization (excessDFA) ~?= 
    DFA {dstart = 0, 
         dstates = Set.fromList [0,2,5],
         daccept = Set.fromList [2],
         dtransition = Map.fromList [((0,'0'),0),
                                     ((0,'1'),2),
                                     ((2,'0'),2),
                                     ((2,'1'),5),
                                     ((5,'0'),5),
                                     ((5,'1'),5)],
         dalphabet = NonEmpty.fromList "01"},

    dfaMinimization (DFA {dstart = 0, 
         dstates = Set.fromList [0,1,2,3],
         daccept = Set.fromList [1],
         dtransition = Map.fromList [((0,'a'),1),
                                     ((1,'a'),2),
                                     ((2,'a'),3),
                                     ((3,'a'),2)],
         dalphabet = return 'a'}) ~?=
    dfaMinimization (dfaConstruction (singleCharNfa 'a')),

    dfaMinimization (DFA {dstart = 0,
                      dstates = Set.fromList [0,1],
                      daccept = Set.empty,
                      dtransition = Map.fromList [((1,'a'),0)],
                      dalphabet = NonEmpty.fromList "ab"}) ~?=
    emptySetDfa (NonEmpty.fromList "ab")
  ]

deleteUnreachable :: DFA -> [QState] -> DFA
deleteUnreachable d [] = d
deleteUnreachable d @states(x:xs) = 
  if ((not $ inwardTransition x $ dtransition d) && not (x == dstart d)) 
    then deleteUnreachable (DFA {dstart = dstart d,
                                 dstates = Set.delete x (dstates d),
                                 daccept = daccept d,  
                                 dtransition = Map.fromList $ deleteKey x $ Map.toList $ dtransition d, 
                                 dalphabet = dalphabet d }) xs 
    else deleteUnreachable d xs 

testDeleteUnreachable :: Test
testDeleteUnreachable = "Unreachable states deleted from resulting DFA" ~:
  TestList[
    deleteUnreachable (unreachableDFA) (Set.toList $ dstates unreachableDFA) ~?= emptySetDfa (NonEmpty.fromList "ab"),
    deleteUnreachable (unreachableDFA2) (Set.toList $ dstates unreachableDFA2) ~?= excessDFA 
  ]


deleteKey :: QState -> [((QState, Char), QState)] -> [((QState, Char), QState)] 
deleteKey k translist = List.filter (\((a,b),c) -> not (a == k)) translist 

testDeleteKey :: Test
testDeleteKey = "Deletes matching keys" ~:
  TestList[
    deleteKey 3 [((3,'a'),2)] ~?= [],
    deleteKey 3 [((3,'a'),2),((3,'b'),1),((2,'a'),3)] ~?= [((2,'a'),3)],
    deleteKey 3 [((2,'a'),4),((3,'a'),2)] ~?= [((2,'a'),4)]
  ]

inwardTransition :: QState -> Dtransition -> Bool 
inwardTransition s transmap = elem s (Map.elems $ Map.filterWithKey (\(k,_) _ -> k /= s) transmap) 

testInwardTransition :: Test 
testInwardTransition = "Identifies inward transition correctly" ~:
  TestList[
    inwardTransition 3 (Map.fromList [((2,'0'),3)]) ~?= True, 
    inwardTransition 3 (Map.fromList [((3,'0'),2)]) ~?= False,
    inwardTransition 3 (Map.fromList []) ~?= False,
    inwardTransition 3 (Map.fromList[((2,'0'),1)]) ~?= False,
    inwardTransition 3 (Map.fromList [((2,'0'),3),((2,'1'),3)]) ~?= True,
    inwardTransition 3 (Map.fromList [((2,'0'),5),((2,'1'),3)]) ~?= True,
    inwardTransition 3 (Map.fromList [((2,'0'),5),((2,'1'),3),((2,'2'),1)]) ~?= True,
    inwardTransition 3 (Map.fromList [((2,'0'),5),((2,'1'),4)]) ~?= False
  ]

allPairs :: [QState] -> [(QState,QState)]
allPairs states = [(s1,s2) | s1 <- states, s2 <- states, s1 < s2]

testAllPairs :: Test
testAllPairs = "Returns all unique pairs in list" ~:
  TestList[
    allPairs [1,2,3,4,5] ~?= [(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)],
    allPairs [1] ~?= [],
    allPairs [1,2] ~?= [(1,2)],
    allPairs [] ~?= []
  ]

mergePair :: DFA -> [(QState,QState)] -> DFA
mergePair d [] = d 
mergePair d (x:xs) =  let newd = mergeIndistinct d (fst x) (snd x) in
                          if (newd == d) 
                          then mergePair d xs -- try next pair in dfa d
                          else mergePair newd $ allPairs $ Set.toList $ dstates newd

addOutward :: QState -> QState-> [((QState, Char), QState)] -> [((QState, Char), QState)] 
addOutward s1 s2 translist = translist ++ (List.map (\((a,b),c) -> ((a,b),s1)) $
                            List.filter (\((a,b),c) -> (c == s2)) translist) 

mergeIndistinct :: DFA -> QState -> QState -> DFA
mergeIndistinct d x1 x2 = if indistinct d x1 x2 
                          then  DFA {dstart = dstart d,
                                     dstates = Set.delete x2 (dstates d),
                                     daccept = Set.delete x2 $ daccept d,  
                                     dtransition = Map.fromList (addOutward x1 x2 $ 
                                                   deleteKey x2 (Map.toList (dtransition d))), 
                                     dalphabet = dalphabet d}
                          else d 

testMergeIndistinct :: Test
testMergeIndistinct = "Merges indistinct states" ~:
  TestList[
    mergeIndistinct excessDFA 2 3 ~?= DFA {dstart = 0, 
                 dstates = Set.fromList [0,1,2,4,5],
                 daccept = Set.fromList [2,4],
                 dtransition = Map.fromList [((0,'0'),1),
                                             ((0,'1'),2),
                                             ((1,'0'),0),
                                             ((1,'1'),2),
                                             ((2,'0'),4),
                                             ((2,'1'),5),
                                             ((4,'0'),4),
                                             ((4,'1'),5),
                                             ((5,'0'),5),
                                             ((5,'1'),5)],
                 dalphabet = NonEmpty.fromList "01"}  
  ]

indistinct :: DFA -> QState -> QState -> Bool
indistinct d1 s1 s2 = 
  let accepts = daccept d1 in
  Set.member s1 accepts == Set.member s2 accepts
    && transitionsIndistinct d1 s1 s2 
  where
    transitionsIndistinct :: DFA -> QState -> QState -> Bool 
    transitionsIndistinct dfa s1 s2 = foldr matches True ab where 
      ab = dalphabet d1
      matches x acc = 
        let transitions = dtransition dfa in
        case (Map.lookup (s1,x) transitions, Map.lookup (s2,x) transitions) of
          (Just a, Just b) -> acc && (a == b || a == s2 || b == s1)
          _ -> False 

testIndistinct :: Test
testIndistinct = "Determines if states are indistinct" ~:
  TestList[
    indistinct excessDFA 2 3 ~?= True,
    indistinct excessDFA 1 2 ~?= False,
    indistinct excessDFA 3 5 ~?= False
  ]

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
deriv (Char cs) c            = if elem c cs then Empty else Void
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
    runTestTT $ TestList [testDfaConstruction, testThompsonNfaConstruction,testDfaMinimization,
                          testDeleteUnreachable, testInwardTransition, testDeleteKey,
                          testAllPairs, testIndistinct, testMergeIndistinct]
    return ()
