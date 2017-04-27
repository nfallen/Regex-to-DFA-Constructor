module Construction where

import Regex
import Automata
import DFA
import NFA

import Data.List
import qualified Data.List as List

import Data.Map (Map)
import qualified Data.Map as Map 

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Text.Parsec as P hiding (Empty)

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
thompsonNfaConstruction (Char c) =  unionList clist 	where clist = Set.toList c
thompsonNfaConstruction (Alt r1 r2) = unionNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Seq r1 r2) = concatNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Star r) = kleeneNfa (thompsonNfaConstruction r)

unionList (x:xs) = unionNfa (singleCharNfa x) (thompsonNfaConstruction (Char (Set.fromList xs))) 	 
unionList [] = emptyNFA

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

dfaConstruction :: NFA -> DFA 
dfaConstruction = undefined 


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


main :: IO ()
main = do
    runTestTT $ TestList [testThompsonNfaConstruction]
    return ()
