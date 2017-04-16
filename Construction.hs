module Construction where

import Regex
import Automata
import DFA
import NFA

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




main :: IO ()
main = do
    runTestTT $ TestList [testThompsonNfaConstruction]
    return ()
