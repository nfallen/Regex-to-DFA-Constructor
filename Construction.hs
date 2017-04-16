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
thompsonNfaConstruction (Char c) =  let (x:xs) = Set.toList c in
                                    unionNfa (singleCharNfa x) (thompsonNfaConstruction (Char (Set.fromList xs)))
thompsonNfaConstruction (Alt r1 r2) = unionNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Seq r1 r2) = concatNfa (thompsonNfaConstruction r1) (thompsonNfaConstruction r2) 
thompsonNfaConstruction (Star r) = kleeneNfa (thompsonNfaConstruction r)

brzozowskiConstruction :: RegExp -> DFA
brzozowskiConstruction = undefined

dfaConstruction :: NFA -> DFA 
dfaConstruction = undefined 
