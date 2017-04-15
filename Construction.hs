module Construction where

import Regex
import Automata
import DFA
import NFA

import Data.Map (Map)
import qualified Data.Map as Map 

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  

--TODO: how to define alphabet here 

thompsonConstruction :: RegExp -> DFA
thompsonConstruction regexp = let nfa = thompsonNfaConstruction regexp
                              in dfaConstruction nfa

thompsonNfaConstruction :: RegExp -> NFA
thompsonNfaConstruction = undefined

brzozowskiConstruction :: RegExp -> DFA
brzozowskiConstruction = undefined

dfaConstruction :: NFA -> DFA 
dfaConstruction = undefined 
