module Construction where

import Regex
import Automata

import Data.Map (Map)
import qualified Data.Map as Map 

import Data.Set (Set)
import qualified Data.Set as Set

--TODO: how to define alphabet here 

thompsonConstruction :: RegExp -> NFA
thompsonConstruction = undefined

singleCharThompson :: Set Char -> Maybe Char -> NFA --TODO: Change type signature to DFA when DFA converter is implemented 
singleCharThompson ab char = let singleStates = Map.insert 1 True (Map.singleton 0 False) in 
                             let singleTransition = Map.insert (0, char) (Set.singleton 1) Map.empty in
                                 NFA {nstart = 0, nstates = singleStates, ntransition = singleTransition, nalphabet = ab}

unionThompson :: Set Char -> RegExp -> NFA
unionThompson ab (Alt r1 r2) = let n1 = thompsonConstruction r1 in
                               let n2 = thompsonConstruction r2 in
                                    let unionStates = Map.union (Map.mapKeys (+1) (nstates n1)) (Map.mapKeys (+ (Map.size (nstates n1) - 1)) (nstates n2)) in -- add new start and finish
                                    let unionTransition = Map.union (Map.mapKeys (\(a,b) -> (a + 1,b)) (ntransition n1)) (Map.mapKeys (\(a,b) -> (a + Map.size (ntransition n1) - 1,b)) (ntransition n2)) in --add new start finish transitions
                                        NFA {nstart = 0, nstates = unionStates, ntransition = unionTransition, nalphabet = ab}



concatThompson :: Set Char -> RegExp -> NFA
concatThompson ab (Seq r1 r2) = undefined 

kleeneThompson :: Set Char -> RegExp -> NFA
kleeneThompson ab (Star r) = undefined 

brzozowskiConstruction :: RegExp -> DFA
brzozowskiConstruction = undefined

dfaConstruction :: NFA -> DFA 
dfaConstruction = undefined 

