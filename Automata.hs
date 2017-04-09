import Data.List as List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map 
import Regex

type State = Int

type Dtransition = Map (State, Char) State

type Ntransition = Map (State, Char) (Set State)

type States = Map State Bool


data DFA = DFA {dstates :: States, dtransition :: Dtransition, dalphabet :: Set Char}

data NFA = NFA {nstates :: States, ntransition :: Ntransition, nalphabet :: Set Char}


acceptDFA :: Set Char -> DFA
acceptDFA ab = DFA {dstates = Map.singleton 0 True, dtransition = Map.empty, dalphabet = ab}

rejectDFA :: Set Char -> DFA
rejectDFA ab = DFA {dstates = Map.singleton 0 False, dtransition = Map.empty, dalphabet = ab}

--transitionMap ::
--transitionMap = Map.empty

--addDTransition

isomorphicDFA :: DFA -> DFA -> Bool 
isomorphicDFA d1 d2 = undefined

stateBijections :: States -> States -> [Map State State]
stateBijections s1 s2 = let m = Map.empty 
                            xs = Map.keys s1 
                            perms = List.permutations (Map.keys s2) in 
                            fmap (\(x,y) -> Map.insert x y m) $ concat $ fmap (\perm -> zip xs perm) perms