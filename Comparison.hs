{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Comparison where 

import Prelude 
--import Control.DeepSeq.TH

import Regex
import Alpha
import Automata
import DFA
import NFA
import Construction 
import Tests

import Criterion.Main

--deriveNFData ''DFA

main :: IO()
main = defaultMain [
		 bench "thompsonConstruction (0|1)*" $ whnf thompsonConstruction [regex|(0|1)*|],
		 bench "brzozowskiConstruction (0|1)*" $ whnf brzozowskiConstruction [regex|(0|1)*|],
		 bench "thompsonConstruction Valid E-Mail" $ whnf thompsonConstruction validDotComMail,
		 bench "brzozowskiConstruction Valid E-Mail" $ whnf brzozowskiConstruction validDotComMail,
		 bench "thompsonConstruction (ab)*|b*" $ whnf thompsonConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b"))),
		 bench "brzozowskiConstruction (ab)*|b*" $ whnf brzozowskiConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b")))]

