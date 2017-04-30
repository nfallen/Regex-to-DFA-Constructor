{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Comparison where 

import Prelude 

import Regex
import Alpha
import Automata
import DFA
import NFA
import Construction 
import Tests

import Criterion.Main

main :: IO()
main = defaultMain [
		 bench "thompsonConstruction [regex|(0|1)*|]" $ whnf thompsonConstruction [regex|(0|1)*|],
		 bench "brzozowskiConstruction [regex|(0|1)*|]" $ whnf brzozowskiConstruction [regex|(0|1)*|],
		 bench "thompsonConstruction validDotComMail" $ whnf thompsonConstruction validDotComMail,
		 bench "brzozowskiConstruction validDotComMail" $ whnf brzozowskiConstruction validDotComMail,
		 bench "thompsonConstruction (ab)*|b*" $ whnf thompsonConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b"))),
		 bench "brzozowskiConstruction (ab)*|b*" $ whnf brzozowskiConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b")))]

