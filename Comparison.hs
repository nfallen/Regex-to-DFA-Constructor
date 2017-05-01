{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Comparison where 

import Prelude 
import Control.DeepSeq

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
		 bench "thompsonConstruction (0|1)*" $ 
		 nf thompsonConstruction [regex|(0|1)*|],
		 bench "brzozowskiConstruction (0|1)*" $ 
		 nf brzozowskiConstruction [regex|(0|1)*|],
		 bench "thompsonConstruction Valid E-Mail" $ 
		 nf thompsonConstruction validDotComMail,
		 bench "brzozowskiConstruction Valid E-Mail" $ 
		 nf brzozowskiConstruction validDotComMail,
		 bench "thompsonConstruction (ab)*|b*" $ 
		 nf thompsonConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b"))),
		 bench "brzozowskiConstruction (ab)*|b*" $ 
		 nf brzozowskiConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b")))]
           

