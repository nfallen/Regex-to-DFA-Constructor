{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Comparison where 

import Prelude 
import Language.Haskell.TH
import Control.DeepSeq

import Regex
import Alpha
import Automata
import DFA
import NFA
import Construction 
import Tests

import Criterion.Main

deriveNFData ''DFA

main :: IO()
main = defaultMain [
		 bench "thompsonConstruction [regex|(0|1)*|]" $ nf thompsonConstruction [regex|(0|1)*|],
		 bench "brzozowskiConstruction [regex|(0|1)*|]" $ nf brzozowskiConstruction [regex|(0|1)*|],
		 bench "thompsonConstruction validDotComMail" $ nf thompsonConstruction validDotComMail,
		 bench "brzozowskiConstruction validDotComMail" $ nf brzozowskiConstruction validDotComMail,
		 bench "thompsonConstruction (ab)*|b*" $ whnf thompsonConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b"))),
		 bench "brzozowskiConstruction (ab)*|b*" $ whnf brzozowskiConstruction (rAlt (rStar (rSeq (rChar "a") (rChar "b"))) 
                    (rStar (rChar "b")))]

