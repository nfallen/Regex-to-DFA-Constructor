{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Tests where

import Prelude

import Regex

chars, validDotComMail'' :: RegExp
chars             = [regex|[a-z]|[A-Z]|[0-9]|[-_.]|]
validDotComMail'' = [regex|${plus chars}@${plus chars}.com|]
 
plus :: RegExp -> RegExp
plus r = Seq r (Star r)