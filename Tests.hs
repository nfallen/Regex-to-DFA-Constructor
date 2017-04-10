{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Tests where

import Prelude

import Regex
import Automata
import Construction

import Data.Set (Set)
import qualified Data.Set as Set

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  
import Test.QuickCheck
import Test.QuickCheck.Function

chars, validDotComMail :: RegExp
chars           = [regex|[a-z]|[A-Z]|[0-9]|[-_.]|]
validDotComMail = [regex|${plus chars}@${plus chars}.com|]
 
plus :: RegExp -> RegExp
plus r = Seq r (Star r)

testConstructionsIsomorphic :: Test
testConstructionsIsomorphic = 
  TestList [
    isomorphicDFA (thompsonConstruction validDotComMail) (brzozowskiConstruction validDotComMail) ~?= True
  ]

instance Arbitrary RegExp where
   arbitrary = oneof [Char . Set.fromList <$> sublistOf "01",
                      Alt <$> arbitrary <*> arbitrary, 
                      Seq <$> arbitrary <*> arbitrary,
                      Star <$> arbitrary, 
                      return Empty,
                      return Void]
   shrink = undefined

propIsomorphic :: RegExp -> Bool
propIsomorphic regexp = isomorphicDFA (thompsonConstruction regexp) (brzozowskiConstruction regexp)

main :: IO ()
main = do
    runTestTT $ testConstructionsIsomorphic
    quickCheck $ propIsomorphic
