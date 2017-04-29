{-# OPTIONS -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, PatternSynonyms, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Alpha (Alpha, alpha, unionAlpha, defaultAlpha, zeroOneAlpha) where

import Prelude

import Data.List (union)

import Data.List.NonEmpty (NonEmpty, nonEmpty, fromList, nub, toList)

import Data.Semigroup

import Regex

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  

type Alpha = NonEmpty Char

defaultAlpha :: Alpha
defaultAlpha = return '0'

zeroOneAlpha :: Alpha
zeroOneAlpha = fromList "01"

createAlpha :: RegExp -> [Char]
createAlpha Empty       = []
createAlpha Void        = []
createAlpha (Char cs)   = toList cs
createAlpha (Alt r1 r2) = createAlpha r1 `union` createAlpha r2
createAlpha (Seq r1 r2) = createAlpha r1 `union` createAlpha r2
createAlpha (Star r1)   = createAlpha r1

alpha :: RegExp -> Alpha
alpha r = 
  case nonEmpty (createAlpha r) of
      Nothing -> defaultAlpha
      Just ne -> ne

unionAlpha :: Alpha -> Alpha -> Alpha
a1 `unionAlpha` a2 = nub $ a1 <> a2

testAlpha :: Test 
testAlpha = TestList [
  alpha (rSeq 
          (rChar "a") 
          (rChar "b")) 
  ~?= fromList "ab"]
  