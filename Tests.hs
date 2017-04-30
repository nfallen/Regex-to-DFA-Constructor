{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Tests where

import Prelude

import Regex
import Alpha
import Automata
import DFA
import NFA
import Construction

import Data.List.NonEmpty as NonEmpty

import Data.Map (Map)
import qualified Data.Map as Map 

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  
import Test.QuickCheck
import Test.QuickCheck.Function

import Debug.Trace

chars, validDotComMail :: RegExp
chars           = [regex|[0-9]|]
validDotComMail = [regex|${plus chars}@${plus chars}.com|]
 
plus :: RegExp -> RegExp
plus r = rSeq r (rStar r)

testBrzozowskiConstruction :: Test
testBrzozowskiConstruction = "brzozowski construction" ~:
  TestList [
    brzozowskiConstruction Empty ~?= emptyStringDfa defaultAlpha,
    brzozowskiConstruction [regex|(0|1)*|] ~?= sigmaStarDfa zeroOneAlpha,
    brzozowskiConstruction (rStar (rChar "a"))
      ~?= DFA {dstart = 0, 
               dstates = Set.singleton 0,
               daccept = Set.singleton 0,
               dtransition = Map.fromList [((0,'a'),0)],
               dalphabet = return 'a'}
  ]

testThompsonConstruction :: Test
testThompsonConstruction = 
  TestList [
    thompsonConstruction Empty ~?= emptyStringDfa defaultAlpha,
    thompsonConstruction [regex|(0|1)*|] ~?= sigmaStarDfa zeroOneAlpha,
    thompsonConstruction (rStar (rChar "a"))
      ~?= DFA {dstart = 0, 
               dstates = Set.singleton 0,
               daccept = Set.singleton 0,
               dtransition = Map.fromList [((0,'a'),0)],
               dalphabet = return 'a'}
  ]

--TODO: optimizations (character set, optimized NFA operations) 
-- to make Thompson construction run in reasonable time
testConstructionsIsomorphic :: Test
testConstructionsIsomorphic = 
  TestList [
    thompsonConstruction (rAlt (rChar "a") (rChar "b")) 
      ~?= brzozowskiConstruction (rAlt (rChar "a") (rChar "b")),
    thompsonConstruction (rSeq (rChar "a") (rChar "b"))
      ~?= brzozowskiConstruction (rSeq (rChar "a") (rChar "b")),
    thompsonConstruction (rStar (rChar "a")) 
      ~?= brzozowskiConstruction (rStar (rChar "a")),
    thompsonConstruction (rAlt (rChar "a") (rStar (rChar "b")))
      ~?= brzozowskiConstruction (rAlt (rChar "1") (rStar (rChar "1"))),
    thompsonConstruction validDotComMail 
      ~?= brzozowskiConstruction validDotComMail
  ]

newtype ZOString = ZOString {str :: String} deriving (Show)

instance Arbitrary ZOString where
  arbitrary = do
      (k :: Int) <- choose (0, 50)
      ZOString <$> sequence [ (choose ('0','1')) | _ <- [1..k]]

instance Arbitrary RegExp where
   arbitrary = frequency [(3, rChar <$> sublistOf "01"),
                          (1, return Empty),
                          (1, rAlt <$> arbitrary <*> arbitrary), 
                          (1, rSeq <$> arbitrary <*> arbitrary),
                          (1, rStar <$> arbitrary)]
   shrink (Char cs)   = [rChar "0", rChar "1"]
   shrink (Alt r1 r2) = [r1, r2]
   shrink (Seq r1 r2) = [r1, r2]
   shrink (Star r)    = [r]
   shrink _           = []

-- On any arbitrary regular expression, the two construction algorithms produce isomorphic DFAs
propIsomorphic :: RegExp -> Bool
propIsomorphic regexp = thompsonConstruction regexp == brzozowskiConstruction regexp

-- For any arbitrary regular expression and string, the DFAs produced 
-- by the two construction algorithms either both accept or both reject
propAcceptSame :: RegExp -> ZOString -> Bool
propAcceptSame regexp s = let thomDfa = thompsonConstruction regexp
                              brzDfa = brzozowskiConstruction regexp
                          in decideString brzDfa (str s) == decideString thomDfa (str s)

propNfaDfaAcceptSame :: RegExp -> ZOString -> Bool
propNfaDfaAcceptSame regexp s = let thomNfa = thompsonNfaConstruction regexp in
                                let thomDfa = dfaConstruction thomNfa in
                                decideString thomNfa (str s) == decideString thomDfa (str s)

-- TODO: generate arbitrary strings that match regexes using QuickCheck and make sure the
-- generated DFAs accept

main :: IO ()
main = do
    runTestTT $ TestList [testBrzozowskiConstruction,
                          testThompsonConstruction,
                          testConstructionsIsomorphic]
    quickCheck $ propIsomorphic
    quickCheck $ propAcceptSame
    quickCheck $ propNfaDfaAcceptSame
