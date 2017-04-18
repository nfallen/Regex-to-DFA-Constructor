{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Tests where

import Prelude

import Regex
import Automata
import DFA
import NFA
import Construction

import Data.Map (Map)
import qualified Data.Map as Map 

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  
import Test.QuickCheck
import Test.QuickCheck.Function

import Debug.Trace

chars, validDotComMail :: RegExp
chars           = [regex|[a-z]|[A-Z]|[0-9]|[-_.]|]
validDotComMail = [regex|${plus chars}@${plus chars}.com|]
 
plus :: RegExp -> RegExp
plus r = Seq r (Star r)

zeroOneAlph = Set.fromList['0','1']

testBrzozowskiConstruction :: Test
testBrzozowskiConstruction = 
  TestList [
    brzozowskiConstruction Empty ~?= emptyStringDfa zeroOneAlph,
    brzozowskiConstruction [regex|(0|1)*|] ~?= sigmaStarDfa zeroOneAlph
  ]

testThompsonConstruction :: Test
testThompsonConstruction = 
  TestList [
    thompsonConstruction Empty ~?= emptyStringDfa zeroOneAlph,
    thompsonConstruction [regex|(0|1)*|] ~?= sigmaStarDfa zeroOneAlph
  ]

testConstructionsIsomorphic :: Test
testConstructionsIsomorphic = 
  TestList [
    thompsonConstruction validDotComMail == brzozowskiConstruction validDotComMail ~?= True
  ]

newtype ZOString = ZOString {str :: String} deriving (Show)

instance Arbitrary ZOString where
  arbitrary = do
      (k :: Int) <- choose (0, 50)
      ZOString <$> sequence [ (choose ('0','1')) | _ <- [1..k]]

instance Arbitrary RegExp where
   arbitrary = oneof [Char . Set.fromList <$> sublistOf "01",
                      Alt <$> arbitrary <*> arbitrary, 
                      Seq <$> arbitrary <*> arbitrary,
                      Star <$> arbitrary, 
                      return Empty,
                      return Void]
   shrink = undefined

-- On any arbitrary regular expression, the two construction algorithms produce isomorphic DFAs
propIsomorphic :: RegExp -> Bool
propIsomorphic regexp = thompsonConstruction regexp == brzozowskiConstruction regexp

-- For any arbitrary regular expression and string, the DFAs produced 
-- by the two construction algorithms either both accept or both reject
propAcceptSame :: RegExp -> ZOString -> Bool
propAcceptSame regexp s = let thomDfa = thompsonConstruction regexp
                              brzDfa = brzozowskiConstruction regexp
                          in decideString brzDfa (str s) == decideString thomDfa (str s)

propThompsonFinishes :: RegExp -> ZOString -> Bool
propThompsonFinishes regexp s = let thomNfa = thompsonNfaConstruction regexp in
                                trace (show thomNfa) True

propDfaFinishes :: RegExp -> ZOString -> Bool
propDfaFinishes regexp s = let thomNfa = thompsonNfaConstruction regexp in
                           let thomDfa = dfaConstruction thomNfa in
                           trace (show thomDfa) True

-- TODO: debug
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
