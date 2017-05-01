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
chars           = [regex|[0123]|]
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
               dalphabet = return 'a'},
    brzozowskiConstruction (rSeq (rStar (rChar "1")) (rStar (rChar "1")))
      ~?= DFA {dstart = 0,
               dstates = Set.fromList [0], 
               daccept = Set.fromList [0],
               dtransition = Map.fromList [((0,'1'),0)], 
               dalphabet = return '1'},
    brzozowskiConstruction (rSeq (rStar (rChar "01")) (rChar "01"))
      ~?= DFA {dstart = 0,
               dstates = Set.fromList [0,1], 
               daccept = Set.fromList [1], 
               dtransition = Map.fromList [((0,'0'),1),
                                           ((0,'1'),1),
                                           ((1,'0'),1),
                                           ((1,'1'),1)],
               dalphabet = NonEmpty.fromList "01"}]

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
    thompsonConstruction Empty ~?= brzozowskiConstruction Empty,
    thompsonConstruction [regex|(0|1)*|]
      ~?= brzozowskiConstruction [regex|(0|1)*|],
    thompsonConstruction (rAlt (rChar "a") (rChar "b")) 
      ~?= brzozowskiConstruction (rAlt (rChar "a") (rChar "b")),
    thompsonConstruction (rSeq (rChar "a") (rChar "b"))
      ~?= brzozowskiConstruction (rSeq (rChar "a") (rChar "b")),
    thompsonConstruction (rStar (rChar "a")) 
      ~?= brzozowskiConstruction (rStar (rChar "a")),
    thompsonConstruction (rStar (rChar "abc")) 
      ~?= brzozowskiConstruction (rStar (rChar "abc")),
    thompsonConstruction (rAlt (rChar "a") (rStar (rChar "b")))
      ~?= brzozowskiConstruction (rAlt (rChar "a") (rStar (rChar "b"))),
    thompsonConstruction (rSeq (rAlt (rChar "1") Empty) (rChar "0"))
      ~?= brzozowskiConstruction (rSeq (rAlt (rChar "1") Empty) (rChar "0")),
    thompsonConstruction (rSeq (rStar (rChar "1")) (rChar "0"))
      ~?= brzozowskiConstruction (rSeq (rStar (rChar "1")) (rChar "0")),
    thompsonConstruction (rStar (rSeq (rChar "0") (rStar (rChar "0"))))
      ~?= brzozowskiConstruction (rStar (rSeq (rChar "0") (rStar (rChar "0")))),
    thompsonConstruction (rSeq (rStar (rChar "01")) (rStar (rChar "0")))
      ~?= brzozowskiConstruction (rSeq (rStar (rChar "01")) (rStar (rChar "0")))
  ]

newtype ZOString = ZOString {str :: String} deriving (Show)

instance Arbitrary ZOString where
  arbitrary = do
      (k :: Int) <- choose (0, 50)
      ZOString <$> sequence [ (choose ('0','1')) | _ <- [1..k]]

propIndistinguishable :: RegExp -> ZOString -> Bool
propIndistinguishable regexp s = 
  let thomDfa = dfaConstruction $ thompsonNfaConstruction regexp in
  case mergeIndistinguishable thomDfa of 
    Nothing -> False
    Just minDfa -> 
      decideString thomDfa (str s) == decideString minDfa (str s)

propMinimization :: RegExp -> ZOString -> Bool
propMinimization regexp s = 
  let thomDfa = dfaConstruction $ thompsonNfaConstruction regexp
      minDfa = dfaMinimization thomDfa in
  decideString thomDfa (str s) == decideString minDfa (str s)

propNfaDfaAcceptSame :: RegExp -> ZOString -> Bool
propNfaDfaAcceptSame regexp s = let thomNfa = thompsonNfaConstruction regexp in
                                let thomDfa = dfaConstruction thomNfa in
                                decideString thomNfa (str s) == decideString thomDfa (str s)

-- On any arbitrary regular expression, the two construction algorithms produce isomorphic DFAs
propIsomorphic :: RegExp -> Bool
propIsomorphic regexp = thompsonConstruction regexp == brzozowskiConstruction regexp

-- For any arbitrary regular expression and string, the DFAs produced 
-- by the two construction algorithms either both accept or both reject
propAcceptSame :: RegExp -> ZOString -> Bool
propAcceptSame regexp s = let thomDfa = thompsonConstruction regexp
                              brzDfa = brzozowskiConstruction regexp
                          in decideString brzDfa (str s) == decideString thomDfa (str s)

-- TODO: generate arbitrary strings that match regexes using QuickCheck and make sure the
-- generated DFAs accept

test :: IO ()
test = do
    Automata.test
    DFA.test
    NFA.test 
    Construction.test 
    runTestTT $ TestList [testBrzozowskiConstruction,
                          testThompsonConstruction,
                          testConstructionsIsomorphic]

    quickCheck $ propNfaDfaAcceptSame
    quickCheck $ propIndistinguishable
    quickCheck $ propMinimization
    quickCheck $ propAcceptSame
    quickCheck $ propIsomorphic
