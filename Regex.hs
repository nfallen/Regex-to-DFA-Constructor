{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, PatternSynonyms, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes , DeriveGeneric, DeriveAnyClass #-}

-- https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial#Template_Haskell_for_building_Embedded_Domain_specific_Languages_.28EDSLs.29

module Regex (regex, RegExp(Empty, Void), 
              pattern Char, pattern Alt, pattern Seq, pattern Star, 
              rAlt, rSeq, rStar, rChar, regexParser) where

import Prelude

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set (singleton, empty, fromList, toList, member, delete)

import Data.List (nub)

import GHC.Generics (Generic)
import Control.DeepSeq

import Data.List.NonEmpty (nonEmpty, NonEmpty) 
import qualified Data.List.NonEmpty as NonEmpty (fromList, toList)

import Data.Generics

import Data.Map (Map)
import qualified Data.Map as Map (fromList, empty, unionWith, singleton)

import Control.Applicative(Alternative(..))
import Control.Monad (ap)

import Text.Parsec as P hiding (Empty)

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)
import Test.QuickCheck
import Test.QuickCheck.Function hiding (apply) 

pattern Char a <- CharExp a
pattern Alt a1 a2 <- AltExp a1 a2
pattern Seq a1 a2 <- SeqExp a1 a2
pattern Star a <- StarExp a

data RegExp = CharExp (NonEmpty Char)      -- single literal character
            | AltExp RegExp RegExp -- r1 | r2   (alternation)
            | SeqExp RegExp RegExp -- r1 r2     (concatenation)
            | StarExp RegExp       -- r*        (Kleene star)
            | Empty                -- ε, accepts empty string
            | Void                 -- ∅, always fails
            | Var String           -- a variable holding another regexp
  deriving (Eq, Ord, GHC.Generics.Generic, NFData)

instance Show RegExp where
  show (CharExp cs)   = "(rChar \"" ++ NonEmpty.toList cs ++ "\")"
  show (AltExp r1 r2) = "(rAlt " ++ show r1 ++ " " ++ show r2 ++ ")"
  show (SeqExp r1 r2) = "(rSeq " ++ show r1 ++ " " ++ show r2 ++ ")"
  show (StarExp r)    = "(rStar " ++ show r ++ ")"
  show Empty          = "Empty"
  show Void           = "Void"
  show (Var s)        = "(Var " ++ s ++ ")"

instance Arbitrary RegExp where
   arbitrary = frequency [(3, rChar <$> sublistOf "01"),
                          (1, return Empty),
                          (1, rAlt <$> arbitrary <*> arbitrary), 
                          (1, rSeq <$> arbitrary <*> arbitrary),
                          (1, rStar <$> arbitrary)]
   -- shrink (Char cs)   = [rChar "0", rChar "1"]
   -- shrink (Alt r1 r2) = [r1, r2]
   -- shrink (Seq r1 r2) = [r1, r2]
   -- shrink (Star r)    = [r]
   -- shrink _           = []

assocAlt :: RegExp -> RegExp -> RegExp
assocAlt r1 r2 = 
  case (r1, r2) of
    (AltExp a1 a2, _) -> 
      if a1 == r2 || a2 == r2
      then rAlt a1 a2
      else AltExp r1 r2  
    (_, AltExp a1 a2) -> 
      if a1 == r1 || a2 == r1
      then rAlt a1 a2
      else AltExp (rAlt r1 a1) a2 
    _ -> AltExp r1 r2

rAlt :: RegExp -> RegExp -> RegExp
rAlt Void x = x
rAlt x Void = x
rAlt (StarExp r) Empty = StarExp r
rAlt Empty (StarExp r) = StarExp r
rAlt r1 r2 
  | r1 == r2  = r1
  | otherwise = 
      if r1 < r2 then assocAlt r1 r2 else assocAlt r2 r1

-- Tests for Brzowski equivalence properties that guarantee convergence
testRAlt :: Test
testRAlt = "test ralt regex construction" ~:
  TestList [
    rAlt (rAlt (rChar "0") (rChar "1")) (rChar "2") ~?=
      rAlt (rChar "0") (rAlt (rChar "1") (rChar "2")),
    rAlt (rAlt (rChar "0") Empty) (rChar "2") ~?=
      rAlt (rChar "0") (rAlt Empty (rChar "2")),
    rAlt (rChar "0") (rChar "1") ~?= rAlt (rChar "1") (rChar "0"),
    rAlt (rChar "0") (rChar "0") ~?= (rChar "0")
  ]

propAltEqual :: RegExp -> Bool
propAltEqual r = rAlt r r == r

propAltAssoc :: RegExp -> RegExp -> RegExp -> Bool
propAltAssoc r1 r2 r3 = rAlt (rAlt r1 r2) r3 == rAlt r1 (rAlt r2 r3)

propAltFlip :: RegExp -> RegExp -> Bool
propAltFlip r1 r2 = rAlt r1 r2 == rAlt r2 r1

rSeq :: RegExp -> RegExp -> RegExp
rSeq Void _ = Void -- concatenating any string to void is void 
rSeq _ Void = Void
rSeq Empty x = x -- concatenating the empty string to any string is itself
rSeq x Empty = x
rSeq r1@(Star x) r2@(Star y) 
  | x == y = rStar x 
  | otherwise = SeqExp r1 r2
rSeq r1@(Seq _ _) r2 = SeqExp r1 r2
rSeq r1 r2@(Seq s1 s2) = SeqExp (SeqExp r1 s1) s2
rSeq r1 r2 = SeqExp r1 r2

rStar :: RegExp -> RegExp
rStar (Star x) = StarExp x -- two iterations is the same as one
rStar Empty    = Empty -- iterating the empty string is the empty string
rStar Void     = Empty -- zero or more occurrences of void is empty
rStar r        = StarExp r -- no optimization

rChar :: [Char] -> RegExp
rChar cs  = case nonEmpty (nub cs) of
  Nothing -> Empty
  Just ne -> CharExp ne

regex :: QuasiQuoter
regex = QuasiQuoter {
    quoteExp  = compile,
    quotePat  = notHandled "patterns",
    quoteType = notHandled "types",
    quoteDec  = notHandled "declarations"
  }
  where notHandled things = error $
          things ++ " are not handled by the regex quasiquoter."
 
compile :: String -> Q Exp
compile s =
  case P.parse regexParser "" s of
    Left  err    -> fail (show err)
    Right regexp -> [e| regexp |]

regexParser :: P.Parsec String () RegExp
regexParser = alts <* eof where
  atom       = try var P.<|> char
  var        = Var <$> (string "${" *> many1 (noneOf "}") <* P.char '}')
  char       = charclass P.<|> singlechar
  singlechar = (rChar . (:[])) <$> noneOf specials
  charclass  = fmap rChar $
                 P.char '[' *> content <* P.char ']'
  content    = try $ P.many (noneOf specials)
  alts       = try (rAlt <$> seqs <*> (P.char '|' *> alts)) P.<|> seqs
  seqs       = try (rSeq <$> star <*> seqs) P.<|> star
  star       = try (rStar <$> (atom <* P.char '*'))
                 P.<|> try (rStar <$> (P.char '(' *> alts <* string ")*"))
                 P.<|> atom
  specials   = "[]()*|"

instance (Ord a, Lift a) => Lift (NonEmpty a) where 
  lift ne = TH.appE (TH.varE 'NonEmpty.fromList) (lift (NonEmpty.toList ne))

instance Lift RegExp where
  -- lift :: RegExp -> Q Exp
  lift (CharExp cs)     = apply 'CharExp  [lift cs]
  lift (AltExp r1 r2)   = apply 'AltExp   (map lift [r1, r2])
  lift (SeqExp r1 r2)   = apply 'SeqExp   (map lift [r1, r2])
  lift (StarExp r1)     = apply 'StarExp  (map lift [r1])
  lift Empty         = apply 'Empty []
  lift Void          = apply 'Void  []
  lift (Var vars)    = foldl1 TH.appE $ map (TH.varE . mkName) (words vars)
 
apply :: Name -> [Q Exp] -> Q Exp
apply n = foldl TH.appE (TH.conE n)

test :: IO ()
test = do
    runTestTT $ testRAlt
    quickCheck $ propAltEqual
    quickCheck $ propAltAssoc
    quickCheck $ propAltFlip
    return ()
