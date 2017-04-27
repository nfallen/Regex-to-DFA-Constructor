{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

-- https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial#Template_Haskell_for_building_Embedded_Domain_specific_Languages_.28EDSLs.29

module Regex where

import Prelude

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set (singleton, empty, fromList, toList, member, delete)

import Data.Generics

import Data.Map (Map)
import qualified Data.Map as Map (fromList, empty, unionWith, singleton)

import Control.Applicative(Alternative(..))
import Control.Monad (ap)

import Text.Parsec as P hiding (Empty)

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

--TODO: marked subexpressions

data RegExp = Char (Set Char)      -- single literal character
            | Alt RegExp RegExp    -- r1 | r2   (alternation)
            | Seq RegExp RegExp    -- r1 r2     (concatenation)
            | Star RegExp          -- r*        (Kleene star)
            | Empty                -- ε, accepts empty string
            | Void                 -- ∅, always fails
            | Var String           -- a variable holding another regexp
  deriving (Show, Eq)

rAlt :: RegExp -> RegExp -> RegExp
rAlt Void x = x
rAlt x Void = x
rAlt r1 r2 
  | r1 == r2  = r1
  | otherwise = Alt r1 r2

rSeq :: RegExp -> RegExp -> RegExp
rSeq Void _ = Void -- concatenating any string to void is void 
rSeq _ Void = Void
rSeq Empty x = x -- concatenating the empty string to any string is itself
rSeq x Empty = x
rSeq r1 r2 = Seq r1 r2 -- no optimization

rStar :: RegExp -> RegExp
rStar (Star x) = Star x -- two iterations is the same as one
rStar Empty    = Empty -- iterating the empty string is the empty string
rStar Void     = Empty -- zero or more occurrences of void is empty
rStar r        = Star r -- no optimization

rChar :: Set Char -> RegExp
rChar cs 
  | cs == Set.empty = Empty
  | otherwise = Char cs

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
  singlechar = (rChar . Set.singleton) <$> noneOf specials
  charclass  = fmap (rChar . Set.fromList) $
                 P.char '[' *> content <* P.char ']'
  content    = try (concat <$> many1 range)
                 P.<|> many1 (noneOf specials)
  range      = enumFromTo
                 <$> (noneOf specials <* P.char '-')
                 <*> noneOf specials
  alts       = try (rAlt <$> seqs <*> (P.char '|' *> alts)) P.<|> seqs
  seqs       = try (rSeq <$> star <*> seqs) P.<|> star
  star       = try (rStar <$> (atom <* P.char '*'))
                 P.<|> try (rStar <$> (P.char '(' *> alts <* string ")*"))
                 P.<|> atom
  specials   = "[]()*|"

instance (Ord a, Lift a) => Lift (Set a) where 
  lift set = TH.appE (TH.varE 'Set.fromList) (lift (Set.toList set))

instance Lift RegExp where
  -- lift :: RegExp -> Q Exp
  lift (Char cs)     = apply 'Char  [lift cs]
  lift (Alt r1 r2)   = apply 'Alt   (map lift [r1, r2])
  lift (Seq r1 r2)   = apply 'Seq   (map lift [r1, r2])
  lift (Star r1)     = apply 'Star  (map lift [r1])
  lift Empty         = apply 'Empty []
  lift Void          = apply 'Void  []
  lift (Var vars)    = foldl1 TH.appE $ map (TH.varE . mkName) (words vars)
 
apply :: Name -> [Q Exp] -> Q Exp
apply n = foldl TH.appE (TH.conE n)
