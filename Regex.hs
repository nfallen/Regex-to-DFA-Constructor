{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

-- https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial#Template_Haskell_for_building_Embedded_Domain_specific_Languages_.28EDSLs.29

module Regex where

import Prelude

import Data.Set (Set)
import qualified Data.Set as Set (singleton, fromList, member, delete)

import Data.Generics

import Data.Map (Map)
import qualified Data.Map as Map (fromList, empty, unionWith, singleton)

import Control.Applicative(Alternative(..))
import Control.Monad (ap)

import Text.Parsec as P hiding (Empty)

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

data RegExp = Char (Set Char)      -- single literal character
            | Alt RegExp RegExp    -- r1 | r2   (alternation)
            | Seq RegExp RegExp    -- r1 r2     (concatenation)
            | Star RegExp          -- r*        (Kleene star)
            | Empty                -- ε, accepts empty string
            | Void                 -- ∅, always fails
            | Mark String RegExp   -- for marked subexpressions
            | Var String           -- a variable holding another regexp
  deriving (Show, Eq)

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
  singlechar = (Char . Set.singleton) <$> noneOf specials
  charclass  = fmap (Char . Set.fromList) $
                 P.char '[' *> content <* P.char ']'
  content    = try (concat <$> many1 range)
                 P.<|> many1 (noneOf specials)
  range      = enumFromTo
                 <$> (noneOf specials <* P.char '-')
                 <*> noneOf specials
  alts       = try (Alt <$> seqs <*> (P.char '|' *> alts)) P.<|> seqs
  seqs       = try (Seq <$> star <*> seqs) P.<|> star
  star       = try (Star <$> (atom <* P.char '*'))
                 P.<|> try (Star <$> (P.char '(' *> alts <* string ")*"))
                 P.<|> atom
  specials   = "[]()*|"

instance Lift a => Lift (Set a) where
  lift set = appE (varE `Set.fromList) (lift (Set.toList set))

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
