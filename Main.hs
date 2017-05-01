{-# OPTIONS -fwarn-incomplete-patterns -fwarn-tabs #-}
{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, ScopedTypeVariables, TemplateHaskell, QuasiQuotes #-}

module Main where

import Prelude

import Regex
import Alpha
import Automata
import DFA
import NFA
import Construction

import Control.Monad.State

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as Set

import Data.Map (Map)
import qualified Data.Map as Map 

import Test.HUnit (Test(..), (~:), (~?=), runTestTT, assertBool)  
import Test.QuickCheck
import Test.QuickCheck.Function

import Text.Parsec as P hiding (Empty)

import Debug.Trace


step :: DFA -> Char -> QState -> Maybe QState
step dfa c q = 
  if notElem c (dalphabet dfa) then Nothing
  else case Map.lookup (q,c) (dtransition dfa) of 
    Just q'  -> Just q'
    Nothing  -> Just q

stepUntilFinish :: DFA -> String -> QState -> IO ()
stepUntilFinish dfa [] q =
  if Set.member q (daccept dfa) then 
    putStrLn "String accepted!"
  else
    putStrLn "String rejected."
stepUntilFinish dfa (c:cs) q = 
  case step dfa c q of
    Nothing -> 
     putStrLn $ "character " ++ show c 
              ++ "not in DFA alphabet. Exiting."
    Just q' -> stepUntilFinish dfa cs q'


stepper :: DFA -> String -> IO ()
stepper dfa s = go dfa s (dstart dfa) where
  go dfa [] q = if Set.member q (daccept dfa) then 
                  putStrLn "String accepted!"
                else
                  putStrLn "String rejected."
  go dfa s@(c:cs) q = do
    putStrLn $ "Current state is " ++ show q ++ " and remaining string is " ++ s
    str <- getLine
    case str of
      "x"             -> return ()    -- quit the stepper
      "n"             -> case step dfa c q of
                           Nothing -> 
                             putStrLn $ "character " ++ show c 
                             ++ " not in DFA alphabet. Exiting."
                           Just q' -> go dfa cs q'
      "c"             -> stepUntilFinish dfa s q
      "d"             -> putStrLn $ show dfa
      _  -> putStrLn "?" -- unknown command
            >> go dfa s q -- remain at the same place in the program

useDfa :: DFA -> IO ()
useDfa dfa = do
  putStrLn "Enter a string to see if it is accepted by the DFA."
  putStrLn "Type 'x' to exit and enter a new regular expression."
  str <- getLine
  if str == "x" then return ()
  else do
    putStrLn $ "Stepping through DFA execution on string " ++ str
    putStrLn $ "Type 'x' to stop executing DFA, "
              ++ "'n' to step forward by one character, "
              ++ "'c' to continue executing until DFA finishes, "
              ++ "and 'd' to show the DFA again."
    stepper dfa str
    useDfa dfa

constructDfa :: RegExp -> IO ()
constructDfa r = do
  putStrLn $ "Enter 'b' to create a DFA using the Brzozowski construction "
             ++ "and 't' to create a DFA using the Thompson construction. "
  str <- getLine
  case str of
    "b" -> do 
      putStrLn "Creating DFA using Brzozowski construction."
      let dfa = brzozowskiConstruction r
      putStrLn $ "DFA is: " ++ show dfa
      useDfa dfa
    "t" -> do
      putStrLn "Creating DFA using Thompson construction."
      putStrLn "First creating NFA..."
      let nfa = thompsonNfaConstruction r
      putStrLn $ "NFA is: " ++ show nfa
      putStrLn "Now creating DFA using power set construction..."
      let dfa = dfaMinimization $ dfaConstruction nfa
      putStrLn $ "DFA is: " ++ show dfa
      useDfa dfa
    _ -> constructDfa r

main :: IO ()
main = prompt where
  prompt = do
  putStrLn "Enter a regular expression."
  str <- getLine
  case P.parse regexParser "" str of
    Left err    -> putStrLn $ "Regex failed to parse : " ++ show err
    Right regexp -> constructDfa regexp
  prompt
