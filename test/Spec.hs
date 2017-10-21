module Main where

import Syntax
import Axioms

import Control.Monad (unless)
import System.Exit (exitFailure)

checkProof :: Proof -> Formula -> IO Bool
checkProof proof goal =
  if goal == getFormula proof
    then do
      putStrLn ("✓ Checked proof of '" ++ show goal ++ "'.")
      return True
    else do
      putStrLn
        ("✘ Proof doesn't show formula '" ++ show goal ++ "'. " ++
         "Instead it shows '" ++ show (getFormula proof) ++ "'.")
      return False

main :: IO ()
main = do
  results <- sequence
    [ checkProof (ax1 truth) (truth `Implies` truth)
    , checkProof (ax1 falsity) (falsity `Implies` falsity)
    ]
  unless (all id results) exitFailure
