module Main where

import Syntax
import Axioms
import Consequences
import TacticMonad
import Tactics

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

phi, psi, xi :: Formula
phi = Var "x" `Elem` Var "s"
psi = Var "y" `Elem` Var "s"
xi  = Var "z" `Elem` Var "s"

tacticProof :: Proof
tacticProof =
  prove (psi `Implies` (phi `Implies` (psi `Or` phi))) $ do
    intro "h1"
    intro "h2"
    left
    assumption "h1"

main :: IO ()
main = do
  results <- sequence
    [ checkProof (ax1 phi) (phi `Implies` phi)
    , checkProof (ignoreFirstArg psi phi) (phi `Implies` (psi `Implies` psi))
    , checkProof (compose phi psi xi) ((psi `Implies` xi) `Implies` ((phi `Implies` psi) `Implies` (phi `Implies` xi)))
    , checkProof tacticProof (psi `Implies` (phi `Implies` (psi `Or` phi)))
    ]
  unless (all id results) exitFailure
