module Main (main) where

import Syntax
import Axioms
import Consequences
import TacticMonad
import Tactics

import Data.Either (isLeft)
import Control.Monad (unless)
import System.Exit (exitFailure)

type Test = IO Bool

checkProof :: Formula -> Tactic -> Test
checkProof formula script =
  case prove' formula script of
    Left exc -> do
      putStrLn ("✘ Proof script for '" ++ show formula ++ "' failed: '" ++ errorMsg exc ++ "'.")
      pure False
    Right _ -> do
      putStrLn ("✓ Checked proof of '" ++ show formula ++ "'.")
      pure True

checkNoProof :: String -> Formula -> Tactic -> Test
checkNoProof reason formula script =
  case prove' formula script of
    Left err -> do
      putStrLn ("✓ Tactic script failed, as it should, since " ++ reason ++ ".")
      pure True
    Right p -> do
      putStrLn
        ("✘ Tactic script succeeded proving '" ++ show formula ++ "'. " ++
         "Expected it to fail since " ++ reason ++ ".")
      pure False

phi, psi, xi :: Formula
phi = Var "x" `Elem` Var "s"
psi = Var "y" `Elem` Var "s"
xi  = Var "z" `Elem` Var "s"

tacticProof :: Test
tacticProof =
  checkProof (psi `Implies` (phi `Implies` (psi `Or` phi))) $ do
    intro "h1"
    intro "h2"
    left
    assumption "h1"

incompleteProof :: Test
incompleteProof = checkNoProof "there are open subgoals" truth (pure ())

wrongAssumptionName :: Test
wrongAssumptionName =
  checkNoProof "there is no assumption named \"g\" in scope" (psi `Implies` psi) $ do
    intro "h"
    assumption "g"

main :: IO ()
main = do
  results <- sequence
    [ checkProof (phi `Implies` phi) (exact (ax1 phi))
    , checkProof (phi `Implies` (psi `Implies` psi)) (exact (ignoreFirstArg psi phi))
    , checkProof
        ((psi `Implies` xi) `Implies` ((phi `Implies` psi) `Implies` (phi `Implies` xi)))
        (exact (compose phi psi xi))
    , tacticProof
    , incompleteProof
    , wrongAssumptionName
    ]
  unless (all id results) exitFailure
