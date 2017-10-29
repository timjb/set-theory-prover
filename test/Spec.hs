{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import SetTheoryProver.Core
import SetTheoryProver.Interactive.TacticMonad
import SetTheoryProver.Interactive.Tactics
import SetTheoryProver.Lib.Logic

import Data.Either (isLeft)
import Control.Monad (unless)
import System.Exit (exitFailure)

type Test = IO Bool

checkTacticProof :: Formula -> Tactic -> Test
checkTacticProof formula script =
  case prove' formula script of
    Left exc -> do
      putStrLn ("✘ Proof script for '" ++ show formula ++ "' failed: '" ++ errorMsg exc ++ "'.")
      pure False
    Right _ -> do
      putStrLn ("✓ Checked proof of '" ++ show formula ++ "'.")
      pure True

checkNoTacticProof :: String -> Formula -> Tactic -> Test
checkNoTacticProof reason formula script =
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
phi = Var "x" :€: Var "s"
psi = Var "y" :€: Var "s"
xi  = Var "z" :€: Var "s"

tacticProof :: Test
tacticProof =
  checkTacticProof (psi :=>: phi :=>: psi :\/: phi) $ do
    intros ["h1", "h2"]
    left
    assumption "h1"

trySkipsErrors :: Test
trySkipsErrors =
  checkTacticProof (phi :=>: phi) $ do
    intro "h1"
    res <- try left -- 'left' tactic is not applicable, since goal is not a disjunction
    case res of
      Nothing -> pure ()
      Just () -> fail "expected 'try left' to return 'Nothing'"
    assumption "h1"

reflProof :: Test
reflProof =
  checkTacticProof (phi :=>: Var "x" :=: Var "x") $ do
    intro "h"
    refl

proofWithContraposition :: Test
proofWithContraposition =
  checkTacticProof ((Neg phi :=>: Neg psi) :=>: psi :=>: phi) $ do
    intro "negPhiImpliesNegPsi"
    contraposition
    assumption "negPhiImpliesNegPsi"

proofWithHave :: Test
proofWithHave =
  checkTacticProof (phi :=>: (phi :\/: psi) :/\: (phi :\/: psi)) $ do
    intro "phi"
    have "phiOrPsi" (phi :\/: psi) by $ do
      left
      assumption "phi"
    split
    assumption "phiOrPsi"
    assumption "phiOrPsi"

proofWithGeneralising :: Test
proofWithGeneralising =
  checkTacticProof (phi :=>: Forall "p" ("p" :=: "p" :/\: phi)) $ do
    intro "phi"
    generalising
    split
    refl
    assumption "phi"

proofWithExists :: Test
proofWithExists =
  checkTacticProof ("x" :€: "s" :=>: Exists "z" ("z" :€: "s" :/\: truth)) $ do
    intro "phi"
    exists "x"
    split
    someAssumption
    exact truthIsTrue

incompleteProof :: Test
incompleteProof = checkNoTacticProof "there are open subgoals" truth (pure ())

wrongAssumptionName :: Test
wrongAssumptionName =
  checkNoTacticProof "there is no assumption named \"g\" in scope" (psi :=>: psi) $ do
    intro "h"
    assumption "g"

main :: IO ()
main = do
  results <- sequence
    [ tacticProof
    , checkTacticProof (phi :=>: psi :=>: psi :\/: phi) (intros ["h1", "h2"] >> right >> assumption "h1")
    , trySkipsErrors
    , reflProof
    , proofWithContraposition
    , proofWithHave
    , proofWithGeneralising
    , proofWithExists
    , incompleteProof
    , wrongAssumptionName
    ]
  unless (all id results) exitFailure
