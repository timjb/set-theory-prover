{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import SetTheoryProver.Core
import SetTheoryProver.Interactive.TacticMonad
import SetTheoryProver.Interactive.Tactics

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

orCommutative :: Test
orCommutative =
  checkTacticProof (phi :\/: psi :=>: psi :\/: phi) $ do
    intro "h"
    cases "h"
    right; assumption "h"
    left; assumption "h"

proofWithContraposition :: Test
proofWithContraposition =
  checkTacticProof ((Neg phi :=>: Neg psi) :=>: psi :=>: phi) $ do
    intro "negPhiImpliesNegPsi"
    contraposition
    assumption "negPhiImpliesNegPsi"

andCommutative :: Test
andCommutative =
  checkTacticProof (phi :/\: psi :=>: psi :/\: phi) $ do
    intro "h"
    destruct "h" "hl" "hr"
    split
    assumption "hr"
    assumption "hl"

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

-- TODO:
--   phi :=>: Neg (Neg phi)
--   phi :/\: (psi :\/: xi) :=>: (phi :/\: psi) :\/: (phi :/\: xi)
--   symmetry of =
--   transitivity of =

currying :: Test
currying =
  checkTacticProof ((phi :/\: psi :=>: xi) `iff` (phi :=>: psi :=>: xi)) $ do
    split
    -- =>
    intros ["uncurriedFn", "phi", "psi"]
    apply "uncurriedFn"
    split
    assumption "phi"
    assumption "psi"
    -- <=
    intros ["curriedFn", "phiAndPsi"]
    destruct "phiAndPsi" "phi" "psi"
    have "psiImpliesXi" (psi :=>: xi) by $ do
      apply "curriedFn"
      assumption "phi"
    apply "psiImpliesXi"
    assumption "psi"

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
    , orCommutative
    , proofWithContraposition
    , andCommutative
    , proofWithHave
    , currying
    , incompleteProof
    , wrongAssumptionName
    ]
  unless (all id results) exitFailure
