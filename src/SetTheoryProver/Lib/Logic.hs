{-# LANGUAGE OverloadedStrings #-}

module SetTheoryProver.Lib.Logic
  (
    -- * Consequences of the axioms
    ignoreFirstArg
  , compose
  , flipAssumptions
    -- * Monoid structure of ∨
  , orCommutative
  , orAssociative
  , orFalsity
    -- * Monoid structure of ∧
  , andCommutative
  , andAssociative
  , andTruth
    -- * Distributivity of ∨ and ∧
  , andDistributesOverOr
  , orDistributesOverAnd
    -- * Properties of ⊤
  , truthIsTrue
    -- * Properties of ⊥
  , exFalso
    -- * Properties relating ⊥ and ¬
  , contradiction
  , negCharacterisation
    -- * Properties of ¬
  , negNegElimination
  , negNegIntroduction
  , contrapositionConverse
  ) where

import Prelude hiding (repeat)

import SetTheoryProver.Core
import SetTheoryProver.Interactive

-- $setup
-- >>> let phi = Var "x" :€: Var "s"
-- >>> let psi = Var "y" :€: Var "s"
-- >>> let xi  = Var "z" :€: Var "s"

-- | Schema 'ψ ⇒ φ ⇒ φ'
--
-- >>> checkProofOf (psi :=>: phi :=>: phi) (ignoreFirstArg phi psi)
ignoreFirstArg :: Formula -> Formula -> Proof
ignoreFirstArg phi psi =
  translate ("x" ::: psi :-> "y" ::: phi :-> "y")
  --let
  --  step1 = ax2 (phi `Implies` phi) psi -- (φ ⇒ φ) ⇒ ψ ⇒ φ ⇒ φ
  --  step2 = ax1 phi                     -- φ ⇒ φ
  --  step3 = step1 `mp` step2            -- ψ ⇒ φ ⇒ φ
  --in
  --  step3

-- | Schema '(ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ)'
--
-- >>> checkProofOf ((psi :=>: xi) :=>: (phi :=>: psi) :=>: phi :=>: xi) (compose phi psi xi)
compose :: Formula -> Formula -> Formula -> Proof
compose phi psi xi =
  translate $
    "f" ::: (psi :=>: xi) :->
      "g" ::: (phi :=>: psi) :->
        "x" ::: phi :->
          "f" :@ ("g" :@ "x")

-- | Proof of 'truth'
--
-- >>> checkProofOf truth truthIsTrue
truthIsTrue :: Proof
truthIsTrue = generalise "x" (ax8 "x")

-- | Schema '(φ ⇒ ψ ⇒ ξ) ⇒ ψ ⇒ φ ⇒ ξ'
--
-- >>> checkProofOf ((phi :=>: psi :=>: xi) :=>: psi :=>: phi :=>: xi) (flipAssumptions phi psi xi)
flipAssumptions :: Formula -> Formula -> Formula -> Proof
flipAssumptions phi psi xi =
  translate $
    "f" ::: (phi :=>: psi :=>: xi) :->
      "psi" ::: psi :->
        "phi" ::: phi :->
          "f" :@ "phi" :@ "psi"

-- | Schema 'φ ∨ ψ ⇒ ψ ∨ φ'
--
-- >>> checkProof (orCommutative phi psi)
orCommutative :: Formula -> Formula -> Proof
orCommutative phi psi =
  prove (phi :\/: psi :=>: psi :\/: phi) $ do
    intro "h"
    cases "h"
    right >> assumption "h"
    left  >> assumption "h"

-- | Schema 'φ ∨ (ψ ∨ ξ) ⇔ (φ ∨ ψ) ∨ ξ'
--
-- >>> checkProof (orAssociative phi psi xi)
orAssociative :: Formula -> Formula -> Formula -> Proof
orAssociative phi psi xi =
  prove ((phi :\/: (psi :\/: xi)) `iff` ((phi :\/: psi) :\/: xi)) $ do
    split
    -- =>
    intro "h"
    cases "h"
    left >> left >> assumption "h"
    cases "h"
    left >> right >> assumption "h"
    right >> assumption "h"
    -- <=
    intro "h"
    cases "h"
    cases "h"
    left >> assumption "h"
    right >> left >> assumption "h"
    right >> right >> assumption "h"

-- | Schema 'φ ∨ ⊥ ⇔ φ'
--
-- >>> checkProof (orFalsity phi)
orFalsity :: Formula -> Proof
orFalsity phi =
  prove ((phi :\/: falsity) `iff` phi) $ do
    split
    -- =>
    intro "h"
    cases "h"
    assumption "h"
    applyProof (exFalso phi) >> assumption "h"
    -- <=
    intro "phi"
    left
    assumption "phi"

-- | Schema 'φ ∧ ψ ⇒ ψ ∧ φ'
--
-- >>> checkProof (andCommutative phi psi)
andCommutative :: Formula -> Formula -> Proof
andCommutative phi psi =
  prove (phi :/\: psi :=>: psi :/\: phi) $ do
    intro "phiAndPsi"
    destruct "phiAndPsi" "phi" "psi"
    split
    assumption "psi"
    assumption "phi"

-- | Schema 'φ ∧ (ψ ∧ ξ) ⇔ (φ ∧ ψ) ∧ ξ'
--
-- >>> checkProof (andAssociative phi psi xi)
andAssociative :: Formula -> Formula -> Formula -> Proof
andAssociative phi psi xi =
  prove ((phi :/\: (psi :/\: xi)) `iff` ((phi :/\: psi) :/\: xi)) $ do
    split
    -- =>
    intro "h"
    destruct "h" "phi" "psiAndXi"
    destruct "psiAndXi" "psi" "xi"
    split
    split >> assumption "phi" >> assumption "psi"
    assumption "xi"
    -- <=
    intro "h"
    destruct "h" "phiAndPsi" "xi"
    destruct "phiAndPsi" "phi" "psi"
    split
    assumption "phi"
    split >> assumption "psi" >> assumption "xi"

-- | Schema 'φ ∧ ⊤ ⇔ φ'
--
-- >>> checkProof (andTruth phi)
andTruth :: Formula -> Proof
andTruth phi =
  prove ((phi :/\: truth) `iff` phi) $ do
    split
    -- =>
    intro "phiAndTruth"
    destruct "phiAndTruth" "phi" "_"
    assumption "phi"
    -- <=
    intro "phi"
    split
    assumption "phi"
    exact truthIsTrue

-- | Schema 'φ ∧ (ψ ∨ ξ) ⇔ (φ ∧ ψ) ∨ (φ ∧ ξ)'
--
-- >>> checkProof (andDistributesOverOr phi psi xi)
andDistributesOverOr :: Formula -> Formula -> Formula -> Proof
andDistributesOverOr phi psi xi =
  prove ((phi :/\: (psi :\/: xi)) `iff` ((phi :/\: psi) :\/: (phi :/\: xi))) $ do
    split
    -- =>
    intro "h"
    destruct "h" "phi" "psiOrXi"
    cases "psiOrXi"
    left  >> split >> assumption "phi" >> assumption "psiOrXi"
    right >> split >> assumption "phi" >> assumption "psiOrXi"
    -- <=
    intro "h"
    cases "h"
    -- first case
    destruct "h" "phi" "psi"
    split
    assumption "phi"
    left
    assumption "psi"
    -- second case
    destruct "h" "phi" "xi"
    split
    assumption "phi"
    right
    assumption "xi"

-- | Schema 'φ ∨ (ψ ∧ ξ) ⇔ (φ ∨ ψ) ∧ (φ ∨ ξ)'
--
-- >>> checkProof (orDistributesOverAnd phi psi xi)
orDistributesOverAnd :: Formula -> Formula -> Formula -> Proof
orDistributesOverAnd phi psi xi =
  prove ((phi :\/: (psi :/\: xi)) `iff` ((phi :\/: psi) :/\: (phi :\/: xi))) $ do
    split
    -- =>
    intro "h"
    cases "h"
    -- first case
    split >> repeat_ (left >> assumption "h")
    -- second case
    destruct "h" "psi" "xi"
    split
    right >> assumption "psi"
    right >> assumption "xi"
    -- <=
    intro "h"
    destruct "h" "phiOrPsi" "phiOrXi"
    cases "phiOrPsi"
    left >> assumption "phiOrPsi"
    cases "phiOrXi"
    left >> assumption "phiOrXi"
    right
    split
    assumption "phiOrPsi"
    assumption "phiOrXi"

-- | Schema '¬φ ⇒ φ ⇒ ⊥'
--
-- >>> checkProof (contradiction phi)
contradiction :: Formula -> Proof
contradiction phi =
  prove (Neg phi :=>: phi :=>: falsity) $ do
    intro "notPhi"
    contraposition
    intro "_"
    assumption "notPhi"

-- | Schema '¬¬φ ⇒ φ'
--
-- >>> checkProof (negNegElimination phi)
negNegElimination :: Formula -> Proof
negNegElimination phi =
  prove (Neg (Neg phi) :=>: phi) $ do
    intro "negNegPhi"
    have "truthImpliesPhi" (truth :=>: phi) by $ do
      contraposition
      applyProof (contradiction (Neg phi))
      assumption "negNegPhi"
    exact ("truthImpliesPhi" :@ LCPrf truthIsTrue)

-- | Schema 'φ ⇒ ¬¬φ'
--
-- >>> checkProof (negNegIntroduction phi)
negNegIntroduction :: Formula -> Proof
negNegIntroduction phi =
  prove (phi :=>: Neg (Neg phi)) $ do
    contraposition
    exact (negNegElimination (Neg phi))

-- | Schema '¬φ ⇔ (φ ⇒ ⊥)'
--
-- >>> checkProof (negCharacterisation phi)
negCharacterisation :: Formula -> Proof
negCharacterisation phi =
  prove (Neg phi `iff` (phi :=>: falsity)) $ do
    split
    -- =>
    exact (contradiction phi)
    -- <=
    intro "notPhi'"
    have "truthImpliesNegPhi" (truth :=>: Neg phi) by $ do
      contraposition
      intro "negNegPhi"
      apply "notPhi'"
      applyProof (negNegElimination phi)
      assumption "negNegPhi"
    exact ("truthImpliesNegPhi" :@ LCPrf truthIsTrue)

-- | Schema '(φ ⇒ ψ) ⇒ ¬ψ ⇒ ¬φ'
--
-- >>> checkProof (contrapositionConverse phi psi)
contrapositionConverse :: Formula -> Formula -> Proof
contrapositionConverse phi psi =
  prove ((phi :=>: psi) :=>: Neg psi :=>: Neg phi) $ do
    intro "phiImpliesPsi"
    contraposition
    intro "negNegPhi"
    applyProof (negNegIntroduction psi)
    apply "phiImpliesPsi"
    applyProof (negNegElimination phi)
    assumption "negNegPhi"

-- | Schema '⊥ ⇒ φ'
--
-- >>> checkProof (exFalso phi)
exFalso :: Formula -> Proof
exFalso phi =
  prove (falsity :=>: phi) $ do
    contraposition
    intro "_"
    applyProof (negNegIntroduction truth)
    exact truthIsTrue

-- TODO: LEM
-- TODO: De Morgan Laws