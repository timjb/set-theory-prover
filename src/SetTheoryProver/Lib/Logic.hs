{-# LANGUAGE OverloadedStrings #-}

module SetTheoryProver.Lib.Logic
  (
    -- * Consequences of the axioms
    ignoreFirstArg
  , compose
  , flipAssumptions
  , contradiction
  , truthIsTrue
  , negNegElimination
  , negNegIntroduction
  , negCharacterisation
  , contrapositionConverse
  , exFalso
  ) where

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
  translate ("x" ::: psi :-> "y" ::: phi :-> LCVar "y")
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
          LCVar "f" :@ (LCVar "g" :@ LCVar "x")

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
          LCVar "f" :@ LCVar "phi" :@ LCVar "psi"

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
    have "contradiction" (Neg (Neg phi) :=>: Neg phi :=>: falsity)
    exact (contradiction (Neg phi))
    have "truthImpliesPhi" (truth :=>: phi)
    contraposition
    apply "contradiction"
    assumption "negNegPhi"
    apply "truthImpliesPhi"
    exact truthIsTrue

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
    have "truthImpliesNegPhi" (truth :=>: Neg phi)
    contraposition
    intro "negNegPhi"
    apply "notPhi'"
    have "negNegPhiImpliesPhi" (Neg (Neg phi) :=>: phi)
    exact (negNegElimination phi)
    apply "negNegPhiImpliesPhi"
    assumption "negNegPhi"
    apply "truthImpliesNegPhi"
    exact truthIsTrue

-- | Schema '(φ ⇒ ψ) ⇒ ¬ψ ⇒ ¬φ'
--
-- >>> checkProof (contrapositionConverse phi psi)
contrapositionConverse :: Formula -> Formula -> Proof
contrapositionConverse phi psi =
  prove ((phi :=>: psi) :=>: Neg psi :=>: Neg phi) $ do
    intro "phiImpliesPsi"
    contraposition
    intro "negNegPhi"
    have "psiImpliesNegNegPsi" (psi :=>: Neg (Neg psi)) >> exact (negNegIntroduction psi)
    have "negNegPhiImpliesPhi" (Neg (Neg phi) :=>: phi) >> exact (negNegElimination phi)
    apply "psiImpliesNegNegPsi"
    apply "phiImpliesPsi"
    apply "negNegPhiImpliesPhi"
    assumption "negNegPhi"

-- | Schema '⊥ ⇒ φ'
--
-- >>> checkProof (exFalso phi)
exFalso :: Formula -> Proof
exFalso phi =
  prove (falsity :=>: phi) $ do
    contraposition
    intro "_"
    have "truthImpliesNegFalsity" (truth :=>: Neg falsity) >> exact (negNegIntroduction truth)
    apply "truthImpliesNegFalsity"
    exact truthIsTrue
