{-# LANGUAGE OverloadedStrings #-}

module SetTheoryProver.Lib.Logic
  (
    -- * Properties of ⇒
    ignoreFirstArg
  , compose
  , flipAssumptions
    -- * Currying
  , curry
  , uncurry
  , currying
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
  , negCharacterisation'
  , negCharacterisation
    -- * Properties of ¬
  , negNegElimination
  , negNegIntroduction
  , contrapositionConverse
    -- * De Morgan's laws
  , deMorgan1a, deMorgan1b, deMorgan1
  , deMorgan2a, deMorgan2b, deMorgan2
    -- * Relation between ⇒ and ∨
  , implicationOr1
  , implicationOr2
  , implicationOr
    -- * Law of Excluded Middle
  , lem
    -- * Properties of =
  , symmetry
  , transitivity
  ) where

import Prelude hiding (repeat, curry, uncurry)

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

-- | Schema '(φ ∧ ψ ⇒ ξ) ⇒ φ ⇒ ψ ⇒ ξ'
--
-- >>> checkProof (curry phi psi xi)
curry :: Formula -> Formula -> Formula -> Proof
curry phi psi xi =
  prove ((phi :/\: psi :=>: xi) :=>: phi :=>: psi :=>: xi) $ do
    intros ["uncurried", "phi", "psi"]
    apply "uncurried"
    split
    assumption "phi"
    assumption "psi"

-- | Schema '(φ ⇒ ψ ⇒ ξ) ⇒ φ ∧ ψ ⇒ ξ'
--
-- >>> checkProof (uncurry phi psi xi)
uncurry :: Formula -> Formula -> Formula -> Proof
uncurry phi psi xi =
  prove ((phi :=>: psi :=>: xi) :=>: phi :/\: psi :=>: xi) $ do
    intros ["curriedFn", "phiAndPsi"]
    destruct "phiAndPsi" "phi" "psi"
    have "psiImpliesXi" (psi :=>: xi) by $ do
      apply "curriedFn"
      assumption "phi"
    apply "psiImpliesXi"
    assumption "psi"

currying :: Formula -> Formula -> Formula -> Proof
currying phi psi xi =
  prove ((phi :/\: psi :=>: xi) `iff` (phi :=>: psi :=>: xi)) $ do
    split
    exact (curry phi psi xi)
    exact (uncurry phi psi xi)

-- | Schema 'φ ∨ ψ ⇒ ψ ∨ φ'
--
-- >>> checkProof (orCommutative phi psi)
orCommutative :: Formula -> Formula -> Proof
orCommutative phi psi =
  prove (phi :\/: psi :=>: psi :\/: phi) $ do
    intro "phiOrPsi"
    cases "phiOrPsi" "phi" "psi"
    right >> assumption "phi"
    left  >> assumption "psi"

-- | Schema 'φ ∨ (ψ ∨ ξ) ⇔ (φ ∨ ψ) ∨ ξ'
--
-- >>> checkProof (orAssociative phi psi xi)
orAssociative :: Formula -> Formula -> Formula -> Proof
orAssociative phi psi xi =
  prove ((phi :\/: (psi :\/: xi)) `iff` ((phi :\/: psi) :\/: xi)) $ do
    split
    -- =>
    intro "phiOrPsiOrXi"
    cases "phiOrPsiOrXi" "phi" "psiOrXi"
    left >> left >> assumption "phi"
    cases "psiOrXi" "psi" "xi"
    left >> right >> assumption "psi"
    right >> assumption "xi"
    -- <=
    intro "phiOrPsiOrXi"
    cases "phiOrPsiOrXi" "phiOrPsi" "xi"
    cases "phiOrPsi" "phi" "psi"
    left >> assumption "phi"
    right >> left >> assumption "psi"
    right >> right >> assumption "xi"

-- | Schema 'φ ∨ ⊥ ⇔ φ'
--
-- >>> checkProof (orFalsity phi)
orFalsity :: Formula -> Proof
orFalsity phi =
  prove ((phi :\/: falsity) `iff` phi) $ do
    split
    -- =>
    intro "phiOrFalsity"
    cases "phiOrFalsity" "phi" "falsity"
    assumption "phi"
    applyProof (exFalso phi) >> assumption "falsity"
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
    intro "phiAndPsiOrXi"
    destruct "phiAndPsiOrXi" "phi" "psiOrXi"
    cases "psiOrXi" "psi" "xi"
    left  >> split >> assumption "phi" >> assumption "psi"
    right >> split >> assumption "phi" >> assumption "xi"
    -- <=
    intro "h"
    cases "h" "phiAndPsi" "phiAndXi"
    -- first case
    destruct "phiAndPsi" "phi" "psi"
    split
    assumption "phi"
    left
    assumption "psi"
    -- second case
    destruct "phiAndXi" "phi" "xi"
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
    intro "phiOrPsiAndXi"
    cases "phiOrPsiAndXi" "phi" "psiAndXi"
    -- first case
    split >> repeat_ (left >> assumption "phi")
    -- second case
    destruct "psiAndXi" "psi" "xi"
    split
    repeat_ (right >> someAssumption)
    -- <=
    intro "h"
    destruct "h" "phiOrPsi" "phiOrXi"
    cases "phiOrPsi" "phi" "psi"
    -- first case
    left >> assumption "phi"
    -- second case
    cases "phiOrXi" "phi" "xi"
    -- first subcase (of second case)
    left >> assumption "phi"
    -- second subcase (of second case)
    right
    split
    assumption "psi"
    assumption "xi"

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
    suffices "truthImpliesPhi" (truth :=>: phi) by $ do
      apply "truthImpliesPhi"
      exact truthIsTrue
    contraposition
    applyProof (contradiction (Neg phi))
    assumption "negNegPhi"

-- | Schema 'φ ⇒ ¬¬φ'
--
-- >>> checkProof (negNegIntroduction phi)
negNegIntroduction :: Formula -> Proof
negNegIntroduction phi =
  prove (phi :=>: Neg (Neg phi)) $ do
    contraposition
    exact (negNegElimination (Neg phi))

-- | Schema '(φ ⇒ ⊥) ⇒ ¬φ'
--
-- >>> checkProof (negCharacterisation' phi)
negCharacterisation' :: Formula -> Proof
negCharacterisation' phi =
  prove ((phi :=>: falsity) :=>: Neg phi) $ do
    intro "notPhi'"
    suffices "truthImpliesNegPhi" (truth :=>: Neg phi) by $ do
      apply "truthImpliesNegPhi"
      exact truthIsTrue
    contraposition
    intro "negNegPhi"
    apply "notPhi'"
    applyProof (negNegElimination phi)
    someAssumption

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
    exact (negCharacterisation' phi)

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

--assumeTheContrary :: Tactic
--assumeTheContrary = do
--  Subgoal { claim = target } <- getSubgoal

-- | Schema '¬(φ ∧ ψ) ⇒ ¬φ ∨ ¬ψ'
--
-- >>> checkProof (deMorgan1a phi psi)
deMorgan1a :: Formula -> Formula -> Proof
deMorgan1a phi psi =
  prove (Neg (phi :/\: psi) :=>: Neg phi :\/: Neg psi) $ do
    contraposition
    intro "negNegPhiOrNegPsi"
    have "negNegPhiAndNegNegPsi" (Neg (Neg phi) :/\: Neg (Neg psi)) by $
      exact (LCPrf (deMorgan2a (Neg phi) (Neg psi)) :@ "negNegPhiOrNegPsi")
    destruct "negNegPhiAndNegNegPsi" "negNegPhi" "negNegPsi"
    applyProof (negNegIntroduction (phi :/\: psi))
    split
    exact (LCPrf (negNegElimination phi) :@ "negNegPhi")
    exact (LCPrf (negNegElimination psi) :@ "negNegPsi")

-- | Schema '¬φ ∨ ¬ψ ⇒ ¬(φ ∧ ψ)'
--
-- >>> checkProof (deMorgan1b phi psi)
deMorgan1b :: Formula -> Formula -> Proof
deMorgan1b phi psi =
  prove (Neg phi :\/: Neg psi :=>: Neg (phi :/\: psi)) $ do
    intro "negPhiOrNegPsi"
    applyProof (negCharacterisation' (phi :/\: psi))
    intro "phiAndPsi"
    destruct "phiAndPsi" "phi" "psi" >> clear "phiAndPsi"
    cases "negPhiOrNegPsi" "negPhi" "negPsi"
    exact (LCPrf (contradiction phi) :@ "negPhi" :@ "phi")
    exact (LCPrf (contradiction psi) :@ "negPsi" :@ "psi")

-- | Schema '¬(φ ∧ ψ) ⇔ ¬φ ∨ ¬ψ'
--
-- >>> checkProof (deMorgan1 phi psi)
deMorgan1 :: Formula -> Formula -> Proof
deMorgan1 phi psi =
  prove (Neg (phi :/\: psi) `iff` (Neg phi :\/: Neg psi)) $ do
    split
    exact (deMorgan1a phi psi)
    exact (deMorgan1b phi psi)

-- | Schema '¬(φ ∨ ψ) ⇒ ¬φ ∧ ¬ψ'
--
-- >>> checkProof (deMorgan2a phi psi)
deMorgan2a :: Formula -> Formula -> Proof
deMorgan2a phi psi =
  prove (Neg (phi :\/: psi) :=>: Neg phi :/\: Neg psi) $ do
    intro "negPhiOrPsi"
    split
    -- left conjunct
    applyProof (negCharacterisation' phi)
    intro "phi"
    apply (LCPrf (contradiction (phi :\/: psi)) :@ "negPhiOrPsi")
    left
    assumption "phi"
    -- right conjunct
    applyProof (negCharacterisation' psi)
    intro "psi"
    apply (LCPrf (contradiction (phi :\/: psi)) :@ "negPhiOrPsi")
    right
    assumption "psi"

-- | Schema '¬(φ ∨ ψ) ⇒ ¬φ ∧ ¬ψ'
--
-- >>> checkProof (deMorgan2b phi psi)
deMorgan2b :: Formula -> Formula -> Proof
deMorgan2b phi psi =
  prove (Neg phi :/\: Neg psi :=>: Neg (phi :\/: psi)) $ do
    intro "negPhiAndNegPsi"
    destruct "negPhiAndNegPsi" "negPhi" "negPsi"
    applyProof (negCharacterisation' (phi :\/: psi))
    intro "phiOrPsi"
    cases "phiOrPsi" "phi" "psi"
    exact (LCPrf (contradiction phi) :@ "negPhi" :@ "phi")
    exact (LCPrf (contradiction psi) :@ "negPsi" :@ "psi")

-- | Schema '¬(φ ∨ ψ) ⇔ ¬φ ∧ ¬ψ'
--
-- >>> checkProof (deMorgan2 phi psi)
deMorgan2 :: Formula -> Formula -> Proof
deMorgan2 phi psi =
  prove (Neg (phi :\/: psi) `iff` (Neg phi :/\: Neg psi)) $ do
    split
    exact (deMorgan2a phi psi)
    exact (deMorgan2b phi psi)

-- | Schema '(φ ⇒ ψ) ⇒ ¬φ ∨ ψ'
--
-- >>> checkProof (implicationOr1 phi psi)
implicationOr1 :: Formula -> Formula -> Proof
implicationOr1 phi psi =
  prove ((phi :=>: psi) :=>: Neg phi :\/: psi) $ do
    intro "phiImpliesPsi"
    have "phiOrNegPhi" (phi :\/: Neg phi) from (lem phi)
    cases "phiOrNegPhi" "phi" "negPhi"
    right >> apply "phiImpliesPsi" >> assumption "phi"
    left >> assumption "negPhi"

-- | Schema '¬φ ∨ ψ ⇒ φ ⇒ ψ'
--
-- >>> checkProof (implicationOr2 phi psi)
implicationOr2 :: Formula -> Formula -> Proof
implicationOr2 phi psi =
  prove (Neg phi :\/: psi :=>: phi :=>: psi) $ do
    intros ["negPhiOrPsi", "phi"]
    cases "negPhiOrPsi" "negPhi" "psi"
    -- first case
    applyProof (exFalso psi)
    exact (LCPrf (contradiction phi) :@ "negPhi" :@ "phi")
    -- second case
    assumption "psi"

-- | Schema '(φ ⇒ ψ) ⇔ ¬φ ∨ ψ'
--
-- >>> checkProof (implicationOr phi psi)
implicationOr :: Formula -> Formula -> Proof
implicationOr phi psi =
  prove ((phi :=>: psi) `iff` (Neg phi :\/: psi)) $ do
    split
    exact (implicationOr1 phi psi)
    exact (implicationOr2 phi psi)

-- | Schema 'φ ∨ ¬φ'
--
-- >>> checkProof (lem phi)
lem :: Formula -> Proof
lem phi =
  prove (phi :\/: Neg phi) $ do
    applyProof (negNegElimination (phi :\/: Neg phi))
    -- from here on, the proof is constructive
    applyProof (negCharacterisation' (Neg (phi :\/: Neg phi)))
    intro "negPhiOrNegPhi"
    suffices "phiOrNegPhi" (phi :\/: Neg phi) by $
      exact (LCPrf (contradiction (phi :\/: Neg phi)) :@ "negPhiOrNegPhi" :@ "phiOrNegPhi")
    right
    applyProof (negCharacterisation' phi)
    intro "phi"
    have "phiOrNegPhi" (phi :\/: Neg phi) by (left >> assumption "phi")
    exact (LCPrf (contradiction (phi :\/: Neg phi)) :@ "negPhiOrNegPhi" :@ "phiOrNegPhi")

-- | Schema 's = t ⇒ t = s'
--
-- >>> checkProof (symmetry (Var "x") (Var "y"))
symmetry :: Term -> Term -> Proof
symmetry s t =
  prove (s :=: t :=>: t :=: s) $ do
    intro "s=t"
    transport "s=t" (\z -> z :=: s)
    refl

-- | Schema 's = t ⇒ t = u ⇒ s = u'
--
-- >>> checkProof (transitivity (Var "x") (Var "y") (Var "z"))
transitivity :: Term -> Term -> Term -> Proof
transitivity s t u =
  prove (s :=: t :=>: t :=: u :=>: s :=: u) $ do
    intro "s=t"
    intro "t=u"
    transport "t=u" (\r -> s :=: r)
    assumption "s=t"