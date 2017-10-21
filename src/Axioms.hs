module Axioms
  (
  -- * Proof data type
    Proof(getFormula)
  -- * Proof Rules
  , mp
  , generalise
  -- * Axioms for a Hilbert-style deductive system
  -- ** Axioms for ⇒
  , ax1
  , ax2
  , ax3
  -- ** Axiom for ¬
  , ax4
  -- ** Axioms for ∀
  , ax5
  , ax6
  , ax7
  -- ** Axioms for =
  , ax8
  , ax9
  -- ** Axioms for ∧
  , and_intro
  , and_elim1
  , and_elim2
  -- ** Axioms for ∨
  , or_intro1
  , or_intro2
  , or_elim
  -- ** Axioms for ∃ and ∀
  , exists_elim
  -- * ZFC axioms
  , extensionalityAxiom
  , regularityAxiom
  , separationAxiom
  , pairingAxiom
  , unionAxiom
  , replacementAxiom
  , infinityAxiom
  , powersetAxiom
  , choiceAxiom
  ) where

import Syntax

newtype Proof = Proof { getFormula :: Formula }

-- | Modus Ponens
mp :: Proof -> Proof -> Proof
mp (Proof p) (Proof q) =
  case p of
    Implies precedent consequent ->
      if precedent == q
        then Proof consequent
        else error "mp: The second argument of 'mp' must be equal to the precedent of the first argument!"
    _ -> error "mp: The first argument to 'mp' must be the proof of an implication!"

-- | Generalisation
generalise :: VarName -> Proof -> Proof
generalise x (Proof phi) = Proof (Forall x phi)

-- | Axiom schema 'φ ⇒ φ'
--
-- This is implemented using 'ax2' and 'ax3', showing that this axiom is not strictly necessary.
ax1 :: Formula -> Proof
ax1 phi =
  let
    step1 = ax2 phi (phi `Implies` phi)     -- φ ⇒ (φ ⇒ φ) ⇒ φ
    step2 = ax3 phi (phi `Implies` phi) phi -- (φ ⇒ (φ ⇒ φ) ⇒ φ) ⇒ (φ ⇒ φ ⇒ φ) ⇒ φ
    step3 = mp step2 step1                  -- (φ ⇒ φ ⇒ φ) ⇒ φ
    step4 = ax2 phi phi                     -- φ ⇒ φ ⇒ φ
    step5 = mp step3 step4                  -- φ
  in
    step5

-- | Axiom schema 'φ ⇒ ψ ⇒ φ'
ax2 :: Formula -> Formula -> Proof
ax2 phi psi = Proof (phi `Implies` (psi `Implies` phi))

-- | Axiom schema '(φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ)'
ax3 :: Formula -> Formula -> Formula -> Proof
ax3 phi psi xi = Proof (antecedent `Implies` consequent)
  where
    antecedent = Implies phi (Implies psi xi)
    consequent = Implies (Implies phi psi) (Implies phi xi)

-- | Axiom schema '(¬φ ⇒ ¬ψ) ⇒ ψ ⇒ φ
ax4 :: Formula -> Formula -> Proof
ax4 phi psi = Proof (antecedent `Implies` consequent)
  where
    antecedent = Implies (Neg phi) (Neg psi)
    consequent = Implies psi phi

-- | Axiom schema '(∀x. φ) ⇒ φ[x := t]'
ax5 :: VarName -> Term -> Formula -> Proof
ax5 x s phi = Proof (antecedent `Implies` consequent)
  where
    antecedent = Forall x phi
    consequent = replaceInFormula x s phi

-- TODO: According to wikipedia this isn't strictly needed. Is this right? In that case, derive it.
-- | Axiom schema '(∀x. φ ⇒ ψ) ⇒ (∀x. φ) ⇒ (∀x. ψ)'
ax6 :: VarName -> Formula -> Formula -> Proof
ax6 x phi psi = Proof (antecedent `Implies` consequent)
  where
    antecedent = Forall x (Implies phi psi)
    consequent = Implies (Forall x phi) (Forall x psi)

-- TODO: According to wikipedia this isn't strictly needed. Is this right? In that case, derive it.
-- | Axiom schema 'φ ⇒ (∀x. φ)' if x is not free in φ
ax7 :: Formula -> VarName -> Proof
ax7 phi x =
  if x `elem` fvInFormula phi
    then error "ax7: variable must not occur freely in formula!"
    else Proof (Implies phi (Forall x phi))

-- | Axiom schema 't = t' (reflexivity)
ax8 :: Term -> Proof
ax8 t = Proof (Eq t t)

-- | Axiom schema 's = t ⇒ φ[x := s] ⇒ φ[x := t]' (transport)
ax9 :: Term -> Term -> VarName -> Formula -> Proof
ax9 s t x phi = Proof (antecedent `Implies` consequent)
  where
    antecedent = Eq s t
    consequent = Implies (replaceInFormula x s phi) (replaceInFormula x t phi)

-- | Axiom schema 'φ ⇒ (ψ ⇒ φ ∧ ψ)'
and_intro :: Formula -> Formula -> Proof
and_intro phi psi = Proof (Implies phi (Implies psi (And phi psi)))

-- | Axiom schema 'φ ∧ ψ ⇒ φ'
and_elim1 :: Formula -> Formula -> Proof
and_elim1 phi psi = Proof (Implies (And phi psi) phi)

-- | Axiom schema 'φ ∧ ψ ⇒ ψ'
and_elim2 :: Formula -> Formula -> Proof
and_elim2 phi psi = Proof (Implies (And phi psi) psi)

-- | Axiom schema '(φ ⇒ ξ) ⇒ (ψ ⇒ ξ) ⇒ (φ ∨ ψ ⇒ ξ)'
or_elim :: Formula -> Formula -> Formula -> Proof
or_elim phi psi xi = Proof (Implies (Implies phi xi) (Implies (Implies psi xi) (Implies (Or phi psi) xi)))

-- | Axiom schema 'φ ⇒ φ ∨ ψ'
or_intro1 :: Formula -> Formula -> Proof
or_intro1 phi psi = Proof (Implies phi (Or phi psi))

-- | Axiom schema 'ψ ⇒ φ ∨ ψ'
or_intro2 :: Formula -> Formula -> Proof
or_intro2 phi psi = Proof (Implies psi (Or phi psi))

-- | Axiom schema '(∀x. φ ⇒ ψ) ⇒ (∃x. φ) ⇒ ψ'
exists_elim :: VarName -> Formula -> Formula -> Proof
exists_elim x phi psi =
  if x `elem` fvInFormula psi
    then error "exists_elim: variable must not occur freely in second formula"
    else Proof (Implies precedent consequent)
  where
    precedent = Forall x (Implies phi psi)
    consequent = Implies (Exists x phi) psi

-- ZFC axioms
-- (source: https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory)

extensionalityAxiom :: Proof
extensionalityAxiom = Proof (Forall x (Forall y (antecedent `Implies` consequent)))
  where
    antecedent = And (subset (Var x) (Var y)) (subset (Var y) (Var x))
    consequent = Eq (Var x) (Var y)
    x = "x"
    y = "y"

regularityAxiom :: Proof
regularityAxiom = Proof (Forall x (antecedent `Implies` consequent))
  where
    antecedent = Exists y (Elem (Var y) (Var x))
    consequent = existsIn y (Var x) (Neg (existsIn z (Var y) (Elem (Var z) (Var x))))
    x = "x"
    y = "y"
    z = "z"

-- TODO: do we have to check that x /= z?
separationAxiom :: VarName -> VarName -> Formula -> Proof
separationAxiom x z phi =
  let y = freshVar (fvInFormula phi `varUnion` [x,z])
  in Proof (Forall z (Exists y (Forall x ((Var x `Elem` Var y) `iff` ((Var x `Elem` Var z) `And` phi)))))

pairingAxiom :: Proof
pairingAxiom = Proof (Forall x (Forall y (Exists z ((Var x `Elem` Var z) `And` (Var y `Elem` Var z)))))
  where
    x = "x"
    y = "y"
    z = "z"

unionAxiom :: Proof
unionAxiom = Proof (Forall x (Exists y (forallIn v (Var x) (forallIn u (Var v) (Var u `Elem` Var x)))))
  where
    x = "x"
    y = "y"
    u = "u"
    v = "v"

-- TODO: do we have to check that x y a are pairwise different?
replacementAxiom :: VarName -> VarName -> VarName -> Formula -> Proof
replacementAxiom x y a phi =
  let b = freshVar (fvInFormula phi)
      antecedent = forallIn x (Var a) (existsUnique y phi)
      consequent = Exists b (forallIn x (Var a) (existsIn y (Var b) phi))
  in Proof (antecedent `Implies` consequent)

successor :: Term -> Term
successor x = pairSet x (singletonSet x)

infinityAxiom :: Proof
infinityAxiom = Proof (Exists x ((emptySet `Elem` Var x) `And` forallIn y (Var x) (successor (Var y) `Elem` Var x)))
  where
    x = "x"
    y = "y"

powersetAxiom :: Proof
powersetAxiom = Proof (Forall x (Exists y (Forall z ((Var z `Elem` Var y) `iff` (Var z `subset` Var x)))))
  where
    x = "x"
    y = "y"
    z = "z"

-- TODO: axiom of choice
choiceAxiom :: Proof
choiceAxiom = Proof (Forall z (Implies precedent consequent))
  where
    precondition1 = forallIn x (Var z) (Exists y (Var y `Elem` Var x))
    precondition2 = forallIn x1 (Var z) (forallIn x2 (Var z) (Neg (existsIn y (Var x1) (Var y `Elem` Var x2))))
    precedent = precondition1 `And` precondition2
    consequent = Exists w (forallIn x (Var z) (existsUniqueIn y (Var w) (Var y `Elem` Var x)))
    x = "x"
    x1 = "x1"
    x2 = "x2"
    y = "y"
    z = "z"
    w = "w"