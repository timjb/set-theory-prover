module SetTheoryProver.Core.Axioms
  (
  -- * Proof data type
    Proof(getFormula, reason)
  , ValidityReason(..)
  , checkProof
  , checkProofOf
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
  , andIntro
  , andElimLeft
  , andElimRight
  -- ** Axioms for ∨
  , orIntroLeft
  , orIntroRight
  , orElim
  -- ** Axioms for ∃ and ∀
  , existsIntro
  , existsElim
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

import SetTheoryProver.Core.Syntax

import Control.Monad (when)

import Control.DeepSeq

data Proof = Proof { getFormula :: Formula, reason :: ValidityReason Proof }

data ValidityReason p
  = ModusPonens p p
  | Generalisation VarName p
  | Axiom

axiom :: Formula -> Proof
axiom formula = Proof { getFormula = formula, reason = Axiom }

checkProof :: Proof -> IO ()
checkProof p =
  getFormula p `deepseq` pure ()

checkProofOf :: Formula -> Proof -> IO ()
checkProofOf goal proof =
  when (goal /= getFormula proof) $
    fail "checkProof: goal does not match proofed statement!"

-- | Modus Ponens
mp :: Proof -> Proof -> Proof
mp p q =
  case getFormula p of
    precedent :=>: consequent ->
      if precedent /= getFormula q then
        error
          ("mp: The second argument '" ++ show (getFormula q) ++
           "' of 'mp' must be equal to the precedent '" ++ show precedent ++
           "' of the first argument!")
      else
        Proof { getFormula = consequent, reason = ModusPonens p q }
    _ -> error "mp: The first argument to 'mp' must be the proof of an implication!"

-- | Generalisation
generalise :: VarName -> Proof -> Proof
generalise x p = Proof { getFormula = Forall x (getFormula p), reason = Generalisation x p }

-- | Axiom schema 'φ ⇒ φ'
--
-- This is implemented using 'ax2' and 'ax3', showing that this axiom is not strictly necessary.
ax1 :: Formula -> Proof
ax1 phi =
  let
    step1 = ax2 phi (phi :=>: phi)     -- φ ⇒ (φ ⇒ φ) ⇒ φ
    step2 = ax3 phi (phi :=>: phi) phi -- (φ ⇒ (φ ⇒ φ) ⇒ φ) ⇒ (φ ⇒ φ ⇒ φ) ⇒ (φ ⇒ φ)
    step3 = mp step2 step1             -- (φ ⇒ φ ⇒ φ) ⇒ (φ ⇒ φ)
    step4 = ax2 phi phi                -- φ ⇒ φ ⇒ φ
    step5 = mp step3 step4             -- φ ⇒ φ
  in
    step5

-- | Axiom schema 'φ ⇒ ψ ⇒ φ'
ax2 :: Formula -> Formula -> Proof
ax2 phi psi = axiom (phi :=>: psi :=>: phi)

-- | Axiom schema '(φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ)'
ax3 :: Formula -> Formula -> Formula -> Proof
ax3 phi psi xi = axiom ((phi :=>: psi :=>: xi) :=>: (phi :=>: psi) :=>: (phi :=>: xi))

-- | Axiom schema '(¬ψ ⇒ ¬φ) ⇒ φ ⇒ ψ'
ax4 :: Formula -> Formula -> Proof
ax4 phi psi = axiom ((Neg psi :=>: Neg phi) :=>: phi :=>: psi)

-- | Axiom schema '(∀x. φ) ⇒ φ[x := t]'
ax5 :: VarName -> Term -> Formula -> Proof
ax5 x s phi = axiom (Forall x phi :=>: replaceInFormula x s phi)

-- TODO: According to wikipedia this isn't strictly needed. Is this right? In that case, derive it.
-- | Axiom schema '(∀x. φ ⇒ ψ) ⇒ (∀x. φ) ⇒ (∀x. ψ)'
ax6 :: VarName -> Formula -> Formula -> Proof
ax6 x phi psi = axiom (antecedent :=>: consequent)
  where
    antecedent = Forall x (phi :=>: psi)
    consequent = Forall x phi :=>: Forall x psi

-- TODO: According to wikipedia this isn't strictly needed. Is this right? In that case, derive it.
-- | Axiom schema 'φ ⇒ (∀x. φ)' if x is not free in φ
ax7 :: VarName -> Formula -> Proof
ax7 x phi =
  if x `elem` fvInFormula phi then
    error "ax7: variable must not occur freely in formula!"
  else
    axiom (phi :=>: Forall x phi)

-- | Axiom schema 't = t' (reflexivity)
ax8 :: Term -> Proof
ax8 t = axiom (t :=: t)

-- | Axiom schema 's = t ⇒ φ[x := s] ⇒ φ[x := t]' (transport)
ax9 :: Term -> Term -> VarName -> Formula -> Proof
ax9 s t x phi = axiom (antecedent :=>: consequent)
  where
    antecedent = s :=: t
    consequent = replaceInFormula x s phi :=>: replaceInFormula x t phi

-- | Axiom schema 'φ ⇒ (ψ ⇒ φ ∧ ψ)'
andIntro :: Formula -> Formula -> Proof
andIntro phi psi = axiom (phi :=>: psi :=>: phi :/\: psi)

-- | Axiom schema 'φ ∧ ψ ⇒ φ'
andElimLeft :: Formula -> Formula -> Proof
andElimLeft phi psi = axiom (phi :/\: psi :=>: phi)

-- | Axiom schema 'φ ∧ ψ ⇒ ψ'
andElimRight :: Formula -> Formula -> Proof
andElimRight phi psi = axiom (phi :/\: psi :=>: psi)

-- | Axiom schema '(φ ⇒ ξ) ⇒ (ψ ⇒ ξ) ⇒ (φ ∨ ψ ⇒ ξ)'
orElim :: Formula -> Formula -> Formula -> Proof
orElim phi psi xi = axiom ((phi :=>: xi) :=>: (psi :=>: xi) :=>: phi :\/: psi :=>: xi)

-- | Axiom schema 'φ ⇒ φ ∨ ψ'
orIntroLeft :: Formula -> Formula -> Proof
orIntroLeft phi psi = axiom (phi :=>: phi :\/: psi)

-- | Axiom schema 'ψ ⇒ φ ∨ ψ'
orIntroRight :: Formula -> Formula -> Proof
orIntroRight phi psi = axiom (psi :=>: phi :\/: psi)

-- | Axiom schema 'φ ⇒ ∃y. φ[x := y]' if y is not free in φ
existsIntro :: VarName -> VarName -> Formula -> Proof
existsIntro x y phi =
  if y `elem` fvInFormula phi then
    error "existsIntro: variable capture!"
  else
    axiom (phi :=>: Exists y (replaceInFormula x (Var y) phi))

-- | Axiom schema '(∀x. φ ⇒ ψ) ⇒ (∃x. φ) ⇒ ψ' if x is not free in ψ
existsElim :: VarName -> Formula -> Formula -> Proof
existsElim x phi psi =
  if x `elem` fvInFormula psi then
    error "existsElim: variable must not occur freely in second formula"
  else
    axiom (Forall x (phi :=>: psi) :=>: (Exists x phi) :=>: psi)

-- ZFC axioms
-- (source: https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory)

extensionalityAxiom :: Proof
extensionalityAxiom = axiom (Forall x (Forall y (subset (Var x) (Var y) :=>: subset (Var y) (Var x) :=>: Var x :=: Var y)))
  where
    x = "x"
    y = "y"

regularityAxiom :: Proof
regularityAxiom = axiom (Forall x (antecedent :=>: consequent))
  where
    antecedent = Exists y (Var y :€: Var x)
    consequent = existsIn y (Var x) (Neg (existsIn z (Var y) (Var z :€: Var x)))
    x = "x"
    y = "y"
    z = "z"

-- TODO: do we have to check that x /= z?
separationAxiom :: VarName -> VarName -> Formula -> Proof
separationAxiom x z phi =
  let y = freshVar (fvInFormula phi `varUnion` [x,z])
  in axiom (Forall z (Exists y (Forall x (Var x :€: Var y :<=>: (Var x :€: Var z) :/\: phi))))

pairingAxiom :: Proof
pairingAxiom = axiom (Forall x (Forall y (Exists z ((Var x :€: Var z) :/\: (Var y :€: Var z)))))
  where
    x = "x"
    y = "y"
    z = "z"

unionAxiom :: Proof
unionAxiom = axiom (Forall x (Exists y (forallIn v (Var x) (forallIn u (Var v) (Var u :€: Var x)))))
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
  in axiom (antecedent :=>: consequent)

successor :: Term -> Term
successor x = pairSet x (singletonSet x)

infinityAxiom :: Proof
infinityAxiom = axiom (Exists x ((emptySet :€: Var x) :/\: forallIn y (Var x) (successor (Var y) :€: Var x)))
  where
    x = "x"
    y = "y"

powersetAxiom :: Proof
powersetAxiom = axiom (Forall x (Exists y (Forall z (Var z :€: Var y :<=>: Var z `subset` Var x))))
  where
    x = "x"
    y = "y"
    z = "z"

-- TODO: axiom of choice
choiceAxiom :: Proof
choiceAxiom = axiom (Forall z (precedent :=>: consequent))
  where
    precondition1 = forallIn x (Var z) (Exists y (Var y :€: Var x))
    precondition2 = forallIn x1 (Var z) (forallIn x2 (Var z) (Neg (existsIn y (Var x1) (Var y :€: Var x2))))
    precedent = precondition1 :/\: precondition2
    consequent = Exists w (forallIn x (Var z) (existsUniqueIn y (Var w) (Var y :€: Var x)))
    x = "x"
    x1 = "x1"
    x2 = "x2"
    y = "y"
    z = "z"
    w = "w"