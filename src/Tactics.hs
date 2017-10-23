{-# LANGUAGE LambdaCase #-}

module Tactics
  ( split
  , left
  , intro
  , assumption
  , exact
  ) where

import Syntax
import Axioms
import TacticMonad
import LambdaEmbedding

import Control.Monad.State.Strict hiding (state)

abstract :: Env -> LC -> LC
abstract env term = foldl (flip LCAbs) term env

apply :: LC -> Env -> LC
apply term env = foldr (\(v, _) t -> LCApp t (LCVar v)) term env

liftModusPonens :: Env -> Proof -> [Proof] -> Proof
liftModusPonens asms fun args =
  let
    app = foldl (\t arg -> t :@ apply (LCPrf arg) asms) (LCPrf fun) args
  in
    translate (abstract asms app)

split :: Tactic
split = do
  state <- get
  (asms, phi, psi, otherGoals) <-
    case currentGoals state of
      [] -> fail "split: no goals"
      (Subgoal { assumptions = asms, claim = phi :/\: psi }):otherGoals -> pure (asms, phi, psi, otherGoals)
      _:_ -> fail "split: first goal is not of the form φ ∧ ψ"
  put $
    ProofState
    { currentGoals = Subgoal { assumptions = asms, claim = phi } : Subgoal { assumptions = asms, claim = psi } : otherGoals
    , constructProof =
        \case
          phiProof:psiProof:otherProofs ->
            let phiAndPsiProof = liftModusPonens asms (and_intro phi psi) [phiProof, psiProof]
                  --translate $ abstract asms $
                  --  ((LCPrf (and_intro phi psi) `LCApp` apply (LCPrf phiProof) asms) `LCApp` apply (LCPrf psiProof) asms)
            in constructProof state (phiAndPsiProof:otherProofs)
          _ -> error "split: expected to get proofs for two subgoals (corresponding to the two conjuncts)"
    }

left :: Tactic
left = do
  state <- get
  (asms, phi, psi, otherGoals) <-
    case currentGoals state of
      [] -> fail "left: no goals"
      (Subgoal { assumptions = asms, claim = phi `Or` psi }):otherGoals -> pure (asms, phi, psi, otherGoals)
      _:_ -> fail "left: first goal is not of the form φ ∨ ψ"
  put $
    ProofState
    { currentGoals = (Subgoal { assumptions = asms, claim = phi }):otherGoals
    , constructProof =
        \case
          [] -> error "left: expected to get proof of at least one subgoal (corresponding to the left disjunct)"
          phiProof:otherProofs ->
            let phiOrPsiProof = liftModusPonens asms (or_intro1 phi psi) [phiProof]
                  --translate (abstract asms (LCPrf (or_intro1 phi psi) `LCApp` apply (LCPrf phiProof) asms))
            in constructProof state (phiOrPsiProof:otherProofs)
    }

-- TODO: right

intro :: String -> Tactic
intro name = do
  state <- get
  (asms, phi, psi, otherGoals) <-
    case currentGoals state of
      [] -> fail "intro: no goals"
      (Subgoal { assumptions = asms, claim = phi `Implies` psi }):otherGoals -> pure (asms, phi, psi, otherGoals)
      _:_ -> fail "intro: first goal is not of the form φ ⇒ ψ"
  when (name `elem` map fst asms) $
    fail ("intro: name '" ++ name ++ "' already in scope!")
  put $
    state
    { currentGoals = (Subgoal { assumptions = (name, phi):asms, claim = psi }):otherGoals
    }

assumption :: String -> Tactic
assumption name = do
  state <- get
  (asms, formula, otherGoals) <-
    case currentGoals state of
      [] -> fail "assumption: no goals"
      (Subgoal { assumptions = asms, claim = formula }):otherGoals -> pure (asms, formula, otherGoals)
  case lookup name asms of
    Nothing -> fail ("assumption: '" ++ name ++ "' is not an assumption!")
    Just formula' ->
      when (formula /= formula') $
        fail ("assumption '" ++ name ++ "' doesn't prove the current goal!")
  put $
    ProofState
    { currentGoals = otherGoals
    , constructProof =
        \subproofs ->
          let proof = translate (abstract asms (LCVar name))
          in constructProof state (proof:subproofs)
    }

exact :: Proof -> Tactic
exact proof = do
  state <- get
  (formula, otherGoals) <-
    case currentGoals state of
      [] -> fail "exact: no goals"
      (Subgoal { claim = formula }):otherGoals -> pure (formula, otherGoals)
  when (formula /= getFormula proof) $
    fail "exact: purported proof doesn't prove the first subgoal"
  put $
    ProofState
    { currentGoals = otherGoals
    , constructProof = \subproofs -> constructProof state (proof:subproofs)
    }

-- TODO: try tactic
-- TODO: intros tactic
-- TODO: tactic for local lemmas