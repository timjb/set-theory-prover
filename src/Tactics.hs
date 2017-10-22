module Tactics
  ( split
  , left
  , intro
  , assumption
  , exact
  ) where

import Syntax
import Axioms
import ProofState
import LambdaEmbedding

import GHC.Stack

abstract :: Env -> LC -> LC
abstract env term = foldl (\t (name, formula) -> LCAbs name formula t) term env

apply :: LC -> Env -> LC
apply term env = foldr (\(v, _) t -> LCApp t (LCVar v)) term env

liftModusPonens :: Env -> Proof -> [Proof] -> Proof
liftModusPonens asms fun args =
  let
    app = foldl (\t arg -> LCApp t (apply (LCPrf arg) asms)) (LCPrf fun) args
  in
    translate (abstract asms app)

split :: HasCallStack => Tactic
split state =
  case currentGoals state of
    [] -> error "split: no goals"
    (Subgoal { assumptions = asms, claim = phi `And` psi }):otherGoals ->
      ProofState
      { currentGoals = Subgoal { assumptions = asms, claim = phi } : Subgoal { assumptions = asms, claim = psi } : otherGoals
      , constructProof =
          \subproofs ->
            case subproofs of
              phiProof:psiProof:otherProofs ->
                let phiAndPsiProof = liftModusPonens asms (and_intro phi psi) [phiProof, psiProof]
                      --translate $ abstract asms $
                      --  ((LCPrf (and_intro phi psi) `LCApp` apply (LCPrf phiProof) asms) `LCApp` apply (LCPrf psiProof) asms)
                in constructProof state (phiAndPsiProof:otherProofs)
              _ -> error "split: expected to get proofs for two subgoals (corresponding to the two conjuncts)"
      }
    _ -> error "split: first goal is not of the form φ ∧ ψ"

left :: HasCallStack => Tactic
left state =
  case currentGoals state of
    [] -> error "left: no goals"
    (Subgoal { assumptions = asms, claim = phi `Or` psi }):otherGoals ->
      ProofState
      { currentGoals = (Subgoal { assumptions = asms, claim = phi }):otherGoals
      , constructProof =
          \subproofs ->
            case subproofs of
              [] -> error "left: expected to get proof of at least one subgoal (corresponding to the left disjunct)"
              phiProof:otherProofs ->
                let phiOrPsiProof = liftModusPonens asms (or_intro1 phi psi) [phiProof]
                      --translate (abstract asms (LCPrf (or_intro1 phi psi) `LCApp` apply (LCPrf phiProof) asms))
                in constructProof state (phiOrPsiProof:otherProofs)
      }
    _ -> error "split: first goal is not of the form φ ∨ ψ"

-- TODO: right

intro :: HasCallStack => String -> Tactic
intro name state =
  case currentGoals state of
    [] -> error "intro: no goals"
    (Subgoal { assumptions = asms, claim = phi `Implies` psi }):otherGoals ->
      if name `elem` map fst asms then error ("intro: name '" ++ name ++ "' already in scope!") else
      state
      { currentGoals = (Subgoal { assumptions = (name, phi):asms, claim = psi }):otherGoals
      }
    _ -> error "intro: first goal is not of the form φ ⇒ ψ"

assumption :: HasCallStack => String -> Tactic
assumption name state =
  case currentGoals state of
    [] -> error "assumption: no goals"
    (Subgoal { assumptions = asms, claim = formula }):otherGoals ->
      case lookup name asms of
        Nothing -> error ("assumption: '" ++ name ++ "' is not an assumption!")
        Just formula' | formula' /= formula -> error ("assumption '" ++ name ++ "' doesn't prove the current goal!")
        Just _ ->
          ProofState
          { currentGoals = otherGoals
          , constructProof =
              \subproofs ->
                let proof = translate (abstract asms (LCVar name))
                in constructProof state (proof:subproofs)
          }

exact :: HasCallStack => Proof -> Tactic
exact proof state =
  case currentGoals state of
    [] -> error "exact: no goals"
    (Subgoal { claim = firstGoal }):otherGoals ->
      if firstGoal /= getFormula proof
        then error "exact: purported proof doesn't prove the first subgoal"
        else
          ProofState
          { currentGoals = otherGoals
          , constructProof = \subproofs -> constructProof state (proof:subproofs)
          }

-- TODO: tactic for local lemmas