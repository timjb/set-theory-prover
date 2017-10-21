module Tactics
  ( split
  , left
  , exact
  ) where

import Syntax
import Axioms
import ProofState

split :: Tactic
split state =
  case currentGoals state of
    [] -> error "split: no goals"
    (phi `And` psi):otherGoals ->
      ProofState
      { currentGoals = phi:psi:otherGoals
      , constructProof =
          \subproofs ->
            case subproofs of
              phiProof:psiProof:otherProofs ->
                let phiAndPsiProof = ((and_intro phi psi) `mp` phiProof) `mp` psiProof
                in constructProof state (phiAndPsiProof:otherProofs)
              _ -> error "split: expected to get proofs for two subgoals (corresponding to the two conjuncts)"
      }
    _ -> error "split: first goal is not of the form φ ∧ ψ"

left :: Tactic
left state =
  case currentGoals state of
    [] -> error "left: no goals"
    (phi `Or` psi):otherGoals ->
      ProofState
      { currentGoals = phi:otherGoals
      , constructProof =
          \subproofs ->
            case subproofs of
              [] -> error "left: expected to get proof of at least one subgoal (corresponding to the left disjunct)"
              phiProof:otherProofs ->
                let phiOrPsiProof = (or_intro1 phi psi) `mp` phiProof
                in constructProof state (phiOrPsiProof:otherProofs)
      }
    _ -> error "split: first goal is not of the form φ ∨ ψ"

-- TODO: right

exact :: Proof -> Tactic
exact proof state =
  case currentGoals state of
    [] -> error "exact: no goals"
    firstGoal:_otherGoals ->
      if firstGoal /= getFormula proof
        then error "exact: purported proof doesn't prove the first subgoal"
        else
          ProofState
          { currentGoals = currentGoals state
          , constructProof = \subproofs -> constructProof state (proof:subproofs)
          }

-- TODO: intro