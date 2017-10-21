module ProofState
  ( Goal
  , ProofState(..)
  , Tactic
  , prove
  ) where

import Syntax
import Axioms (Proof(..))

type Goal = Formula

data ProofState
  = ProofState
  { currentGoals :: [Goal] -- ^ current subgoals
  , constructProof :: [Proof] -> Proof -- ^ given proofs for the subgoals, construct a proof for the overall goal
  }

type Tactic = ProofState -> ProofState

initialProofState :: Formula -> ProofState
initialProofState goal =
  ProofState
  { currentGoals = [goal]
  , constructProof =
      \ps ->
        case ps of
          []  -> error "initialProofState: expected to get at least one proof"
          p:_ -> p
  }

extractProof :: ProofState -> Proof
extractProof state =
  case currentGoals state of
    [] -> error "to extract a proof, there mustn't be open subgoals"
    _  -> constructProof state []

prove :: Formula -> [Tactic] -> Proof
prove goal tactics =
  let p = extractProof (foldl (\state tac -> tac state) (initialProofState goal) tactics)
  in if getFormula p == goal
       then p
       else error "prove: proved statement differs from goal!"