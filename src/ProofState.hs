module ProofState
  ( Env
  , Subgoal(..)
  , ProofState(..)
  , Tactic
  , prove
  ) where

import Syntax
import Axioms (Proof(..))

type Env = [(String, Formula)]

data Subgoal
  = Subgoal
  { assumptions :: Env
  , claim :: Formula
  }

data ProofState
  = ProofState
  { currentGoals :: [Subgoal] -- ^ current subgoals
  , constructProof :: [Proof] -> Proof -- ^ given proofs for the subgoals, construct a proof for the overall goal
  }

type Tactic = ProofState -> ProofState

initialProofState :: Formula -> ProofState
initialProofState goal =
  ProofState
  { currentGoals = [Subgoal { assumptions = [], claim = goal }]
  , constructProof =
      \ps ->
        case ps of
          []  -> error "initialProofState: expected to get at least one proof"
          p:_ -> p
  }

extractProof :: ProofState -> Proof
extractProof state =
  case currentGoals state of
    [] -> constructProof state []
    _  -> error "to extract a proof, there mustn't be open subgoals"

prove :: Formula -> [Tactic] -> Proof
prove goal tactics =
  let
    p = extractProof (foldl (\state tac -> tac state) (initialProofState goal) tactics)
  in
    if getFormula p == goal then
      p
    else
      error
        ("prove: Proved statement differs from goal! " ++
         "Proof shows '" ++ show (getFormula p) ++ "' is true, but the goal was to show that '" ++
         show goal ++ "' is true.")