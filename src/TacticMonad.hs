{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TacticMonad
  ( Env
  , Subgoal(..)
  , ProofState(..)
  , TacticM
  , Tactic
  , prove
  ) where

import Control.Monad.State.Strict

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

newtype TacticM a
  = TacticM
  { runTacticM :: State ProofState a
  } deriving (Functor, Applicative, Monad, MonadState ProofState)

type Tactic = TacticM ()

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
extractProof (ProofState { currentGoals = currGoals, constructProof = constrPrf }) =
  case currGoals of
    [] -> constrPrf []
    _  -> error "to extract a proof, there mustn't be open subgoals"

prove :: Formula -> TacticM a -> Proof
prove goal script =
  let
    p = extractProof (execState (runTacticM script) (initialProofState goal))
  in
    if getFormula p == goal then
      p
    else
      error
        ("prove: Proved statement differs from goal! " ++
         "Proof shows '" ++ show (getFormula p) ++ "' is true, but the goal was to show that '" ++
         show goal ++ "' is true.")