{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SetTheoryProver.Interactive.TacticMonad
  ( Env
  , Subgoal(..)
  , ProofState(..)
  , TacticException(..)
  , TacticM
  , Tactic
  , prove'
  , prove
  ) where

import SetTheoryProver.Core.Syntax
import SetTheoryProver.Core.Axioms (Proof(..))

import Control.Monad.State.Strict
import Control.Monad.Except

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
  , proofLog :: [String] -- ^ log messages
  }

newtype TacticException
  = TacticException
  { errorMsg :: String
  }

newtype TacticM a
  = TacticM
  { runTacticM :: StateT ProofState (Except TacticException) a
  } deriving (Functor, Applicative, MonadState ProofState, MonadError TacticException)

instance Monad TacticM where
  return = pure
  x >>= f = TacticM (runTacticM x >>= runTacticM . f)
  fail msg = throwError (TacticException { errorMsg = msg })

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
  , proofLog = []
  }

extractProof :: ProofState -> Except TacticException Proof
extractProof (ProofState { currentGoals = currGoals, constructProof = constrPrf }) =
  case currGoals of
    [] -> pure (constrPrf [])
    _  -> throwError (TacticException "to extract a proof, there mustn't be open subgoals")

prove' :: Formula -> TacticM a -> Either TacticException Proof
prove' goal script =
  runExcept $ do
    proofState <- execStateT (runTacticM script) (initialProofState goal)
    proof <- extractProof proofState
    unless (getFormula proof == goal) $
      throwError $ TacticException $
        "Proved statement differs from goal! " ++
        "Proof shows '" ++ show (getFormula proof) ++ "' is true, but the goal was to show that '" ++
        show goal ++ "' is true."
    pure proof

prove :: Formula -> TacticM a -> Proof
prove goal script =
  case prove' goal script of
    Left exc  -> error (errorMsg exc)
    Right prf -> prf