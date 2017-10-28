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
  , interactive
  ) where

import SetTheoryProver.Core.Syntax
import SetTheoryProver.Core.Axioms (Proof(..))
import SetTheoryProver.Interactive.LambdaEmbedding

import Control.Monad.State.Strict
import Control.Monad.Except

import System.Console.ANSI

type Env = [(String, Formula)]

data Subgoal
  = Subgoal
  { assumptions :: Env
  , claim :: Formula
  } deriving (Eq)

data ProofState
  = ProofState
  { currentGoals :: [Subgoal] -- ^ current subgoals
  , constructProof :: [LC] -> LC -- ^ given proofs for the subgoals, construct a proof for the overall goal
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
    [] -> pure (translate (constrPrf []))
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

printSubgoal :: Subgoal -> IO ()
printSubgoal (Subgoal { assumptions = asms, claim = target }) = do
  let
    nameColWidth    = foldl max 1 (map (length . fst) asms)
    colGap          = "  "
    formulaColWidth = foldl max 6 (map (length . show . snd) asms)
    totalWidth      = max (length (show target)) (nameColWidth + length colGap + formulaColWidth)
  forM_ (reverse asms) $ \(name, formula) -> do
    setSGR [SetColor Foreground Vivid Blue]
    putStr (padLeft nameColWidth name)
    setSGR [Reset]
    putStr colGap
    putStrLn (show formula)
  putStrLn (replicate totalWidth '-')
  putStrLn (show target)
  where
    padLeft n str = replicate (max 0 (n - length str)) ' ' ++ str

interactive :: Formula -> TacticM a -> IO (Maybe a)
interactive goal script = do
  case runExcept (runStateT (runTacticM script) (initialProofState goal)) of
    Left (TacticException msg) -> do
      outputErrorMsg msg
      pure Nothing
    Right (res, proofState) -> do
      unless (null (proofLog proofState)) $ do
        forM_ (proofLog proofState) $ \msg -> do
          setSGR [SetColor Foreground Vivid Blue]
          putStrLn msg
          setSGR [Reset]
        putStrLn ""
      case currentGoals proofState of
        [] -> do
          let
            proof = translate (constructProof proofState [])
          unless (getFormula proof == goal) $
            outputErrorMsg $ unlines
              [ "Proved statement differs from goal! Proof shows that"
              , "  " ++ show (getFormula proof)
              , "is true, but the goal was to show that"
              , "  " ++ show goal
              , "is true."
              ]
        [subgoal] -> do
          putStrLn "Finished with one open subgoal:\n"
          printSubgoal subgoal
        subgoal:_:_ -> do
          putStrLn ("Finished with " ++ show (length (currentGoals proofState)) ++ " open subgoals, the first of which is\n")
          printSubgoal subgoal
      pure (Just res)
  where
    outputErrorMsg msg = do
      setSGR [SetColor Foreground Vivid Red]
      mapM_ putStrLn (zipWith (++) ("✘ " : repeat "  ") (lines msg))
      setSGR [Reset]