module SetTheoryProver.Core.ProofScript
  ( ProofStep(..)
  , ProofScript
  , prettyPrintProof
  ) where

import SetTheoryProver.Core.Syntax
import SetTheoryProver.Core.Axioms

import Control.Monad (forM_)
import Data.List (foldl')

import System.Console.ANSI

data ProofStep
  = ProofStep
  { proofStepFormula :: Formula
  , proofStepReason :: ValidityReason Int
  }

type ProofScript = [ProofStep]

proofToProofScript :: Proof -> ProofScript
proofToProofScript = snd . go []
  where
    go :: ProofScript -> Proof -> (Int, ProofScript)
    go script proof =
      case filter ((getFormula proof ==) . proofStepFormula . snd) (zip [0..] script) of
        (i, _):_ -> (i, script)
        [] ->
          case reason proof of
            Axiom ->
              let step = ProofStep { proofStepFormula = getFormula proof, proofStepReason = Axiom }
              in (length script, script ++ [step])
            ModusPonens p q ->
              let
                (pIndex, script') = go script p
                (qIndex, script'') = go script' q
                step = ProofStep { proofStepFormula = getFormula proof, proofStepReason = ModusPonens pIndex qIndex }
              in
                (length script'', script'' ++ [step])
            Generalisation x p ->
              let
                (pIndex, script') = go script p
                step = ProofStep { proofStepFormula = getFormula proof, proofStepReason = Generalisation x pIndex }
              in (length script', script' ++ [step])

prettyPrintProofScript :: ProofScript -> IO ()
prettyPrintProofScript script =
  let
    numbers = map show [1..(length script)]
    maxNumberLength = foldl' max 0 (map length numbers)
    paddedNumbers = map (padLeft maxNumberLength) numbers
    reasons = map (prettyReason . proofStepReason) script
    maxReasonLength = foldl' max 0 (map length reasons)
    paddedReasons = map (padRight maxReasonLength) reasons
    formulas = map (show . proofStepFormula) script
  in
    forM_ (zip3 paddedNumbers paddedReasons formulas) $ \(num, reas, formula) -> do
      putStr num
      putStr "  "
      setSGR [SetColor Foreground Vivid Blue]
      putStr reas
      setSGR [Reset]
      putStr "  "
      putStrLn formula
  where
    prettyReason r =
      case r of
        Axiom -> "Ax"
        ModusPonens i j -> "MP " ++ show (i+1) ++ " " ++ show (j+1)
        Generalisation x k -> "Gen '" ++ x ++ "' " ++ show (k+1)
    padLeft n str =
      replicate (max 0 (n - length str)) ' ' ++ str
    padRight n str =
      str ++ replicate (max 0 (n - length str)) ' '

prettyPrintProof :: Proof -> IO ()
prettyPrintProof proof =
  prettyPrintProofScript (proofToProofScript proof)