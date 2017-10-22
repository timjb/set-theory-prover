module Consequences
  (
  -- * Consequences of the axioms
    ignoreFirstArg
  , compose
  ) where

import Syntax
import Axioms
import LambdaEmbedding

-- | Schema 'ψ ⇒ φ ⇒ φ'
ignoreFirstArg :: Formula -> Formula -> Proof
ignoreFirstArg phi psi = translate (LCAbs "x" psi (LCAbs "y" phi (LCVar "y")))
  --let
  --  step1 = ax2 (phi `Implies` phi) psi -- (φ ⇒ φ) ⇒ ψ ⇒ φ ⇒ φ
  --  step2 = ax1 phi                     -- φ ⇒ φ
  --  step3 = step1 `mp` step2            -- ψ ⇒ φ ⇒ φ
  --in
  --  step3

-- | Schema '(ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ)'
compose :: Formula -> Formula -> Formula -> Proof
compose phi psi xi =
  translate $
    LCAbs "f" (psi `Implies` xi) $
      LCAbs "g" (phi `Implies` psi) $
        LCAbs "x" phi $
          LCVar "f" `LCApp` (LCVar "g" `LCApp` LCVar "x")