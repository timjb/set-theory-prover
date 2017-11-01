{-# LANGUAGE OverloadedStrings #-}

module SetTheoryProver.Lib.SetTheory
  (
    -- * The subset relation
    subsetReflexivity
  , subsetTransitivity
  , subsetAntisymmetry
  ) where

import SetTheoryProver.Core
import SetTheoryProver.Interactive

-- $setup
-- >>> let s = Var "s"
-- >>> let t = Var "t"
-- >>> let u = Var "u"

-- | Every set is a subset of itself
--
-- >>> checkProof (subsetReflexivity s)
subsetReflexivity :: Term -> Proof
subsetReflexivity s =
  prove (s `subset` s) $ do
    generalising
    intro "h"
    assumption "h"

-- | The "is subset of" relation is transitive
--
-- >>> checkProof (subsetTransitivity s t u)
subsetTransitivity :: Term -> Term -> Term -> Proof
subsetTransitivity s t u =
  prove ((s `subset` t) :=>: (t `subset` u) :=>: (s `subset` u)) $ do
    intros ["s_subset_t", "t_subset_u"]
    generalising
    intro "elem_s"
    instantiate "t_subset_u" "x1" >>= apply
    instantiate "s_subset_t" "x1" >>= apply
    assumption "elem_s"

-- | The "is subset of" relation is anti-symmetric
--
-- >>> checkProof (subsetAntisymmetry s t)
subsetAntisymmetry :: Term -> Term -> Proof
subsetAntisymmetry s t =
  prove ((s `subset` t) :=>: (t `subset` s) :=>: s :=: t) $ do
    ext1 <- instantiate (LCPrf extensionalityAxiom) s
    ext2 <- instantiate ext1 t
    exact ext2

-- TODO:
-- * x `cap` y subset x
-- * x `cap` y subset y
-- * leere Menge ist Teilmenge einer jeden Menge
-- * Schnitt ist kommutativ, assoziativ
-- * Vereinigung ist kommutativ, assoziativ
-- * Distributivgesetz(e) von Schnitt und Vereinigung
-- * x ist Teilmenge von x Vereinigung y
-- * y ist Teilmenge von x Vereinigung y