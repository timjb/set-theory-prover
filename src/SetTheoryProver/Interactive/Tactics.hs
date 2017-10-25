{-# LANGUAGE LambdaCase #-}

module SetTheoryProver.Interactive.Tactics
  ( split
  , left
  , right
  , intro
  , intros
  , assumption
  , exact
  , try
  , refl
  , cases
  , destruct
  , contraposition
  ) where

import SetTheoryProver.Core
import SetTheoryProver.Interactive.TacticMonad
import SetTheoryProver.Interactive.LambdaEmbedding

import Control.Monad (mapM_)
import Control.Monad.Except (catchError)
import Control.Monad.State.Strict hiding (state)

abstract :: Env -> LC -> LC
abstract env term = foldl (flip LCAbs) term env

apply :: LC -> Env -> LC
apply term env = foldr (\(v, _) t -> LCApp t (LCVar v)) term env

liftModusPonens :: Env -> Proof -> [Proof] -> Proof
liftModusPonens asms fun args =
  let
    app = foldl (\t arg -> t :@ apply (LCPrf arg) asms) (LCPrf fun) args
  in
    translate (abstract asms app)

split :: Tactic
split = do
  state <- get
  (asms, phi, psi, otherGoals) <-
    case currentGoals state of
      [] -> fail "split: no goals"
      Subgoal { assumptions = asms, claim = phi :/\: psi } : otherGoals -> pure (asms, phi, psi, otherGoals)
      _:_ -> fail "split: first goal is not of the form 'phi :/\\: psi'"
  put $
    ProofState
    { currentGoals = Subgoal { assumptions = asms, claim = phi } : Subgoal { assumptions = asms, claim = psi } : otherGoals
    , constructProof =
        \case
          phiProof:psiProof:otherProofs ->
            let phiAndPsiProof = liftModusPonens asms (and_intro phi psi) [phiProof, psiProof]
                  --translate $ abstract asms $
                  --  ((LCPrf (and_intro phi psi) `LCApp` apply (LCPrf phiProof) asms) `LCApp` apply (LCPrf psiProof) asms)
            in constructProof state (phiAndPsiProof:otherProofs)
          _ -> error "split: expected to get proofs for two subgoals (corresponding to the two conjuncts)"
    }

left :: Tactic
left = do
  state <- get
  (asms, phi, psi, otherGoals) <-
    case currentGoals state of
      [] -> fail "left: no goals"
      Subgoal { assumptions = asms, claim = phi :\/: psi } : otherGoals -> pure (asms, phi, psi, otherGoals)
      _:_ -> fail "left: first goal is not of the form 'phi :\\/: psi'"
  put $
    ProofState
    { currentGoals = Subgoal { assumptions = asms, claim = phi } : otherGoals
    , constructProof =
        \case
          [] -> error "left: expected to get proof of at least one subgoal (corresponding to the left disjunct)"
          phiProof:otherProofs ->
            let phiOrPsiProof = liftModusPonens asms (or_intro1 phi psi) [phiProof]
                  --translate (abstract asms (LCPrf (or_intro1 phi psi) `LCApp` apply (LCPrf phiProof) asms))
            in constructProof state (phiOrPsiProof:otherProofs)
    }

right :: Tactic
right = do
  state <- get
  (asms, phi, psi, otherGoals) <-
    case currentGoals state of
      [] -> fail "right: no goals"
      Subgoal { assumptions = asms, claim = phi :\/: psi } : otherGoals -> pure (asms, phi, psi, otherGoals)
      _:_ -> fail "right: first goal is not of the form 'phi :\\/: psi'"
  put $
    ProofState
    { currentGoals = Subgoal { assumptions = asms, claim = psi } : otherGoals
    , constructProof =
        \case
          [] -> error "right: expected to get proof of at least one subgoal (corresponding to the right disjunct)"
          psiProof:otherProofs ->
            let phiOrPsiProof = liftModusPonens asms (or_intro2 phi psi) [psiProof]
                  --translate (abstract asms (LCPrf (or_intro2 phi psi) `LCApp` apply (LCPrf phiProof) asms))
            in constructProof state (phiOrPsiProof:otherProofs)
    }

intro :: String -> Tactic
intro name = do
  state <- get
  (asms, phi, psi, otherGoals) <-
    case currentGoals state of
      [] -> fail "intro: no goals"
      Subgoal { assumptions = asms, claim = phi :=>: psi } : otherGoals -> pure (asms, phi, psi, otherGoals)
      _:_ -> fail "intro: first goal is not of the form 'phi :=>: psi'"
  when (name `elem` map fst asms) $
    fail ("intro: name '" ++ name ++ "' already in scope!")
  put $
    state
    { currentGoals = Subgoal { assumptions = (name, phi):asms, claim = psi } : otherGoals
    }

intros :: [String] -> Tactic
intros = mapM_ intro

assumption :: String -> Tactic
assumption name = do
  state <- get
  (asms, formula, otherGoals) <-
    case currentGoals state of
      [] -> fail "assumption: no goals"
      Subgoal { assumptions = asms, claim = formula } : otherGoals -> pure (asms, formula, otherGoals)
  case lookup name asms of
    Nothing -> fail ("assumption: '" ++ name ++ "' is not an assumption!")
    Just formula' ->
      when (formula /= formula') $
        fail ("assumption '" ++ name ++ "' doesn't prove the current goal!")
  put $
    ProofState
    { currentGoals = otherGoals
    , constructProof =
        \subproofs ->
          let proof = translate (abstract asms (LCVar name))
          in constructProof state (proof:subproofs)
    }

exact :: Proof -> Tactic
exact proof = do
  state <- get
  (formula, otherGoals) <-
    case currentGoals state of
      [] -> fail "exact: no goals"
      Subgoal { claim = formula } : otherGoals -> pure (formula, otherGoals)
  when (formula /= getFormula proof) $
    fail "exact: purported proof doesn't prove the first subgoal"
  put $
    ProofState
    { currentGoals = otherGoals
    , constructProof = \subproofs -> constructProof state (proof:subproofs)
    }

try :: TacticM a -> TacticM (Maybe a)
try script =
  catchError (Just <$> script) $ \_exc ->
    -- TODO: log exception
    pure Nothing

refl :: Tactic
refl = do
  state <- get
  case currentGoals state of
    [] -> fail "refl: no goals"
    Subgoal { assumptions = asms, claim = s :=: t } : otherGoals -> do
      when (s /= t) $
        fail "refl: terms not equal!"
      let reflProof = translate (abstract asms (LCPrf (ax8 s)))
      put $
        ProofState
        { currentGoals = otherGoals
        , constructProof = \subproofs -> constructProof state (reflProof:subproofs)
        }
    _:_ -> fail "refl: goal must be of the form 's :=: t'!"

cases :: String -> Tactic
cases name = do
  state <- get
  (Subgoal { assumptions = asms, claim = target }, otherSubgoals) <-
    case currentGoals state of
      [] -> fail "cases: no goals"
      subgoal : otherGoals -> pure (subgoal, otherGoals)
  (phi, psi) <-
    case lookup name asms of
      Nothing -> fail ("cases: '" ++ name ++ "' is not an assumption!")
      Just (phi :\/: psi) -> pure (phi, psi)
      Just _ -> fail ("cases: assumption '" ++ name ++ "' is not of the form 'phi :\\/: psi'!")
  let
    asmsWithPhi = set name phi asms
    asmsWithPsi = set name psi asms
    subgoalWithPhi = Subgoal { assumptions = asmsWithPhi, claim = target }
    subgoalWithPsi = Subgoal { assumptions = asmsWithPsi, claim = target }
  put $
    ProofState
    { currentGoals = subgoalWithPhi : subgoalWithPsi : otherSubgoals
    , constructProof =
        \case
          subgoalProofWithPhi:subgoalProofWithPsi:otherProofs ->
            let
              subgoalProof =
                translate $ abstract asms $
                  LCPrf (or_elim phi psi target)
                    :@ (name ::: phi :-> apply (LCPrf subgoalProofWithPhi) asmsWithPhi)
                    :@ (name ::: psi :-> apply (LCPrf subgoalProofWithPsi) asmsWithPsi)
                    :@ LCVar name
            in constructProof state (subgoalProof:otherProofs)
          _ -> error "cases: expected to get at least two proofs (for the claim, one assuming phi, one assuming psi)"
    }
  where
    set :: Eq k => k -> v -> [(k, v)] -> [(k, v)]
    set key val assocList =
      case assocList of
        [] -> [(key, val)]
        (key1, val1) : rest ->
          if key1 == key then
            (key, val) : rest
          else
            (key1, val1) : set key val rest

destruct :: String -> String -> String -> Tactic
destruct asmName leftAsmName rightAsmName = do
  state <- get
  (Subgoal { assumptions = asms, claim = target }, otherSubgoals) <-
    case currentGoals state of
      [] -> fail "destruct: no goals"
      subgoal : otherGoals -> pure (subgoal, otherGoals)
  (phi, psi) <-
    case lookup asmName asms of
      Nothing -> fail ("cases: '" ++ asmName ++ "' is not an assumption!")
      Just (phi :/\: psi) -> pure (phi, psi)
      Just _ -> fail ("cases: assumption '" ++ asmName ++ "' is not of the form 'phi :/\\: psi'!")
  when (leftAsmName `elem` map fst asms) $
    fail ("destruct: name '" ++ leftAsmName ++ "' already in scope!")
  when (rightAsmName `elem` map fst asms) $
    fail ("destruct: name '" ++ rightAsmName ++ "' already in scope!")
  let
    asms' = (rightAsmName, psi) : (leftAsmName, phi) : asms
  put $
    ProofState
    { currentGoals = Subgoal { assumptions = asms', claim = target } : otherSubgoals
    , constructProof =
        \case
          [] -> error "destruct: expected to get at least one proof!"
          subgoalProof':otherProofs ->
            let
              subgoalProof =
                translate $ abstract asms $
                  apply (LCPrf subgoalProof') asms
                    :@ (LCPrf (and_elim1 phi psi) :@ LCVar asmName)
                    :@ (LCPrf (and_elim2 phi psi) :@ LCVar asmName)
            in
              constructProof state (subgoalProof:otherProofs)
    }

contraposition :: Tactic
contraposition = do
  state <- get
  (asms, phi, psi, otherSubgoals) <-
    case currentGoals state of
      [] -> fail "contraposition: no goals"
      Subgoal { assumptions = asms, claim = phi :=>: psi } : otherSubgoals ->
        pure (asms, phi, psi, otherSubgoals)
      _:_ -> fail "contraposition: goal is not of the form 'phi :=>: psi'"
  put $
    ProofState
    { currentGoals = Subgoal { assumptions = asms, claim = Neg psi :=>: Neg phi } : otherSubgoals
    , constructProof =
        \case
          [] -> error "contraposition: expected to get at least one proof"
          contrapositionProof:otherProofs ->
            let
              implicationProof = translate (abstract asms (LCPrf (ax4 phi psi) :@ apply (LCPrf contrapositionProof) asms))
            in
              constructProof state (implicationProof:otherProofs)
    }

-- TODO: rewrite tactic
-- TODO: tactic for lifting lambda terms
-- TODO: tactic for instantiation of forall
-- TODO: tactic for generalization
-- TODO: tactic for existential introduction
-- TODO: tactic for introducing local lemmas
-- TODO: ex falso tactic