{-# LANGUAGE LambdaCase #-}

module SetTheoryProver.Interactive.Tactics
  ( logMsg
  , try
  , repeat
  , repeat_
  , getSubgoals
  , getSubgoal
  , getAssumptions
  , clear
  , split
  , left
  , right
  , intro
  , intros
  , assumption
  , someAssumption
  , exact
  , refl
  , cases
  , destruct
  , contraposition
  , introAssumption
  , have
  , suffices
  , by, from
  , apply
  , applyProof
  , focus
  , generalising
  , transport
  ) where

import Prelude hiding (repeat)

import SetTheoryProver.Core
import SetTheoryProver.Interactive.TacticMonad
import SetTheoryProver.Interactive.LambdaEmbedding

import Control.Monad (mapM_, void)
import Control.Monad.Except (catchError)
import Control.Monad.State.Strict hiding (state)

logMsg :: String -> Tactic
logMsg msg = modify $ \state -> state { proofLog = msg : proofLog state }

try :: TacticM a -> TacticM (Maybe a)
try script =
  catchError (Just <$> script) $ \exc -> do
    logMsg ("tried tactic failed with msg: " ++ errorMsg exc)
    pure Nothing

-- | Repeats a tactic until it fails, returning a list of results.
repeat :: TacticM a -> TacticM [a]
repeat tactic = go []
  where
    go results =
      catchError (Right <$> tactic) (pure . Left) >>= \case
        Left exc -> do
          logMsg ("repeat: tactic failed after " ++ show (length results) ++ " invocations with message: " ++ errorMsg exc)
          pure (reverse results)
        Right result ->
          go (result : results)

-- | Repeats a tactic until it fails.
repeat_ :: Tactic -> Tactic
repeat_ tactic = void (repeat tactic)

getSubgoals :: TacticM [Subgoal]
getSubgoals = gets currentGoals

-- >>> embedding "abc" "bacha"
-- Right [1,0,2]
--
-- >>> embedding "ax" "abc"
-- Left 'x'
embedding :: Eq a => [a] -> [a] -> Either a [Int]
embedding xs ys =
  forM xs $ \x ->
    case lookup x ysWithIndex of
      Nothing -> Left x
      Just i  -> Right i
  where
    ysWithIndex = zip ys [0..]

setSubgoals :: [Subgoal] -> Tactic
setSubgoals subgoals' = do
  state <- get
  emb <-
    case embedding (currentGoals state) subgoals' of
      Left subgoal -> fail ("setSubgoals: current subgoal with claim " ++ show (claim subgoal) ++ " is not among the new subgoals")
      Right emb -> pure emb
  put $
    state
    { currentGoals = subgoals'
    , constructProof =
        \subproofs ->
          if length subproofs < length subgoals' then
            error "setSubgoals: received too few subproofs!"
          else
            constructProof state (map (subproofs !!) emb)
    }

getSubgoal :: TacticM Subgoal
getSubgoal = do
  subgoals <- getSubgoals
  case subgoals of
    [] -> fail "getSubgoal: no subgoals"
    subgoal:_ -> pure subgoal

getAssumptions :: TacticM Env
getAssumptions = assumptions <$> getSubgoal

-- | Drops an assumption
clear :: String -> Tactic
clear name = do
  state <- get
  (currentSubgoal, otherSubgoals) <-
    case currentGoals state of
      [] -> fail "clear: no goals"
      currentSubgoal:otherSubgoals -> pure (currentSubgoal, otherSubgoals)
  let currentSubgoal' = currentSubgoal { assumptions = filter ((/= name) . fst) (assumptions currentSubgoal) }
  put $ state { currentGoals = currentSubgoal':otherSubgoals }

split :: Tactic
split = do
  state <- get
  (asms, phi, psi, otherGoals) <-
    case currentGoals state of
      [] -> fail "split: no goals"
      Subgoal { assumptions = asms, claim = phi :/\: psi } : otherGoals -> pure (asms, phi, psi, otherGoals)
      _:_ -> fail "split: first goal is not of the form 'phi :/\\: psi'"
  put $
    state
    { currentGoals = Subgoal { assumptions = asms, claim = phi } : Subgoal { assumptions = asms, claim = psi } : otherGoals
    , constructProof =
        \case
          phiProof:psiProof:otherProofs ->
            let phiAndPsiProof = LCPrf (and_intro phi psi) :@ phiProof :@ psiProof
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
    state
    { currentGoals = Subgoal { assumptions = asms, claim = phi } : otherGoals
    , constructProof =
        \case
          [] -> error "left: expected to get proof of at least one subgoal (corresponding to the left disjunct)"
          phiProof:otherProofs ->
            let phiOrPsiProof = LCPrf (or_intro1 phi psi) :@ phiProof
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
    state
    { currentGoals = Subgoal { assumptions = asms, claim = psi } : otherGoals
    , constructProof =
        \case
          [] -> error "right: expected to get proof of at least one subgoal (corresponding to the right disjunct)"
          psiProof:otherProofs ->
            let phiOrPsiProof = LCPrf (or_intro2 phi psi) :@ psiProof
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
    , constructProof =
        \case
          [] -> error "intro: expected to get proof of at least subgoal (of conclusion given assumption)"
          psiProof:otherProofs ->
            let phiImpliesPsiProof = name ::: phi :-> psiProof
            in constructProof state (phiImpliesPsiProof:otherProofs)
    }

intros :: [String] -> Tactic
intros = mapM_ intro

assumption :: String -> Tactic
assumption name = do
  state <- get
  (asms, formula) <-
    case currentGoals state of
      [] -> fail "assumption: no goals"
      Subgoal { assumptions = asms, claim = formula } : _ -> pure (asms, formula)
  case lookup name asms of
    Nothing -> fail ("assumption: '" ++ name ++ "' is not an assumption!")
    Just formula' ->
      when (formula /= formula') $
        fail ("assumption '" ++ name ++ "' doesn't prove the current goal!")
  exact (LCVar name)

someAssumption :: Tactic
someAssumption = do
  subgoal <- getSubgoal
  asms <- getAssumptions
  case lookup (claim subgoal) (map (\(a,b) -> (b,a)) asms) of
    Nothing -> fail "someAssumption: no assumption matching goal!"
    Just asmName -> assumption asmName

exact :: ToLC a => a -> Tactic
exact proofLike = do
  state <- get
  (Subgoal { assumptions = asms, claim = formula }, otherGoals) <-
    case currentGoals state of
      [] -> fail "exact: no goals"
      subgoal : otherGoals -> pure (subgoal, otherGoals)
  let lambdaTerm = toLC proofLike
  proofedFormula <-
    case inferType asms lambdaTerm of
      Left err -> fail ("exact: failed to infer type of given term. Reason: '" ++ err ++ "'")
      Right inferred -> pure inferred
  when (formula /= proofedFormula) $
    fail ("exact: term does not prove the first subgoal, instead it proves '" ++ show proofedFormula ++ "'")
  put $
    state
    { currentGoals = otherGoals
    , constructProof =
        \subproofs -> constructProof state (lambdaTerm : subproofs)
    }

refl :: Tactic
refl = do
  state <- get
  case currentGoals state of
    [] -> fail "refl: no goals"
    Subgoal { claim = s :=: t } : otherGoals -> do
      when (s /= t) $
        fail "refl: terms not equal!"
      let reflProof = LCPrf (ax8 s)
      put $
        state
        { currentGoals = otherGoals
        , constructProof = \subproofs -> constructProof state (reflProof:subproofs)
        }
    _:_ -> fail "refl: goal must be of the form 's :=: t'!"

cases :: String -> String -> String -> Tactic
cases nameDisjunction nameLeftDisjunct nameRightDisjunct = do
  state <- get
  (Subgoal { assumptions = asms, claim = target }, otherSubgoals) <-
    case currentGoals state of
      [] -> fail "cases: no goals"
      subgoal : otherGoals -> pure (subgoal, otherGoals)
  (phi, psi) <-
    case lookup nameDisjunction asms of
      Nothing -> fail ("cases: '" ++ nameDisjunction ++ "' is not an assumption!")
      Just (phi :\/: psi) -> pure (phi, psi)
      Just _ -> fail ("cases: assumption '" ++ nameDisjunction ++ "' is not of the form 'phi :\\/: psi'!")
  when (nameLeftDisjunct `elem` map fst asms) $
    fail ("destruct: name '" ++ nameLeftDisjunct ++ "' already in scope!")
  when (nameRightDisjunct `elem` map fst asms) $
    fail ("destruct: name '" ++ nameRightDisjunct ++ "' already in scope!")
  let
    asmsWithPhi = (nameLeftDisjunct, phi) : asms
    asmsWithPsi = (nameRightDisjunct, psi) : asms
    subgoalWithPhi = Subgoal { assumptions = asmsWithPhi, claim = target }
    subgoalWithPsi = Subgoal { assumptions = asmsWithPsi, claim = target }
  put $
    state
    { currentGoals = subgoalWithPhi : subgoalWithPsi : otherSubgoals
    , constructProof =
        \case
          subgoalProofWithPhi:subgoalProofWithPsi:otherProofs ->
            let
              subgoalProof =
                LCPrf (or_elim phi psi target)
                  :@ (nameLeftDisjunct ::: phi :-> subgoalProofWithPhi)
                  :@ (nameRightDisjunct ::: psi :-> subgoalProofWithPsi)
                  :@ (LCVar nameDisjunction)
            in constructProof state (subgoalProof:otherProofs)
          _ -> error "cases: expected to get at least two proofs (for the claim, one assuming phi, one assuming psi)"
    }

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
    state
    { currentGoals = Subgoal { assumptions = asms', claim = target } : otherSubgoals
    , constructProof =
        \case
          [] -> error "destruct: expected to get at least one proof!"
          subgoalProof':otherProofs ->
            let
              subgoalProof =
                (leftAsmName ::: phi :-> rightAsmName ::: psi :-> subgoalProof')
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
    state
    { currentGoals = Subgoal { assumptions = asms, claim = Neg psi :=>: Neg phi } : otherSubgoals
    , constructProof =
        \case
          [] -> error "contraposition: expected to get at least one proof"
          contrapositionProof:otherProofs ->
            let
              implicationProof = LCPrf (ax4 phi psi) :@ contrapositionProof
            in
              constructProof state (implicationProof:otherProofs)
    }

introAssumption :: String -> Formula -> Tactic
introAssumption name formula = do
  state <- get
  (Subgoal { assumptions = asms, claim = target }, otherSubgoals) <-
    case currentGoals state of
      subgoal:otherSubgoals -> pure (subgoal, otherSubgoals)
      [] -> fail "have: no goals"
  when (name `elem` map fst asms) $
    fail ("have: name '" ++ name ++ "' already in scope!")
  let
    asms' = (name, formula) : asms
  put $
    state
    { currentGoals = Subgoal { assumptions = asms, claim = formula } : Subgoal { assumptions = asms', claim = target } : otherSubgoals
    , constructProof =
        \case
          formulaProof:targetProofUsingFormula:otherProofs ->
            let targetProof = (name ::: formula :-> targetProofUsingFormula) :@ formulaProof
            in constructProof state (targetProof:otherProofs)
          _ -> error "have: expected to get at least two proofs!"
    }

have :: String -> Formula -> (a -> Tactic) -> a -> Tactic
have name formula toTactic scriptLike = do
  introAssumption name formula
  focus (toTactic scriptLike)

swapSubgoals :: Tactic
swapSubgoals = do
  subgoals <- getSubgoals
  case subgoals of
    firstSubgoal:secondSubgoal:otherSubgoals -> setSubgoals (secondSubgoal:firstSubgoal:otherSubgoals)
    _ -> fail "swapSubgoals: fewer than two subgoals!"

suffices :: String -> Formula -> (a -> Tactic) -> a -> Tactic
suffices name formula toTactic scriptLike = do
  introAssumption name formula
  swapSubgoals
  focus (toTactic scriptLike)

by :: Tactic -> Tactic
by = id

from :: Proof -> Tactic
from = exact

apply :: LC -> Tactic
apply lambdaTerm = do
  state <- get
  (Subgoal { assumptions = asms, claim = target }, otherSubgoals) <-
    case currentGoals state of
      subgoal:otherSubgoals -> pure (subgoal, otherSubgoals)
      [] -> fail "apply: no goals"
  (phi, psi) <-
    case inferType asms lambdaTerm of
      Left err -> fail ("apply: inferring the type of the given type failed with message '" ++ err ++ "'")
      Right (phi :=>: psi) -> pure (phi, psi)
      Right _ -> fail ("apply: given term does not prove an implication!")
  when (psi /= target) $
    fail ("apply: the current target does not match the consequent of the given term, which is '" ++ show psi ++ "'")
  put $
    state
    { currentGoals = Subgoal { assumptions = asms, claim = phi } : otherSubgoals
    , constructProof =
        \case
          [] -> error "apply: expected at least one proof"
          psiProof:otherProofs ->
            let phiProof = lambdaTerm :@ psiProof
            in constructProof state (phiProof:otherProofs)
    }

applyProof :: Proof -> Tactic
applyProof proof = apply (LCPrf proof)

-- | Hides all other subgoals
focus :: TacticM a -> TacticM a
focus script = do
  state <- get
  (subgoal, otherSubgoals) <-
    case currentGoals state of
      [] -> fail "focus: expected one open subgoal"
      subgoal:otherSubgoals -> pure (subgoal, otherSubgoals)
  put $ state { currentGoals = [subgoal] }
  res <- script
  state' <- get
  put $ state' { currentGoals = currentGoals state' ++ otherSubgoals }
  unless (null (currentGoals state')) $
    logMsg ("focus: tactic did not fully solve subgoal '" ++ show (claim subgoal) ++ "'")
  pure res

generalising :: Tactic
generalising = do
  state <- get
  (asms, x, phi, otherSubgoals) <-
    case currentGoals state of
      [] -> fail "generalising: no goals"
      Subgoal { assumptions = asms, claim = Forall x phi } : otherSubgoals -> pure (asms, x, phi, otherSubgoals)
      _:_ -> fail "generalising: expected goal to be of the form 'Forall x phi'"
  let asms' = filter ((x `notElem`) . fvInFormula . snd) asms
  put $
    state
    { currentGoals = Subgoal { assumptions = asms', claim = phi } : otherSubgoals
    , constructProof =
        \case
          [] -> error "generalising: expected to get at least one proof!"
          phiProof:otherProofs -> constructProof state (LCForall x phiProof : otherProofs)
    }

transport :: LC -> (Term -> Formula) -> Tactic
transport term instantiateFormula = do
  state <- get
  (Subgoal { assumptions = asms, claim = target }, otherSubgoals) <-
    case currentGoals state of
      [] -> fail "rewrite: no goal"
      subgoal:otherSubgoals -> pure (subgoal, otherSubgoals)
  (s, t) <-
    case inferType asms term of
      Left err -> fail ("transport: failed to infer type of given term. Reason: '" ++ err ++ "'")
      Right (s :=: t) -> pure (s, t)
      Right _ -> fail ("transport: expected type of term to be of the form 's :=: t'")
  when (target /= instantiateFormula t) $
    fail ("transport: target does not match formula '" ++ show (instantiateFormula t) ++ "'")
  let z = freshVar (varsInFormula (instantiateFormula (Var "x")))
  put $
    state
    { currentGoals = Subgoal { assumptions = asms, claim = instantiateFormula s } : otherSubgoals
    , constructProof =
        \case
          [] -> error "transport: expected to get at least one proof"
          p:ps ->
            let p' = LCPrf (ax9 s t z (instantiateFormula (Var z))) :@ term :@ p
            in constructProof state (p':ps)
    }

-- TODO: 'remainsToShow' tactic
-- TODO: rewrite tactic
-- TODO: tactic for instantiation of forall
-- TODO: tactic for existential introduction
-- TODO: ex falso tactic
-- TODO: auto tactic
-- TODO: admit tactic