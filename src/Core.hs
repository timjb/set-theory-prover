module Core
  ( VarName
  , Term (..)
  , Formula (..)
  , iff, existsUnique
  , Proof(getFormula)
  , mp
  , ax2, ax3, ax4, ax5, ax6, ax7, ax8, ax9
  , and_intro, and_elim1, and_elim2
  , or_intro1, or_intro2, or_elim
  , exists_elim
  , subset, forallIn, existsIn
  , emptySet, setComprehension, intersection, union
  , pairSet, singletonSet
  , extensionalityAxiom
  , regularityAxiom
  , separationAxiom
  , pairingAxiom
  , unionAxiom
  , replacementAxiom
  , infinityAxiom
  , powersetAxiom
  , choiceAxiom
  ) where

type VarName = String

varUnion :: [VarName] -> [VarName] -> [VarName]
varUnion xs ys = xs ++ filter (`notElem` xs) ys

-- TODO: function application?
data Term
  = Var VarName
  | DefDescr VarName Formula -- ^ definite descriptor
  deriving (Eq)

fvInTerm :: Term -> [VarName]
fvInTerm (Var x) = [x]
fvInTerm (DefDescr x f) = filter (/= x) (fvInFormula f)

replaceInTerm :: VarName -> Term -> Term -> Term
replaceInTerm x s t =
  case t of
    Var y -> if x == y then s else t
    DefDescr y f -> if x == y then t else DefDescr y (replaceInFormula x s f)

data Formula
  -- First-order logic (with equality)
  = Implies Formula Formula
  | And Formula Formula
  | Or Formula Formula
  | Neg Formula
  | Eq Term Term
  | Forall VarName Formula
  | Exists VarName Formula
  -- Set-theory
  | Elem Term Term
  deriving (Eq)

iff :: Formula -> Formula -> Formula
iff phi psi = (phi `Implies` psi) `And` (psi `Implies` phi)

existsUnique :: VarName -> Formula -> Formula
existsUnique x phi = Exists x (And phi uniquenessOfX)
  where
    y = freshVar (fvInFormula phi)
    uniquenessOfX = Forall y (Implies (replaceInFormula x (Var y) phi) (Eq (Var x) (Var y)))

-- | Introduce all-quantifiers for all free variables
generalize :: Formula -> Formula
generalize phi =
  let vs = fvInFormula phi
  in foldl (\psi v -> Forall v psi) phi vs

fvInFormula :: Formula -> [VarName]
fvInFormula f =
  case f of
    Implies g h -> fvInFormula g `varUnion` fvInFormula h
    And g h     -> fvInFormula g `varUnion` fvInFormula h
    Or g h      -> fvInFormula g `varUnion` fvInFormula h
    Neg g       -> fvInFormula g
    Eq s t      -> fvInTerm s `varUnion` fvInTerm t
    Forall x g  -> filter (/= x) (fvInFormula g)
    Exists x g  -> filter (/= x) (fvInFormula g)
    Elem s t    -> fvInTerm s `varUnion` fvInTerm t

replaceInFormula :: VarName -> Term -> Formula -> Formula
replaceInFormula x s f =
  case f of
    Implies g h -> Implies (replaceInFormula x s g) (replaceInFormula x s h)
    And g h -> And (replaceInFormula x s g) (replaceInFormula x s h)
    Or g h -> Or (replaceInFormula x s g) (replaceInFormula x s h)
    Neg g -> Neg (replaceInFormula x s g)
    Eq r t -> Eq (replaceInTerm x s r) (replaceInTerm x s t)
    Forall y g -> if x == y then f else Forall y (replaceInFormula x s g)
    Exists y g -> if x == y then f else Exists y (replaceInFormula x s g)
    Elem r t -> Elem (replaceInTerm x s r) (replaceInTerm x s t)

newtype Proof = Proof { getFormula :: Formula }

-- | Modus Ponens
mp :: Proof -> Proof -> Proof
mp (Proof p) (Proof q) =
  case p of
    Implies precedent consequent ->
      if precedent == q
        then Proof consequent
        else error "mp: The second argument of 'mp' must be equal to the precedent of the first argument!"
    _ -> error "mp: The first argument to 'mp' must be the proof of an implication!"

-- | Axiom schema 'φ ⇒ ψ ⇒ φ'
ax2 :: Formula -> Formula -> Proof
ax2 phi psi = Proof (generalize (Implies phi (Implies psi phi)))

-- | Axiom schema '(φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ)'
ax3 :: Formula -> Formula -> Formula -> Proof
ax3 phi psi xi = Proof (generalize (Implies antecedent consequent))
  where
    antecedent = Implies phi (Implies psi xi)
    consequent = Implies (Implies phi psi) (Implies phi xi)

-- | Axiom schema '(¬φ ⇒ ¬ψ) ⇒ ψ ⇒ φ
ax4 :: Formula -> Formula -> Proof
ax4 phi psi = Proof (generalize (Implies antecedent consequent))
  where
    antecedent = Implies (Neg phi) (Neg psi)
    consequent = Implies psi phi

-- | Axiom schema '(∀x. φ) ⇒ φ[x := t]'
ax5 :: VarName -> Term -> Formula -> Proof
ax5 x s phi = Proof (generalize (Implies antecedent consequent))
  where
    antecedent = Forall x phi
    consequent = replaceInFormula x s phi

-- | Axiom schema '(∀x. φ ⇒ ψ) ⇒ (∀x. φ) ⇒ (∀x. ψ)'
ax6 :: VarName -> Formula -> Formula -> Proof
ax6 x phi psi = Proof (generalize (Implies antecedent consequent))
  where
    antecedent = Forall x (Implies phi psi)
    consequent = Implies (Forall x phi) (Forall x psi)

-- | Axiom schema 'φ ⇒ (∀x. φ)' if x is not free in φ
ax7 :: Formula -> VarName -> Proof
ax7 phi x =
  if x `elem` fvInFormula phi
    then error "ax7: variable must not occur freely in formula!"
    else Proof (Implies phi (Forall x phi))

-- | Axiom schema 't = t' (reflexivity)
ax8 :: Term -> Proof
ax8 t = Proof (generalize (Eq t t))

-- | Axiom schema 's = t ⇒ φ[x := s] ⇒ φ[x := t]' (transport)
ax9 :: Term -> Term -> VarName -> Formula -> Proof
ax9 s t x phi = Proof (generalize (Implies antecedent consequent))
  where
    antecedent = Eq s t
    consequent = Implies (replaceInFormula x s phi) (replaceInFormula x t phi)

-- | Axiom schema 'φ ⇒ (ψ ⇒ φ ∧ ψ)'
and_intro :: Formula -> Formula -> Proof
and_intro phi psi = Proof (Implies phi (Implies psi (And phi psi)))

-- | Axiom schema 'φ ∧ ψ ⇒ φ'
and_elim1 :: Formula -> Formula -> Proof
and_elim1 phi psi = Proof (generalize (Implies (And phi psi) phi))

-- | Axiom schema 'φ ∧ ψ ⇒ ψ'
and_elim2 :: Formula -> Formula -> Proof
and_elim2 phi psi = Proof (generalize (Implies (And phi psi) psi))

-- | Axiom schema '(φ ⇒ ξ) ⇒ (ψ ⇒ ξ) ⇒ (φ ∨ ψ ⇒ ξ)'
or_elim :: Formula -> Formula -> Formula -> Proof
or_elim phi psi xi = Proof (generalize (Implies (Implies phi xi) (Implies (Implies psi xi) (Implies (Or phi psi) xi))))

-- | Axiom schema 'φ ⇒ φ ∨ ψ'
or_intro1 :: Formula -> Formula -> Proof
or_intro1 phi psi = Proof (generalize (Implies phi (Or phi psi)))

-- | Axiom schema 'ψ ⇒ φ ∨ ψ'
or_intro2 :: Formula -> Formula -> Proof
or_intro2 phi psi = Proof (generalize (Implies psi (Or phi psi)))

-- | Axiom schema '(∀x. φ ⇒ ψ) ⇒ (∃x. φ) ⇒ ψ'
exists_elim :: VarName -> Formula -> Formula -> Proof
exists_elim x phi psi =
  if x `elem` fvInFormula psi
    then error "exists_elim: variable must not occur freely in second formula"
    else Proof (generalize (Implies precedent consequent))
  where
    precedent = Forall x (Implies phi psi)
    consequent = Implies (Exists x phi) psi

-- TODO: move into other module?
varSource :: [VarName]
varSource = ["x" ++ show n | n <- [(1 :: Int)..] ]

freshVars :: [VarName] -> [VarName]
freshVars vs = filter (`notElem` vs) varSource

freshVar :: [VarName] -> VarName
freshVar = head . freshVars

-- TODO: move into other module?
subset :: Term -> Term -> Formula
subset s t =
  let x = freshVar (fvInTerm s `varUnion` fvInTerm t)
  in Forall x ((Var x `Elem` s) `Implies` (Var x `Elem` t))

-- TODO: make pattern?
forallIn :: VarName -> Term -> Formula -> Formula
forallIn x y phi = Forall x ((Var x `Elem` y) `Implies` phi)

-- TODO: make pattern?
existsIn :: VarName -> Term -> Formula -> Formula
existsIn x y phi = Exists x ((Var x `Elem` y) `And` phi)

existsUniqueIn :: VarName -> Term -> Formula -> Formula
existsUniqueIn x y phi = existsUnique x ((Var x `Elem` y) `And` phi)

emptySet :: Term
emptySet = DefDescr name (Forall x (Neg (Var x `Elem` Var name)))
  where
    name = "∅"
    x = "x"

pairSet :: Term -> Term -> Term
pairSet s t =
  let x:y:_ = freshVars (fvInTerm s `varUnion` fvInTerm t)
  in DefDescr x (Forall y ((Var y `Elem` Var x) `iff` ((Var y `Eq` s) `Or` (Var y `Eq` t))))

singletonSet :: Term -> Term
singletonSet t =
  let x:y:_ = freshVars (fvInTerm t)
  in DefDescr x (Forall y ((Var y `Elem` Var x) `iff` (Var y `Eq` t)))

-- | '{ x ∈ y | phi }'
setComprehension :: VarName -> Term -> Formula -> Term
setComprehension x y phi = DefDescr u (Forall x (Elem (Var x) (Var u) `iff` (Elem (Var x) y `And` phi)))
  where
    u = freshVar ([x] `varUnion` (fvInTerm y `varUnion` fvInFormula phi))

logicalToSetOperator :: (Formula -> Formula -> Formula) -> Term -> Term -> Term
logicalToSetOperator op x y =
  DefDescr u (Forall v ((Var v `Elem` Var u) `iff` ((Var v `Elem` x) `op` (Var v `Elem` y))))
  where
    u:v:_ = freshVars (fvInTerm x `varUnion` fvInTerm y)

intersection :: Term -> Term -> Term
intersection = logicalToSetOperator And

union :: Term -> Term -> Term
union = logicalToSetOperator Or

-- ZFC axioms
-- (source: https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory)

extensionalityAxiom :: Proof
extensionalityAxiom = Proof (Forall x (Forall y (Implies antecedent consequent)))
  where
    antecedent = And (subset (Var x) (Var y)) (subset (Var y) (Var x))
    consequent = Eq (Var x) (Var y)
    x = "x"
    y = "y"

regularityAxiom :: Proof
regularityAxiom = Proof (Forall x (Implies antecedent consequent))
  where
    antecedent = Exists y (Elem (Var y) (Var x))
    consequent = existsIn y (Var x) (Neg (existsIn z (Var y) (Elem (Var z) (Var x))))
    x = "x"
    y = "y"
    z = "z"

-- TODO: do we have to check that x /= z?
separationAxiom :: VarName -> VarName -> Formula -> Proof
separationAxiom x z phi =
  let y = freshVar (fvInFormula phi `varUnion` [x,z])
  in Proof (generalize (Forall z (Exists y (Forall x ((Var x `Elem` Var y) `iff` ((Var x `Elem` Var z) `And` phi))))))

pairingAxiom :: Proof
pairingAxiom = Proof (Forall x (Forall y (Exists z ((Var x `Elem` Var z) `And` (Var y `Elem` Var z)))))
  where
    x = "x"
    y = "y"
    z = "z"

unionAxiom :: Proof
unionAxiom = Proof (Forall x (Exists y (forallIn v (Var x) (forallIn u (Var v) (Var u `Elem` Var x)))))
  where
    x = "x"
    y = "y"
    u = "u"
    v = "v"

-- TODO: do we have to check that x y a are pairwise different?
replacementAxiom :: VarName -> VarName -> VarName -> Formula -> Proof
replacementAxiom x y a phi =
  let b = freshVar (fvInFormula phi)
      antecedent = forallIn x (Var a) (existsUnique y phi)
      consequent = Exists b (forallIn x (Var a) (existsIn y (Var b) phi))
  in Proof (generalize (antecedent `Implies` consequent))

successor :: Term -> Term
successor x = pairSet x (singletonSet x)

infinityAxiom :: Proof
infinityAxiom = Proof (Exists x ((emptySet `Elem` Var x) `And` forallIn y (Var x) (successor (Var y) `Elem` Var x)))
  where
    x = "x"
    y = "y"

powersetAxiom :: Proof
powersetAxiom = Proof (Forall x (Exists y (Forall z ((Var z `Elem` Var y) `iff` (Var z `subset` Var x)))))
  where
    x = "x"
    y = "y"
    z = "z"

-- TODO: axiom of choice
choiceAxiom :: Proof
choiceAxiom = Proof (Forall z (Implies precedent consequent))
  where
    precondition1 = forallIn x (Var z) (Exists y (Var y `Elem` Var x))
    precondition2 = forallIn x1 (Var z) (forallIn x2 (Var z) (Neg (existsIn y (Var x1) (Var y `Elem` Var x2))))
    precedent = precondition1 `And` precondition2
    consequent = Exists w (forallIn x (Var z) (existsUniqueIn y (Var w) (Var y `Elem` Var x)))
    x = "x"
    x1 = "x1"
    x2 = "x2"
    y = "y"
    z = "z"
    w = "w"