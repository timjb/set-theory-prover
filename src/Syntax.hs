module Syntax
  ( VarName
  , Ctx
  , Term (..)
  , Formula (..)
  -- * Variable management
  , varUnion
  , freshVar
  -- ** In terms
  , fvInTerm
  , replaceInTerm
  -- ** In formulas
  , fvInFormula
  , replaceInFormula
  -- * Derived logical connectives
  , iff
  -- * Derived predicates
  , truth
  , falsity
  , subset
  , superset
  -- * Derived quantifiers
  , existsUnique
  , forallIn
  , existsIn
  , existsUniqueIn
  -- * Constructions with sets
  , comprehension
  , intersection
  , union
  , emptySet
  , singletonSet
  , pairSet
  ) where

type VarName = String
type Ctx = [VarName]

varUnion :: Ctx -> Ctx -> Ctx
varUnion xs ys = xs ++ filter (`notElem` xs) ys

-- TODO: function application?
data Term
  = Var VarName
  | DefDescr VarName Formula -- ^ definite descriptor
  deriving (Eq, Show)

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
  = Implies Formula Formula -- ^ implication
  | And Formula Formula -- ^ conjunction
  | Or Formula Formula -- ^ disjunction
  | Neg Formula -- ^ negation
  | Eq Term Term -- ^ equality
  | Forall VarName Formula -- ^ universal quantification
  | Exists VarName Formula -- ^ existential quantification
  -- Set-theory
  | Elem Term Term -- ^ Element relation
  deriving (Eq, Show)

iff :: Formula -> Formula -> Formula
iff phi psi = (phi `Implies` psi) `And` (psi `Implies` phi)

existsUnique :: VarName -> Formula -> Formula
existsUnique x phi = Exists x (And phi uniquenessOfX)
  where
    y = freshVar (fvInFormula phi)
    uniquenessOfX = Forall y (Implies (replaceInFormula x (Var y) phi) (Eq (Var x) (Var y)))

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

-- TODO: move into other module?
varSource :: [VarName]
varSource = ["x" ++ show n | n <- [(1 :: Int)..] ]

freshVars :: [VarName] -> [VarName]
freshVars vs = filter (`notElem` vs) varSource

freshVar :: [VarName] -> VarName
freshVar = head . freshVars

truth :: Formula
truth = Forall x (Var x `Eq` Var x)
  where
    x = "x"

falsity :: Formula
falsity = Neg truth

subset :: Term -> Term -> Formula
subset s t =
  let x = freshVar (fvInTerm s `varUnion` fvInTerm t)
  in Forall x ((Var x `Elem` s) `Implies` (Var x `Elem` t))

superset :: Term -> Term -> Formula
superset s t = subset t s

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
comprehension :: VarName -> Term -> Formula -> Term
comprehension x y phi = DefDescr u (Forall x (Elem (Var x) (Var u) `iff` (Elem (Var x) y `And` phi)))
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