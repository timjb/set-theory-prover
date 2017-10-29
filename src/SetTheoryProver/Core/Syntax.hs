{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}

module SetTheoryProver.Core.Syntax
  ( VarName
  , Ctx
  , Term (..)
  , Formula (.., (:=>:), (:\/:), (:/\:), (:=:), (:€:))
  -- * Variable management
  , varUnion
  , freshVar
  -- ** In terms
  , fvInTerm
  , varsInTerm
  , replaceInTerm
  -- ** In formulas
  , fvInFormula
  , varsInFormula
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

import Control.DeepSeq (NFData)
import Data.String (IsString(..))
import GHC.Generics (Generic)

type VarName = String
type Ctx = [VarName]

varUnion :: Ctx -> Ctx -> Ctx
varUnion xs ys = xs ++ filter (`notElem` xs) ys

-- TODO: function application?
data Term
  = Var VarName
  | DefDescr VarName Formula -- ^ definite descriptor
  deriving (Eq, Generic, NFData)

instance IsString Term where
  fromString = Var

instance Show Term where
  showsPrec ctxPrec term =
    case term of
      Var name -> showsPrec ctxPrec name
      DefDescr x phi ->
        let
          showsFn = showsPrec 10 x . (" " ++) . showsPrec 10 phi
        in if appPrec < ctxPrec then
          ("(" ++) . showsFn . (")" ++)
        else
          showsFn
    where
      appPrec = 10

fvInTerm :: Term -> [VarName]
fvInTerm (Var x) = [x]
fvInTerm (DefDescr x f) = filter (/= x) (fvInFormula f)

varsInTerm :: Term -> [VarName]
varsInTerm (Var x) = [x]
varsInTerm (DefDescr x f) = [x] `varUnion` varsInFormula f

replaceInTerm' :: VarName -> Term -> [VarName] -> Term -> Term
replaceInTerm' x s fvInS t =
  case t of
    Var y -> if x == y then s else t
    DefDescr y g -> DefDescr y (replaceInFormulaWithCaptureAndShadowingCheck x s fvInS y g)

replaceInTerm :: VarName -> Term -> Term -> Term
replaceInTerm x s =
  if s == Var x then
    id -- optimization
  else
    replaceInTerm' x s (fvInTerm s)

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
  deriving (Eq, Generic, NFData)

instance Show Formula where
  showsPrec ctxPrec formula =
    case formula of
      Implies phi psi ->
        let showsPsi = case psi of { Implies _ _ -> showsPrec 0; _ -> showsPrec' impliesPrec }
        in parenthesise impliesPrec $ showsPrec' impliesPrec phi . (" :=>: " ++) . showsPsi psi
      And phi psi ->
        let showsPsi = case psi of { And _ _ -> showsPrec 0; _ -> showsPrec' andPrec }
        in parenthesise andPrec (showsPrec' andPrec phi . (" :/\\: " ++) . showsPsi psi)
      Or phi psi ->
        let showsPsi = case psi of { Or _ _ -> showsPrec 0; _ -> showsPrec' orPrec }
        in parenthesise orPrec (showsPrec' orPrec phi . (" :\\/: " ++) . showsPsi psi)
      Neg phi      -> parenthesise appPrec (("Neg " ++) . showsPrec' appPrec phi)
      Eq s t       -> parenthesise eqPrec (showsPrec' eqPrec s . (" :=: " ++) . showsPrec' eqPrec t)
      Forall x phi -> parenthesise appPrec (("Forall " ++) . showsPrec' appPrec x . (" " ++) . showsPrec' appPrec phi)
      Exists x phi -> parenthesise appPrec (("Exists " ++) . showsPrec' appPrec x . (" " ++) . showsPrec' appPrec phi)
      Elem s t     -> parenthesise elemPrec (showsPrec' elemPrec s . (" :€: " ++) . showsPrec' elemPrec t)
    where
      showsPrec' p = showsPrec (p+1)
      eqPrec = 4
      elemPrec = 4
      andPrec = 3
      orPrec = 2
      impliesPrec = 1
      appPrec = 10
      parenthesise opPrec showsFn =
        if opPrec < ctxPrec then
          ("(" ++) . showsFn . (")" ++)
        else
          showsFn

infix  4 :=:, :€:
infixr 3 :/\:
infixr 2 :\/:
infixr 1 :=>:

pattern (:=>:) :: Formula -> Formula -> Formula
pattern f :=>: g = Implies f g

pattern (:\/:) :: Formula -> Formula -> Formula
pattern f :\/: g = Or f g

pattern (:/\:) :: Formula -> Formula -> Formula
pattern f :/\: g = And f g

pattern (:=:) :: Term -> Term -> Formula
pattern f :=: g = Eq f g

pattern (:€:) :: Term -> Term -> Formula
pattern x :€: y  = Elem x y

-- TODO: make pattern synonym?
iff :: Formula -> Formula -> Formula
iff phi psi = (phi :=>: psi) :/\: (psi :=>: phi)

existsUnique :: VarName -> Formula -> Formula
existsUnique x phi = Exists x (phi :/\: uniquenessOfX)
  where
    y = freshVar (fvInFormula phi)
    uniquenessOfX = Forall y (replaceInFormula x (Var y) phi :=>: (Var x :=: Var y))

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

varsInFormula :: Formula -> [VarName]
varsInFormula f =
  case f of
    Implies g h -> varsInFormula g `varUnion` varsInFormula h
    And g h     -> varsInFormula g `varUnion` varsInFormula h
    Or g h      -> varsInFormula g `varUnion` varsInFormula h
    Neg g       -> varsInFormula g
    Eq s t      -> varsInTerm s `varUnion` varsInTerm t
    Forall x g  -> [x] `varUnion` varsInFormula g
    Exists x g  -> [x] `varUnion` varsInFormula g
    Elem s t    -> varsInTerm s `varUnion` varsInTerm t

replaceInFormulaWithCaptureAndShadowingCheck :: VarName -> Term -> [VarName] -> VarName -> Formula -> Formula
replaceInFormulaWithCaptureAndShadowingCheck x s fvInS y g =
  if x == y then -- shadowing
    g
  else if y `elem` fvInS then
    if x `elem` fvInFormula g then -- capturing
      error ("variable '" ++ y ++ "' captured!")
    else
      g
  else
    replaceInFormula' x s fvInS g

replaceInFormula' :: VarName -> Term -> [VarName] -> Formula -> Formula
replaceInFormula' x s fvInS f =
  case f of
    Implies g h -> Implies (recurseFormula g) (recurseFormula h)
    And g h -> And (recurseFormula g) (recurseFormula h)
    Or g h -> Or (recurseFormula g) (recurseFormula h)
    Neg g -> Neg (recurseFormula g)
    Eq r t -> Eq (recurseTerm r) (recurseTerm t)
    Forall y g -> Forall y (replaceInFormulaWithCaptureAndShadowingCheck x s fvInS y g)
    Exists y g -> Exists y (replaceInFormulaWithCaptureAndShadowingCheck x s fvInS y g)
    Elem r t -> Elem (recurseTerm r) (recurseTerm t)
  where
    recurseFormula = replaceInFormula' x s fvInS
    recurseTerm = replaceInTerm' x s fvInS

replaceInFormula :: VarName -> Term -> Formula -> Formula
replaceInFormula x s =
  if s == Var x then
    id -- optimization
  else
    replaceInFormula' x s (fvInTerm s)

-- TODO: move into other module?
varSource :: [VarName]
varSource = ["x" ++ show n | n <- [(1 :: Int)..] ]

freshVars :: [VarName] -> [VarName]
freshVars vs = filter (`notElem` vs) varSource

freshVar :: [VarName] -> VarName
freshVar = head . freshVars

truth :: Formula
truth = Forall x (Var x :=: Var x)
  where
    x = "x"

falsity :: Formula
falsity = Neg truth

subset :: Term -> Term -> Formula
subset s t =
  let x = freshVar (fvInTerm s `varUnion` fvInTerm t)
  in Forall x (Var x :€: s :=>: Var x :€: t)

superset :: Term -> Term -> Formula
superset s t = subset t s

-- TODO: make pattern?
forallIn :: VarName -> Term -> Formula -> Formula
forallIn x y phi = Forall x (Var x :€: y :=>: phi)

-- TODO: make pattern?
existsIn :: VarName -> Term -> Formula -> Formula
existsIn x y phi = Exists x (Var x :€: y :/\: phi)

existsUniqueIn :: VarName -> Term -> Formula -> Formula
existsUniqueIn x y phi = existsUnique x ((Var x :€: y) :/\: phi)

emptySet :: Term
emptySet = DefDescr name (Forall x (Neg (Var x :€: Var name)))
  where
    name = "∅"
    x = "x"

pairSet :: Term -> Term -> Term
pairSet s t =
  let x:y:_ = freshVars (fvInTerm s `varUnion` fvInTerm t)
  in DefDescr x (Forall y ((Var y :€: Var x) `iff` (Var y :=: s :\/: Var y :=: t)))

singletonSet :: Term -> Term
singletonSet t =
  let x:y:_ = freshVars (fvInTerm t)
  in DefDescr x (Forall y ((Var y :€: Var x) `iff` (Var y :=: t)))

-- | '{ x ∈ y | phi }'
comprehension :: VarName -> Term -> Formula -> Term
comprehension x y phi = DefDescr u (Forall x ((Var x :€: Var u) `iff` (Var x :€: y :/\: phi)))
  where
    u = freshVar ([x] `varUnion` (fvInTerm y `varUnion` fvInFormula phi))

logicalToSetOperator :: (Formula -> Formula -> Formula) -> Term -> Term -> Term
logicalToSetOperator op x y =
  DefDescr u (Forall v ((Var v :€: Var u) `iff` ((Var v :€: x) `op` (Var v :€: y))))
  where
    u:v:_ = freshVars (fvInTerm x `varUnion` fvInTerm y)

intersection :: Term -> Term -> Term
intersection = logicalToSetOperator (:/\:)

union :: Term -> Term -> Term
union = logicalToSetOperator (:\/:)