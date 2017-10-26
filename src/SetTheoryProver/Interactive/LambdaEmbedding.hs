{-# LANGUAGE PatternSynonyms #-}

module SetTheoryProver.Interactive.LambdaEmbedding
  (
  -- * Translating lambda terms to proofs
    LC(.., (:->), (:@))
  , pattern (:::)
  , ToLC(..)
  , inferType
  , translate
  ) where

import SetTheoryProver.Core

import Control.Monad (when)
import Data.Maybe (fromMaybe)
import Data.String (IsString(..))

data LC
  = LCAbs (VarName, Formula) LC -- ^ lambda abstraction
  | LCApp LC LC                 -- ^ application
  | LCVar VarName               -- ^ variable
  | LCPrf Proof                 -- ^ proof

infix 8 :::
infixl 4 :@
infixr 1 :->

instance IsString LC where
  fromString = LCVar

class ToLC a where
  toLC :: a -> LC

instance ToLC LC where
  toLC = id

instance ToLC Proof where
  toLC = LCPrf

pattern (:::) :: VarName -> Formula -> (VarName, Formula)
pattern x ::: y = (x, y)

pattern (:->) :: (VarName, Formula) -> LC -> LC
pattern arg :-> t = LCAbs arg t

pattern (:@) :: LC -> LC -> LC
pattern s :@ t = LCApp s t

freeVariables :: LC -> [VarName]
freeVariables t =
  case t of
    LCAbs arg s -> filter (/= fst arg) (freeVariables s)
    LCApp u v   -> freeVariables u `varUnion` freeVariables v
    LCVar x     -> [x]
    LCPrf _     -> []

inferType :: [(VarName, Formula)] -> LC -> Either String Formula
inferType env t =
  case t of
    LCAbs arg@(_, formula) body ->
      (formula :=>:) <$> inferType (arg:env) body
    LCApp u v -> do
      uType <- inferType env u
      vType <- inferType env v
      case uType of
        phi :=>: psi -> do
          when (phi /= vType) $
            Left "type of applicant doesn't match the antecedent of the implication"
          pure psi
        _ -> Left "the first argument of an application must be of the form 'phi :=>: psi'"
    LCVar x ->
      case lookup x env of
        Nothing -> Left ("'" ++ x ++ "' is not in environment!")
        Just formula -> Right formula
    LCPrf p ->
      Right (getFormula p)

translate :: LC -> Proof
translate lambdaTerm = extract (fst (go [] lambdaTerm))
  where
    getEnv :: VarName -> [(VarName, x)] -> x
    getEnv x env = fromMaybe (error ("translate: variable '" ++ x ++ "' not in environment!")) (lookup x env)
    -- https://en.wikipedia.org/wiki/Combinatory_logic#Completeness_of_the_S-K_basis
    go :: [(VarName, Formula)] -> LC -> (LC, Formula)
    go env term =
      case term of
        LCVar x -> (LCVar x, getEnv x env)
        LCApp fun arg ->
          let
            (fun', funType) = go env fun
            (arg', argType) = go env arg
          in
            case funType of
              Implies phi psi ->
                if phi == argType
                  then (LCApp fun' arg', psi)
                  else error "translate: argument types don't match!"
              _ -> error "translate: expected a function type!"
        LCAbs (x, phi) body ->
          case body of
            LCVar y | y == x -> (LCPrf (ax1 phi), phi :=>: phi)
            LCApp fun arg | x `elem` freeVariables body ->
              let
                (fun', funType) = go env (LCAbs (x, phi) fun)
                (arg', _argType) = go env (LCAbs (x, phi) arg)
              in
                case funType of
                  phi' :=>: (psi :=>: xi) | phi == phi' ->
                    ((LCPrf (ax3 phi psi xi) `LCApp` fun') `LCApp` arg', phi `Implies` xi)
                  _ -> error "translate: expected a function type with two arguments, the first of which is phi!"
            LCAbs _ _ | x `elem` freeVariables body ->
              let
                env' = (x,phi):env
                (body', _) = go env' body
              in
                go env (LCAbs (x, phi) body')
            _ -> -- x is not free in body
              let
                (body', bodyType) = go env body
              in
                (LCPrf (ax2 bodyType phi) `LCApp` body', phi `Implies` bodyType)
        LCPrf p -> (LCPrf p, getFormula p)
    extract :: LC -> Proof
    extract term =
      case term of
        LCPrf p -> p
        LCApp fun arg -> extract fun `mp` extract arg
        LCAbs _ _ -> error "translate: didn't expect function in extract"
        LCVar _ -> error "translate: didn't expect variable in extract"