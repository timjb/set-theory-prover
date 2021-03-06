{-# LANGUAGE PatternSynonyms #-}

module SetTheoryProver.Interactive.LambdaEmbedding
  (
  -- * Translating lambda terms to proofs
    LC(.., (:->), (:@), (:@@))
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
  | LCTermAbs VarName LC        -- ^ all-quantification
  | LCTermApp LC Term           -- ^ instantiation of an all-quantified formula

infix 8 :::
infixl 4 :@, :@@
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

pattern (:@@) :: LC -> Term -> LC
pattern s :@@ t = LCTermApp s t

freeVariables :: LC -> [VarName]
freeVariables t =
  case t of
    LCAbs arg s   -> filter (/= fst arg) (freeVariables s)
    LCApp u v     -> freeVariables u `varUnion` freeVariables v
    LCVar x       -> [x]
    LCPrf _       -> []
    LCTermAbs _ s -> freeVariables s
    LCTermApp s _ -> freeVariables s

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
    LCTermAbs x body ->
      let
        typeOfVariableContainsX v =
          case lookup v env of
            Nothing -> False
            Just formula -> x `elem` fvInFormula formula
      in
        case filter typeOfVariableContainsX (freeVariables body) of
          v:_ ->
            Left
              ("forbidden usage of lambda variable '" ++ v ++ "' (whose formula contains '" ++ x ++ "') " ++
               "in term proving all-quantified (over '" ++ x ++ "') subformula")
          [] -> Forall x <$> inferType env body
    LCTermApp s term -> do
      sType <- inferType env s
      case sType of
        Forall x phi -> Right (replaceInFormula x term phi)
        _ -> Left "expected first argument of LCTermApp to have type of the form 'Forall x phi'"

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
              phi :=>: psi ->
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
                    ((LCPrf (ax3 phi psi xi) `LCApp` fun') `LCApp` arg', phi :=>: xi)
                  _ -> error "translate: expected a function type with two arguments, the first of which is phi!"
            LCAbs _ _ | x `elem` freeVariables body ->
              let
                env' = (x,phi):env
                (body', _) = go env' body
              in
                go env (LCAbs (x, phi) body')
            LCTermAbs y forallBody | x `elem` freeVariables body ->
              if y `elem` fvInFormula phi then
                error
                  ("translate: forbidden usage of lambda variable '" ++ x ++ "' (whose formula contains '" ++ y ++ "') " ++
                   "in term proving all-quantified (over '" ++ y ++ "') subformula")
              else
                let
                  env' = (x,phi):env
                  (forallBody', forallBodyType) = go env' (LCAbs (x, phi) forallBody)
                in
                  case forallBodyType of
                    phi' :=>: psi | phi == phi' ->
                      go env (LCAbs (x, phi) ((LCPrf (ax6 y phi psi) `LCApp` (LCTermAbs y forallBody')) `LCApp` (LCPrf (ax7 y phi) `LCApp` LCVar x)))
                    _ -> error "translate: expected a function type with two arguments, the first of which is phi!"
            LCTermApp s _ | x `elem` freeVariables s ->
              let
                env' = (x,phi):env
                (body', _) = go env' body
              in
                go env (LCAbs (x,phi) body')
            _ -> -- x is not free in body
              let
                (body', bodyType) = go env body
              in
                (LCPrf (ax2 bodyType phi) `LCApp` body', phi :=>: bodyType)
        LCPrf p -> (LCPrf p, getFormula p)
        LCTermAbs x body ->
          let
            (body', bodyType) = go env body
          in
            (LCTermAbs x body', Forall x bodyType)
        LCTermApp s t ->
          let
            (s', sType) = go env s
          in
            case sType of
              Forall x phi ->
                (LCPrf (ax5 x t phi) :@ s', replaceInFormula x t phi)
              _ -> error "translate: expected an all-quantified formula"
    extract :: LC -> Proof
    extract term =
      case term of
        LCPrf p -> p
        LCApp fun arg -> extract fun `mp` extract arg
        LCTermAbs x body -> generalise x (extract body)
        LCAbs _ _ -> error "translate: didn't expect function in extract"
        LCVar _ -> error "translate: didn't expect variable in extract"
        LCTermApp _ _ -> error "translate: didn't expect term application"