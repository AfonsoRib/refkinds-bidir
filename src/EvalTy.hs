{-# LANGUAGE OverloadedStrings #-}

-- | Hidden deterministic evaluator for type-level computation.
module EvalTy (evalTy) where

import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans.Class as Trans
import qualified Substitution as S
import qualified Types as T

type EvalM = IO
data EvalResult = Evaluated T.Type | Suspended T.Type
data TraversalState = BeforeChildren | AfterChild | ChildSuspended

-- Evaluation entry point

evalTy :: T.Type -> IO T.Type
evalTy ty = resultType <$> eval ty

resultType :: EvalResult -> T.Type
resultType (Evaluated ty) = ty

resultType (Suspended ty) = ty

evaluated :: T.Type -> EvalM EvalResult
evaluated = pure . Evaluated

suspended :: T.Type -> EvalM EvalResult
suspended = pure . Suspended

mapResult :: (T.Type -> T.Type) -> EvalResult -> EvalResult
mapResult rebuild (Evaluated ty) = Evaluated (rebuild ty)

mapResult rebuild (Suspended ty) = Suspended (rebuild ty)

-- Unified big-step evaluation

eval :: T.Type -> EvalM EvalResult
eval lambda@T.TLambda {} = evaluated lambda
eval (T.TForall hint domain body) = do
    result <- eval body
    pure (mapResult (T.TForall hint domain) result)
eval (T.TAnn inner@(T.TAnn _ T.KPi {}) T.KPi {}) = eval inner
eval (T.TAnn body classifier@T.KPi {}) = do
    result <- eval body
    pure (attachPi classifier result)
eval (T.TAnn body _) = eval body
eval (T.TLet declaration body) = evalLet declaration body
eval recursive@T.TRec {} = do
    continue recursive (reduceRecursive recursive)
eval (T.TIf condition yes no) = evalIf condition yes no
eval ty
    | Just (T.BAnd, [left, right]) <- T.saturatedTypeOpView ty =
        evalGuard (T.binaryTypeOp T.BAnd) (Just T.TFalse) Nothing left right
    | Just (T.BOr, [left, right]) <- T.saturatedTypeOpView ty =
        evalGuard (T.binaryTypeOp T.BOr) Nothing (Just T.TTrue) left right
eval ty = evalChildren ty
attachPi :: T.Rkind -> EvalResult -> EvalResult
attachPi _ result@(Evaluated (T.TAnn _ T.KPi {})) = result
attachPi classifier result = mapResult (`T.TAnn` classifier) result
evalLet :: T.Decl -> T.Type -> EvalM EvalResult
evalLet (T.Decl hint definition) body = do
    result <- eval definition
    case result of
        Suspended reduced -> suspended (T.TLet (T.Decl hint reduced) body)
        Evaluated value -> eval (S.substitute value body)
evalIf :: T.Type -> T.Type -> T.Type -> EvalM EvalResult
evalIf condition yes no = do
    result <- eval condition
    case result of
        Suspended reduced -> suspended (T.TIf reduced yes no)
        Evaluated value -> case selectBoolean value yes no of
            Just selected -> eval selected
            Nothing -> evaluated (T.TIf value yes no)
evalGuard :: (T.Type -> T.Type -> T.Type) -> Maybe T.Type -> Maybe T.Type
    -> T.Type -> T.Type -> EvalM EvalResult
evalGuard rebuild onFalse onTrue left right = do
    result <- eval left
    case result of
        Suspended reduced -> suspended (rebuild reduced right)
        Evaluated T.TFalse -> finish onFalse
        Evaluated T.TTrue -> finish onTrue
        Evaluated value -> evaluated (rebuild value right)
  where
    finish (Just value) = evaluated value
    finish Nothing = eval right
continue :: T.Type -> Maybe T.Type -> EvalM EvalResult
continue residual Nothing = evaluated residual
continue _ (Just reduced) = eval reduced
evalChildren :: T.Type -> EvalM EvalResult
evalChildren ty = do
    (rebuilt, state) <- State.runStateT
        (T.traverseTypeChildren visit ty) BeforeChildren
    case state of
        ChildSuspended -> suspended rebuilt
        _ -> continue rebuilt (contract rebuilt)
  where
    visit = traverseChild
traverseChild :: T.Type -> State.StateT TraversalState EvalM T.Type
traverseChild child = do
    state <- State.get
    case state of
        ChildSuspended -> pure child
        _ -> evaluateChild child
  where
    evaluateChild :: T.Type -> State.StateT TraversalState EvalM T.Type
    evaluateChild value = do
        result <- Trans.lift (eval value)
        case result of
            Evaluated reduced -> State.put AfterChild >> pure reduced
            Suspended reduced -> State.put ChildSuspended >> pure reduced

-- Contraction helpers

reduceApplication :: T.Type -> T.Type -> Maybe T.Type
reduceApplication (T.TAnn function (T.KPi _ _ codomain)) argument = do
    let result = S.substitute argument codomain
    Just (T.TAnn (T.TApp function argument) result)
reduceApplication (T.TLambda _ body) argument =
    Just (S.substitute argument body)
reduceApplication recursive@(T.TRec _ definition (T.TBound 0)) argument =
    let function = S.substitute recursive
            (stripDefinitionAnnotation definition)
    in Just (T.TApp function argument)
reduceApplication _ _ = Nothing

reduceRecursive :: T.Type -> Maybe T.Type
reduceRecursive recursive@(T.TRec _ definition (T.TBound 0)) =
    case stripDefinitionAnnotation definition of
        T.TLambda {} -> Nothing
        body -> Just (S.substitute recursive body)
reduceRecursive (T.TRec hint definition body) =
    Just (S.substitute (T.TRec hint definition (T.TBound 0)) body)
reduceRecursive _ = Nothing

contract :: T.Type -> Maybe T.Type
contract ty
    | Just (operation, operands) <- T.saturatedTypeOpView ty =
        contractTypeOp operation operands

contract (T.TApp function argument) = reduceApplication function argument

contract _ = Nothing

contractTypeOp :: T.TypeOp -> [T.Type] -> Maybe T.Type
contractTypeOp T.BEq [left, right] =
    booleanType <$> concreteEquality left right
contractTypeOp T.BNot [body] =
    booleanType . not <$> truthValue body
contractTypeOp T.BHead [record] = selectorValue T.BHead record
contractTypeOp T.BHeadLabel [record] = selectorValue T.BHeadLabel record
contractTypeOp T.BTail [record] = selectorValue T.BTail record
contractTypeOp T.BDom [function] = selectorValue T.BDom function
contractTypeOp T.BImg [function] = selectorValue T.BImg function
contractTypeOp T.BRefOf [reference] = selectorValue T.BRefOf reference
contractTypeOp T.BColOf [collection] = selectorValue T.BColOf collection
contractTypeOp T.BConcat [left, right] = appendRows left right
contractTypeOp T.BEmpty [record] = booleanType <$> emptyRecordValue record
contractTypeOp _ _ = Nothing

selectorValue :: T.TypeOp -> T.Type -> Maybe T.Type
selectorValue operation ty = select operation (T.stripAnnotations ty)
  where
    select T.BHead (T.TRecCons _ field _) = Just field
    select T.BHeadLabel (T.TRecCons label _ _) = Just label
    select T.BTail (T.TRecCons _ _ rest) = Just rest
    select T.BDom (T.TArrow domain _) = Just domain
    select T.BImg (T.TArrow _ image) = Just image
    select T.BRefOf (T.TRef element) = Just element
    select T.BColOf (T.TCol element) = Just element
    select _ _ = Nothing

appendRows :: T.Type -> T.Type -> Maybe T.Type
appendRows left right = case T.stripAnnotations left of
    T.TRecNil -> Just right
    T.TRecCons label field rest ->
        let appended = maybe (T.binaryTypeOp T.BConcat rest right) id
                (appendRows rest right)
        in Just (T.TRecCons label field appended)
    _ -> Nothing

emptyRecordValue :: T.Type -> Maybe Bool
emptyRecordValue ty = case T.stripAnnotations ty of
    T.TRecNil -> Just True
    T.TRecCons {} -> Just False
    T.TInt -> Just False
    T.TBool -> Just False
    T.TUnit -> Just False
    T.TString -> Just False
    T.TTrue -> Just False
    T.TFalse -> Just False
    T.TLabel {} -> Just False
    T.TArrow {} -> Just False
    T.TRef {} -> Just False
    T.TCol {} -> Just False
    _ -> Nothing

concreteEquality :: T.Type -> T.Type -> Maybe Bool
concreteEquality left right
    | T.alphaEq left right = Just True
    | all concreteType [left, right] = Just False
    | otherwise = Nothing

concreteType :: T.Type -> Bool
concreteType ty = case T.stripAnnotations ty of
    T.TRecCons label field rest -> all concreteType [label, field, rest]
    T.TArrow domain image -> all concreteType [domain, image]
    T.TRef element -> concreteType element
    T.TCol element -> concreteType element
    T.TRecNil -> True
    T.TInt -> True
    T.TBool -> True
    T.TUnit -> True
    T.TString -> True
    T.TTrue -> True
    T.TFalse -> True
    T.TLabel {} -> True
    _ -> False

truthValue :: T.Type -> Maybe Bool
truthValue T.TTrue = Just True

truthValue T.TFalse = Just False

truthValue _ = Nothing

booleanType :: Bool -> T.Type
booleanType True = T.TTrue

booleanType False = T.TFalse

selectBoolean :: T.Type -> T.Type -> T.Type -> Maybe T.Type
selectBoolean condition yes no =
    select <$> concreteEquality condition T.TTrue
  where
    select True = yes
    select False = no
stripDefinitionAnnotation :: T.Type -> T.Type
stripDefinitionAnnotation (T.TAnn definition classifier) =
    T.retainKind definition classifier
stripDefinitionAnnotation definition = definition
