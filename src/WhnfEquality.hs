-- | Experimental structural conversion with reduction only at demanded heads.
module WhnfEquality (structurallyEqual) where

import qualified Substitution as S
import qualified Types as T

-- Comparison ---------------------------------------------------------------

structurallyEqual :: T.Type -> T.Type -> Bool
structurallyEqual left right = compareHeads (whnf left) (whnf right)

compareHeads :: T.Type -> T.Type -> Bool
compareHeads T.TUnit T.TUnit = True

compareHeads T.TInt T.TInt = True

compareHeads T.TBool T.TBool = True

compareHeads T.TString T.TString = True

compareHeads T.TTrue T.TTrue = True

compareHeads T.TFalse T.TFalse = True

compareHeads T.TRecNil T.TRecNil = True

compareHeads (T.TLabel left) (T.TLabel right) = left == right

compareHeads (T.TVar left) (T.TVar right) = left == right

compareHeads (T.TBound left) (T.TBound right) = left == right

compareHeads (T.PBIn left) (T.PBIn right) = left == right

compareHeads (T.TRef left) (T.TRef right) = structurallyEqual left right

compareHeads (T.TCol left) (T.TCol right) = structurallyEqual left right

compareHeads (T.TArrow domain1 image1) (T.TArrow domain2 image2) =
    structurallyEqual domain1 domain2 && structurallyEqual image1 image2

compareHeads (T.TRecCons label1 field1 rest1)
    (T.TRecCons label2 field2 rest2) =
    structurallyEqual label1 label2 && structurallyEqual field1 field2 &&
        structurallyEqual rest1 rest2

compareHeads (T.TApp function1 argument1)
    (T.TApp function2 argument2) =
    structurallyEqual function1 function2 && structurallyEqual argument1 argument2

compareHeads (T.TLambda _ body1) (T.TLambda _ body2) =
    structurallyEqual body1 body2

compareHeads (T.TForall _ domain1 body1) (T.TForall _ domain2 body2) =
    T.alphaEqKind domain1 domain2 && structurallyEqual body1 body2

compareHeads (T.TAnn body1 kind1) (T.TAnn body2 kind2) =
    T.alphaEqKind kind1 kind2 && structurallyEqual body1 body2

compareHeads (T.TIf condition1 yes1 no1) (T.TIf condition2 yes2 no2) =
    structurallyEqual condition1 condition2 && structurallyEqual yes1 yes2 &&
        structurallyEqual no1 no2

compareHeads (T.TLet (T.Decl _ definition1) body1)
    (T.TLet (T.Decl _ definition2) body2) =
    structurallyEqual definition1 definition2 && structurallyEqual body1 body2

compareHeads (T.TRec _ definition1 body1)
    (T.TRec _ definition2 body2) =
    structurallyEqual definition1 definition2 && structurallyEqual body1 body2

compareHeads _ _ = False

-- Reduction ----------------------------------------------------------------

whnf :: T.Type -> T.Type
whnf (T.TAnn (T.TAnn body inner@T.KPi {}) T.KPi {}) =
    whnf (T.TAnn body inner)

whnf (T.TAnn body classifier@T.KPi {}) =
    T.retainKind (whnf body) classifier

whnf (T.TAnn body _) = whnf body

whnf (T.TLet (T.Decl hint definition) body) =
    let value = whnf definition
    in if isHeadValue value
        then whnf (S.substitute value body)
        else T.TLet (T.Decl hint value) body

whnf recursive@(T.TRec hint definition body) =
    case body of
        T.TBound 0 -> case stripDefinitionAnnotation definition of
            T.TLambda {} -> recursive
            reduced -> whnf (S.substitute recursive reduced)
        _ -> whnf (S.substitute
            (T.TRec hint definition (T.TBound 0)) body)

whnf (T.TIf condition yes no) =
    case whnf condition of
        T.TTrue -> whnf yes
        T.TFalse -> whnf no
        reduced -> T.TIf reduced yes no

whnf ty
    | Just (operation, operands) <- T.saturatedTypeOpView ty =
        reduceOperation operation operands

whnf (T.TApp function argument) =
    let headFunction = whnf function
    in case headFunction of
        T.TLambda _ body -> whnf (S.substitute (whnf argument) body)
        T.TAnn (T.TLambda _ body) T.KPi {} ->
            whnf (S.substitute (whnf argument) body)
        recursive@(T.TRec _ definition (T.TBound 0)) ->
            whnf (T.TApp
                (S.substitute recursive (stripDefinitionAnnotation definition))
                argument)
        _ -> T.TApp headFunction argument

whnf ty = ty

reduceOperation :: T.TypeOp -> [T.Type] -> T.Type
reduceOperation T.BAnd [left, right] =
    case whnf left of
        T.TFalse -> T.TFalse
        T.TTrue -> whnf right
        reduced -> T.binaryTypeOp T.BAnd reduced right

reduceOperation T.BOr [left, right] =
    case whnf left of
        T.TTrue -> T.TTrue
        T.TFalse -> whnf right
        reduced -> T.binaryTypeOp T.BOr reduced right

reduceOperation operation [operand]
    | operation `elem` [T.BHead, T.BHeadLabel, T.BTail, T.BDom,
        T.BImg, T.BRefOf, T.BColOf] =
        let reduced = whnf operand
        in maybe (T.unaryTypeOp operation reduced) whnf
            (select operation (T.stripAnnotations reduced))

reduceOperation T.BNot [operand] =
    case whnf operand of
        T.TTrue -> T.TFalse
        T.TFalse -> T.TTrue
        reduced -> T.unaryTypeOp T.BNot reduced

reduceOperation T.BEmpty [operand] =
    let reduced = whnf operand
    in case T.stripAnnotations reduced of
        T.TRecNil -> T.TTrue
        T.TRecCons {} -> T.TFalse
        _ -> T.unaryTypeOp T.BEmpty reduced

reduceOperation T.BConcat [left, right] =
    let leftHead = whnf left
    in case T.stripAnnotations leftHead of
        T.TRecNil -> whnf right
        T.TRecCons label field rest ->
            T.TRecCons label field (T.binaryTypeOp T.BConcat rest right)
        _ -> T.binaryTypeOp T.BConcat leftHead right

reduceOperation T.BEq [left, right] =
    let leftHead = whnf left
        rightHead = whnf right
    in if structurallyEqual leftHead rightHead
        then T.TTrue
        else if concreteType leftHead && concreteType rightHead
            then T.TFalse
        else T.binaryTypeOp T.BEq leftHead rightHead

reduceOperation operation operands = T.typeOpApp operation operands

select :: T.TypeOp -> T.Type -> Maybe T.Type
select T.BHead (T.TRecCons _ field _) = Just field

select T.BHeadLabel (T.TRecCons label _ _) = Just label

select T.BTail (T.TRecCons _ _ rest) = Just rest

select T.BDom (T.TArrow domain _) = Just domain

select T.BImg (T.TArrow _ image) = Just image

select T.BRefOf (T.TRef element) = Just element

select T.BColOf (T.TCol element) = Just element

select _ _ = Nothing

isHeadValue :: T.Type -> Bool
isHeadValue T.TApp {} = False

isHeadValue T.TIf {} = False

isHeadValue T.TLet {} = False

isHeadValue _ = True

concreteType :: T.Type -> Bool
concreteType ty = case whnf ty of
    T.TRecCons label field rest ->
        all concreteType [label, field, rest]
    T.TArrow domain image -> all concreteType [domain, image]
    T.TRef element -> concreteType element
    T.TCol element -> concreteType element
    T.TRecNil -> True
    T.TUnit -> True
    T.TInt -> True
    T.TBool -> True
    T.TString -> True
    T.TTrue -> True
    T.TFalse -> True
    T.TLabel {} -> True
    _ -> False

stripDefinitionAnnotation :: T.Type -> T.Type
stripDefinitionAnnotation (T.TAnn definition classifier) =
    T.retainKind definition classifier

stripDefinitionAnnotation definition = definition
