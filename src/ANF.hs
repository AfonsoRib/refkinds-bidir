{-# LANGUAGE OverloadedStrings #-}
module ANF
  ( elaborate
  , elaborateExpr
  ) where

import qualified Control.Monad.State.Strict as State
import qualified Substitution as S
import qualified Types as T

type Anf = State.State [String]

freshId :: Anf String
freshId = do
  used <- State.get
  let fresh = S.freshName used
  State.put (fresh : used)
  pure fresh

elaborate :: T.Type -> T.Type
elaborate t = State.evalState (toAnfTypeM t) (S.allTypeNames t)

-- This is ANF elaboration, not call-by-value evaluation or normalization.
toAnfTypeM :: T.Type -> Anf T.Type
toAnfTypeM t
  | Just (T.BAnd, [left, right]) <- T.saturatedTypeOpView t =
      T.binaryTypeOp T.BAnd <$> toAnfTypeM left <*> toAnfTypeM right
  | Just (T.BOr, [left, right]) <- T.saturatedTypeOpView t =
      T.binaryTypeOp T.BOr <$> toAnfTypeM left <*> toAnfTypeM right

toAnfTypeM t = case t of
  T.TRecCons l ty r -> ternaryAtoms T.TRecCons l ty r
  T.TArrow d i -> binaryAtoms T.TArrow d i
  T.TRef e -> withAtom e (pure . T.TRef)
  T.TCol e -> withAtom e (pure . T.TCol)
  T.TLambda b body -> T.TLambda b <$> toAnfTypeM body
  T.TApp fn arg -> do
    withAtom fn $ \fn' ->
      withVariable arg $ \arg' ->
        pure (T.TApp fn' arg')
  T.TAnn term k -> T.TAnn <$> toAnfTypeM term <*> pure k
  T.TForall b k body -> T.TForall b k <$> toAnfTypeM body
  T.TLet (T.Decl b d) body -> do
    d' <- toAnfTypeM d
    body' <- toAnfTypeM body
    typeLet b d' body'
  T.TRec b d body -> do
    d' <- toAnfTypeM d
    body' <- toAnfTypeM body
    pure (T.TRec b d' body')
  T.TIf c whenT whenF -> do
    c' <- toAnfTypeM c
    whenT' <- toAnfTypeM whenT
    whenF' <- toAnfTypeM whenF
    pure (T.TIf c' whenT' whenF')
  _ -> pure t

binaryAtoms :: (T.Type -> T.Type -> T.Type) -> T.Type -> T.Type -> Anf T.Type
binaryAtoms c l r = withAtom l $ \l' -> withAtom r $ \r' -> pure (c l' r')

ternaryAtoms :: (T.Type -> T.Type -> T.Type -> T.Type) -> T.Type -> T.Type -> T.Type -> Anf T.Type
ternaryAtoms c a b d =
  withAtom a $ \a' -> withAtom b $ \b' -> withAtom d $ \d' -> pure (c a' b' d')

withAtom :: T.Type -> (T.Type -> Anf T.Type) -> Anf T.Type
withAtom src cont = do
  norm <- toAnfTypeM src
  continueWithAtom norm cont

continueWithAtom :: T.Type -> (T.Type -> Anf T.Type) -> Anf T.Type
continueWithAtom norm cont
  | isTypeAtom norm = cont norm
continueWithAtom (T.TLet (T.Decl b d) body) cont = do
  fresh <- freshId
  let body' = S.unabstractType (T.typeName fresh) body
  bodyRes <- continueWithAtom body' cont
  pure (T.TLet (T.Decl fresh d) (S.abstractTypeBody [T.typeName fresh] bodyRes))
continueWithAtom norm cont = do
  fresh <- freshId
  body <- cont (T.TVar (T.typeName fresh))
  pure (T.TLet (T.Decl fresh norm) (S.abstractTypeBody [T.typeName fresh] body))

-- Float administrative lets in a definition without naming its final result
-- again. This keeps ANF idempotent and preserves the source synthesis boundary.
typeLet :: T.Identifier -> T.Type -> T.Type -> Anf T.Type
typeLet hint (T.TLet (T.Decl _ definition) inner) body = do
  fresh <- freshId
  result <- typeLet hint (S.unabstractType (T.typeName fresh) inner) body
  pure (T.TLet (T.Decl fresh definition) (S.abstractTypeBody [T.typeName fresh] result))
typeLet hint definition body = pure (T.TLet (T.Decl hint definition) body)

-- Application arguments are variables, even when their source is a literal.
isTypeVariable :: T.Type -> Bool
isTypeVariable T.TVar {} = True
isTypeVariable T.TBound {} = True
isTypeVariable _ = False

withVariable :: T.Type -> (T.Type -> Anf T.Type) -> Anf T.Type
withVariable source cont = withAtom source $ \value ->
  if isTypeVariable value then cont value else do
    fresh <- freshId
    body <- cont (T.TVar (T.typeName fresh))
    pure (T.TLet (T.Decl fresh value) (S.abstractTypeBody [T.typeName fresh] body))

isTypeAtom :: T.Type -> Bool
isTypeAtom t = case t of
  T.TUnit -> True
  T.TInt -> True
  T.TBool -> True
  T.TString -> True
  T.TTrue -> True
  T.TFalse -> True
  T.TLabel {} -> True
  T.TRecNil -> True
  T.TVar {} -> True
  T.TBound {} -> True
  T.TRecCons {} -> True
  T.TArrow {} -> True
  T.TRef {} -> True
  T.TCol {} -> True
  T.TLambda {} -> True
  T.PBIn {} -> True
  T.TAnn term _ -> isTypeAtom term
  T.TForall {} -> True
  _ -> False

-- Expression ANF
elaborateExpr :: T.Expr -> T.Expr
elaborateExpr e = State.evalState (toAnfExprM e) (S.allExprNames e)

-- This is ANF elaboration, not call-by-value evaluation or normalization.
toAnfExprM :: T.Expr -> Anf T.Expr
toAnfExprM expr = case expr of
  T.ELambda x body -> T.ELambda x <$> toAnfExprM body
  T.ETLambda a body -> T.ETLambda a <$> toAnfExprM body
  T.EApp e1 e2 -> do
    withAtomExpr e1 $ \e1' ->
      withVariableExpr e2 $ \e2' ->
        pure (T.EApp e1' e2')
  T.ENot e -> withAtomExpr e (pure . T.ENot)
  T.EStringConcat e1 e2 -> binaryExprAtoms T.EStringConcat e1 e2
  T.ETApp e t -> do
    withAtomExpr e $ \e' ->
      pure (T.ETApp e' (elaborate t))
  T.ELet x e1 e2 -> do
    e1' <- toAnfExprM e1
    e2' <- toAnfExprM e2
    termLet x e1' e2'
  T.ELetRec f t e1 e2 -> do
    e1' <- toAnfExprM e1
    e2' <- toAnfExprM e2
    pure (T.ELetRec f (elaborate t) e1' e2')
  T.ERecordCons l e1 e2 -> binaryExprAtoms (T.ERecordCons l) e1 e2
  T.EConcat e1 e2 -> binaryExprAtoms T.EConcat e1 e2
  T.EHead e -> withAtomExpr e (pure . T.EHead)
  T.EHeadLabel e -> withAtomExpr e (pure . T.EHeadLabel)
  T.ETail e -> withAtomExpr e (pure . T.ETail)
  T.ERef e -> withAtomExpr e (pure . T.ERef)
  T.ERefOf e -> withAtomExpr e (pure . T.ERefOf)
  T.EAssign e1 e2 -> binaryExprAtoms T.EAssign e1 e2
  T.EIf c e1 e2 -> do
    withAtomExpr c $ \c' -> do
      e1' <- toAnfExprM e1
      e2' <- toAnfExprM e2
      pure (T.EIf c' e1' e2')
  T.EAnn e t -> T.EAnn <$> toAnfExprM e <*> pure (elaborate t)
  _ -> pure expr

withAtomExpr :: T.Expr -> (T.Expr -> Anf T.Expr) -> Anf T.Expr
withAtomExpr src cont = do
  norm <- toAnfExprM src
  continueWithAtomExpr norm cont

continueWithAtomExpr :: T.Expr -> (T.Expr -> Anf T.Expr) -> Anf T.Expr
continueWithAtomExpr norm cont
  | isExprAtom norm = cont norm
continueWithAtomExpr (T.ELet x d body) cont = do
  fresh <- freshId
  let body' = S.openExprTerm (T.EVar (T.termName fresh)) body
  bodyRes <- continueWithAtomExpr body' cont
  pure (T.ELet fresh d (S.closeExprTerm (T.termName fresh) bodyRes))
continueWithAtomExpr norm cont = do
  fresh <- freshId
  body <- cont (T.EVar (T.termName fresh))
  pure (T.ELet fresh norm (S.closeExprTerm (T.termName fresh) body))

termLet :: T.Identifier -> T.Expr -> T.Expr -> Anf T.Expr
termLet hint (T.ELet _ definition inner) body = do
  fresh <- freshId
  result <- termLet hint (S.openExprTerm (T.EVar (T.termName fresh)) inner) body
  pure (T.ELet fresh definition (S.closeExprTerm (T.termName fresh) result))
termLet hint definition body = pure (T.ELet hint definition body)

isTermVariable :: T.Expr -> Bool
isTermVariable T.EVar {} = True
isTermVariable T.EBound {} = True
isTermVariable _ = False

withVariableExpr :: T.Expr -> (T.Expr -> Anf T.Expr) -> Anf T.Expr
withVariableExpr source cont = withAtomExpr source $ \value ->
  if isTermVariable value then cont value else do
    fresh <- freshId
    body <- cont (T.EVar (T.termName fresh))
    pure (T.ELet fresh value (S.closeExprTerm (T.termName fresh) body))

isExprAtom :: T.Expr -> Bool
isExprAtom expression = case expression of
  T.EUnit -> True
  T.EInteger {} -> True
  T.EBoolean {} -> True
  T.EString {} -> True
  T.EVar {} -> True
  T.EBound {} -> True
  T.ELabel {} -> True
  T.ERecordNil -> True
  T.ELambda {} -> True
  T.ETLambda {} -> True
  T.EAnn body _ -> isExprAtom body
  _ -> False

binaryExprAtoms :: (T.Expr -> T.Expr -> T.Expr) -> T.Expr -> T.Expr -> Anf T.Expr
binaryExprAtoms constructor left right =
  withAtomExpr left $ \left' ->
    withAtomExpr right $ \right' ->
      pure (constructor left' right')
