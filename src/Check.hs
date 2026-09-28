{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Public façade for kind checking, term checking, and validation.
module Check
  ( checkKind
  , synthKind
  , sub
  , checkRaw
  , synthRaw
  , validateTypeKind
  , validateInferredKind
  , checkTypeEquality
  , checkTypeEqualityWhnf
  , synthType
  , checkType
  ) where

import qualified ANF as A
import qualified Constraint as C
import qualified Context as Ctx
import qualified Data.Set as Set
import qualified EvalTy as Eval
import qualified Prims as P
import qualified Substitution as S
import qualified Types as T
import qualified WhnfEquality as W

-- -----------------------------------------------------------------------------
-- Bidirectional kind checking
-- -----------------------------------------------------------------------------

-- Kind-level quotation is structural and never evaluates executable syntax.
-- Administrative ANF lets are opened before crossing the predicate boundary;
-- the public typeToPred conversion continues to reject residual lets.
typeToPredicate :: Ctx.Context -> T.Type -> T.Pred
typeToPredicate _ = T.typeToPred . preparePredicateType

preparePredicateType :: T.Type -> T.Type
preparePredicateType (T.TLet (T.Decl _ definition) body) =
  preparePredicateType (S.substitute definition body)

preparePredicateType ty = T.mapTypeChildren preparePredicateType ty

checkRaw :: Ctx.Context -> T.Type -> T.Rkind -> C.Cstr
checkRaw ctx t k = checkKind ctx (A.elaborate t) k

synthRaw :: Ctx.Context -> T.Type -> (C.Cstr, T.Rkind)
synthRaw ctx t = synthKind ctx (A.elaborate t)

synthKind :: Ctx.Context -> T.Type -> (C.Cstr, T.Rkind)
-- [K-SYN-UNIT]  Gamma |- Unit => KType{v | v = Unit} ; true
synthKind _ T.TUnit = (C.cTrue, P.unitKind)

-- [K-SYN-INT]  Gamma |- Int => KType{v | v = Int} ; true
synthKind _ T.TInt = (C.cTrue, P.intKind)

-- [K-SYN-BOOL]  Gamma |- Bool => KType{v | v = Bool} ; true
synthKind _ T.TBool = (C.cTrue, P.boolKind)

-- [K-SYN-STRING]  Gamma |- String => KType{v | v = String} ; true
synthKind _ T.TString = (C.cTrue, P.stringKind)

-- [K-SYN-TRUE]  Gamma |- True => KBool{v | v = True} ; true
synthKind _ T.TTrue = (C.cTrue, P.trueKind)

-- [K-SYN-FALSE]  Gamma |- False => KBool{v | v = False} ; true
synthKind _ T.TFalse = (C.cTrue, P.falseKind)

-- [K-SYN-LABEL]  Gamma |- label(l) => KLabel{v | v = label(l)} ; true
synthKind _ (T.TLabel l) = (C.cTrue, P.labelKind l)

-- [K-SYN-VAR]  Gamma(a) = k
--              -----------------------------
--              Gamma |- a => self(a, k) ; true
synthKind ctx (T.TVar name) =
  case Ctx.lookupKind name ctx of
    Just k ->
      let kSelf = selfifyKind name k
      in (C.cTrue, kSelf)
    Nothing -> error ("type error: unbound type variable: " ++ T.nameText name)


-- Bound type variables are opened before this judgment; reaching one violates
-- the locally-closed representation invariant rather than selecting a rule.
synthKind _ (T.TBound idx) = error
  ("type error: unopened type index " ++ show idx ++ " in kind synthesis")

-- [K-SYN-ARROW]  Gamma |- A <= KType ; c1    Gamma |- B <= KType ; c2
--                -------------------------------------------------
--                Gamma |- A -> B => KFun{v | dom(v) = A /\ img(v) = B} ; c1 /\ c2
synthKind ctx (T.TArrow dom img) =
  let c1 = checkKind ctx dom (P.bTrue T.BKType)
      c2 = checkKind ctx img (P.bTrue T.BKType)
      !domain = typeToPredicate ctx dom
      !image = typeToPredicate ctx img
  in (C.cAnd [c1,c2], T.KBase T.BKFun (T.Refined "v"
    (T.PInterp2 T.BAnd
      (T.PInterp2 T.BEq (T.PInterp1 T.BDom (T.PBound 0)) domain)
      (T.PInterp2 T.BEq (T.PInterp1 T.BImg (T.PBound 0)) image))))

-- [K-SYN-RECORD-CONS]  Gamma |- l <= KLabel ; cL   Gamma |- A <= KType ; cA
--   Gamma |- R <= KRec{r | l notin labels(r)} ; cR
--   ----------------------------------------------------------------------
--   Gamma |- <l : A> @ R => KRec{v | v = <l : A> @ R /\ isRec(v)} ; cL /\ cA /\ cR
synthKind ctx (T.TRecCons l ty r) =
  let cL = checkKind ctx l (P.bTrue T.BKLabel)
      cTy = checkKind ctx ty (P.bTrue T.BKType)
      !label = typeToPredicate ctx l
      !field = typeToPredicate ctx ty
      !rest = typeToPredicate ctx r
      cR = checkKind ctx r (T.KBase T.BKRec (T.Refined "r"
        (T.PInterp1 T.BNot (T.PMember label (T.PLabSet (T.PBound 0))))))
  in (C.cAnd [cL,cTy,cR], T.KBase T.BKRec (T.Refined "v"
    (T.PInterp2 T.BAnd
      (T.PInterp2 T.BEq (T.PBound 0) (T.PRecCons label field rest))
      (T.PInterp1 T.BIsRec (T.PBound 0)))))

-- [K-SYN-RECORD-NIL]  Gamma |- <> => KRec{r | r = <> /\ empty(r)} ; true
synthKind _ T.TRecNil = (C.cTrue, T.KBase T.BKRec (T.Refined "r"
  (T.PInterp2 T.BAnd
    (T.PInterp2 T.BEq (T.PBound 0) T.PRecNil)
    (T.PInterp1 T.BEmpty (T.PBound 0)))))

-- [K-SYN-REF]  Gamma |- A <= KType ; c
--              ---------------------------------
--              Gamma |- Ref A => KRef{v | refOf(v) = A} ; c
synthKind ctx (T.TRef element) =
  let constraint = checkKind ctx element (P.bTrue T.BKType)
      !operand = typeToPredicate ctx element
  in (constraint, T.KBase T.BKRef (T.Refined "v"
    (T.PInterp2 T.BEq (T.PInterp1 T.BRefOf (T.PBound 0)) operand)))

-- [K-SYN-COL]  Gamma |- A <= KType ; c
--              ---------------------------------
--              Gamma |- Col A => KCol{v | colOf(v) = A} ; c
synthKind ctx (T.TCol element) =
  let constraint = checkKind ctx element (P.bTrue T.BKType)
      !operand = typeToPredicate ctx element
  in (constraint, T.KBase T.BKCol (T.Refined "v"
    (T.PInterp2 T.BEq (T.PInterp1 T.BColOf (T.PBound 0)) operand)))

-- [K-SYN-PRIM]  opKind(op) = k
--               ----------------
--               Gamma |- op => k ; true
synthKind _ (T.PBIn operation) = (C.cTrue, P.typeOpKind operation)

-- [K-SYN-FORALL]  Gamma, a:k |- T => k' ; c     termKind(k')
--   ----------------------------------------------------------------
--   Gamma |- forall a::k. T => KGen a:k. k' ; forall a:k. c
synthKind ctx (T.TForall hint domain body) =
  let n = T.typeName (S.freshName (hint : Ctx.contextFreshNames ctx ++
        S.allKindNames domain ++ S.allTypeNames body))
      extended = Ctx.addTypeVar n domain ctx
      (bodyConstraint, codomain) = synthKind extended (S.unabstractType n body)
      scoped = Ctx.implicationConstraint n domain bodyConstraint
  in if isAdmissibleUniversalKind codomain
    then (scoped, T.KGen hint domain (S.abstractKind n codomain))
    else error
      "type error: universal body kind cannot end in a dependent function kind (KPi)"

-- [K-SYN-APP]  Gamma |- F => Pi a:k. k' ; c1   Gamma |- x <= k ; c2
--              -----------------------------------------------------
--              Gamma |- F x => k'[a := x] ; c1 /\ c2
synthKind ctx (T.TApp fn arg) =
  let (c1, functionKind) = synthKind ctx fn
  in case functionKind of
    T.KPi _ domain codomain ->
      let c2 = checkKind ctx arg domain
          !result = S.substitute (preparePredicateType arg) codomain
      in (C.cAnd [c1,c2], result)
    _ -> error "type error: application requires function kind (Pi)"

-- [K-SYN-ANN]  Gamma |- T <= k ; c
--              ------------------------
--              Gamma |- (T :: k) => k ; c
synthKind ctx (T.TAnn t k) = (checkKind ctx t k, k)

-- No K-SYN-LAMBDA rule: unannotated type lambdas are checking-only.
synthKind _ (T.TLambda b _) = error
  ("type error: cannot synthesize kind for unannotated lambda " ++
    b ++ " (checking-only)")


synthKind _ t = error ("type error: cannot synthesize kind for: " ++ show t)

-- Universal bodies may produce base kinds or nested generalized kinds.
-- Ordinary dependent function kinds remain checking-only results.
isAdmissibleUniversalKind :: T.Rkind -> Bool
isAdmissibleUniversalKind T.KBase {} = True

isAdmissibleUniversalKind (T.KGen _ _ codomain) =
  isAdmissibleUniversalKind codomain

isAdmissibleUniversalKind T.KPi {} = False

checkKind :: Ctx.Context -> T.Type -> T.Rkind -> C.Cstr
-- [K-CHK-LAMBDA]  Gamma, a:k1 |- T <= k2 ; c
--   ------------------------------------------------
--   Gamma |- fun a -> T <= Pi a:k1. k2 ; forall a:k1. c
checkKind ctx (T.TLambda b body) (T.KPi _ dom cod) =
  let n = T.typeName b
      body' = S.unabstractType n body
      cod' = S.unabstractKind n cod
      ctxExt = Ctx.addTypeVar n dom ctx
      cBody = checkKind ctxExt body' cod'
  in Ctx.implicationConstraint n dom cBody

-- [K-CHK-IF]  Gamma |- P <= KBool ; cP   Gamma |- T <= k ; cT
--   Gamma |- F <= k ; cF     witness is fresh
--   ----------------------------------------------------------
--   Gamma |- if P then T else F <= k ; cP /\ (P => cT) /\ (not P => cF)
checkKind ctx (T.TIf c whenT whenF) kGoal =
  let cCond = checkKind ctx c (P.bTrue T.BKBool)
      guard = typeToPredicate ctx c
      c1 = checkKind ctx whenT kGoal
      c2 = checkKind ctx whenF kGoal
      witness = T.typeName (S.freshName (Ctx.contextFreshNames ctx ++
        S.freeVariables guard ++ S.freeVariables c1 ++ S.freeVariables c2))
      thenConstraint = Ctx.implicationConstraint witness
        (T.KBase T.BKType (T.Refined "guard" guard)) c1
      elseConstraint = Ctx.implicationConstraint witness
        (T.KBase T.BKType (T.Refined "guard" (T.PInterp1 T.BNot guard))) c2
  in C.cAnd [cCond, thenConstraint, elseConstraint]

-- [K-CHK-LET]  Gamma |- D => kD ; cD   Gamma, a:kD |- T <= k ; cT
--   ---------------------------------------------------------------
--   Gamma |- let a = D in T <= k ; cD /\ forall a:kD. cT
checkKind ctx (T.TLet (T.Decl b d) body) kGoal =
  let (c1, kD) = synthKind ctx d
      name = T.typeName b
      body' = S.unabstractType name body
      ctxExt = Ctx.addTypeVar name kD ctx
      c2 = checkKind ctxExt body' kGoal
      scoped = Ctx.implicationConstraint name kD c2
  in C.cAnd [c1, scoped]
-- we expect kD to be well formed
-- [K-CHK-REC]  Gamma, a:kD |- D <= kD ; cD   Gamma, a:kD |- T <= k ; cT
--   ----------------------------------------------------------------------
--   Gamma |- rec a :: kD = D in T <= k ; forall a:kD. (cD /\ cT)
checkKind ctx (T.TRec b (T.TAnn def kD) body) kGoal =
  let name = T.typeName b
      def' = S.unabstractType name def
      body' = S.unabstractType name body
      ctxExt = Ctx.addTypeVar name kD ctx
      c1 = checkKind ctxExt def' kD
      c2 = checkKind ctxExt body' kGoal
  in Ctx.implicationConstraint name kD (C.cAnd [c1, c2])

checkKind _ (T.TRec _ _ _) _ =
  error "type error: recursive type binding requires its own kind annotation"


-- [K-CHK-SUB]  Gamma |- T => k' ; c1   Gamma |- k' <: k ; c2
--              ------------------------------------------------
--              Gamma |- T <= k ; c1 /\ c2
checkKind ctx t kGoal =
  let (cSynth, kSynth) = synthKind ctx t
      cSub = sub ctx kSynth kGoal
  in C.cAnd [cSynth, cSub]

sub :: Ctx.Context -> T.Rkind -> T.Rkind -> C.Cstr
-- [K-SUB-BASE]  B1 <=base B2
--   ----------------------------------------------------------------
--   Gamma |- B1{v | p1} <: B2{w | p2} ; forall x:B1{v | p1}. p2[w := x]
sub ctx source@(T.KBase bk1 (T.Refined v1 p1))
    (T.KBase bk2 (T.Refined v2 p2))
  | not (T.baseSubkind bk1 bk2) =
      error ("type error: incompatible basic kinds: " ++ show bk1 ++
        " not subkind of " ++ show bk2)
  | p2 == T.PTrue = C.cTrue
  | otherwise =
      let preferred = T.typeName v1
          occupied = S.freeNames p1 ++ S.freeNames p2
          -- The paper uses the source binder directly, modulo implicit alpha
          -- renaming. Preserve that name unless it would capture a free use.
          name
            | T.TypeSymbol preferred `notElem` occupied = preferred
            | otherwise = T.typeName (S.freshName
                (v1 : v2 : Ctx.contextFreshNames ctx
                  ++ S.freeVariables p1 ++ S.freeVariables p2))
          conclusion = C.cPred (S.openPredicate (T.PVar name) p2)
      in Ctx.implicationConstraint name source conclusion

-- [K-SUB-PI]  Gamma |- k2 <: k1 ; c1
--   Gamma, a:k2 |- k1' <: k2' ; c2
--   -----------------------------------------------
--   Gamma |- Pi a:k1. k1' <: Pi a:k2. k2' ; c1 /\ forall a:k2. c2
sub ctx (T.KPi b1 dom1 cod1) (T.KPi b2 dom2 cod2) =
  let cDom = sub ctx dom2 dom1
      fresh = S.freshName
        (b1 : b2 : Ctx.contextFreshNames ctx ++ S.freeVariables dom1 ++ S.freeVariables dom2
          ++ S.freeVariables cod1 ++ S.freeVariables cod2)
      name = T.typeName fresh
      cod1' = S.unabstractKind name cod1
      cod2' = S.unabstractKind name cod2
      ctxExt = Ctx.addTypeVar name dom2 ctx
      cCod = sub ctxExt cod1' cod2'
      scoped = Ctx.implicationConstraint name dom2 cCod
  in C.cAnd [cDom, scoped]

-- [K-SUB-GEN]  Gamma |- k2 <: k1 ; c1
--   Gamma, a:k2 |- k1' <: k2' ; c2
--   -------------------------------------------------
--   Gamma |- KGen a:k1. k1' <: KGen a:k2. k2' ; c1 /\ forall a:k2. c2
sub ctx (T.KGen b1 dom1 cod1) (T.KGen b2 dom2 cod2) =
  let cDom = sub ctx dom2 dom1
      fresh = S.freshName
        (b1 : b2 : Ctx.contextFreshNames ctx ++ S.freeVariables dom1 ++ S.freeVariables dom2
          ++ S.freeVariables cod1 ++ S.freeVariables cod2)
      name = T.typeName fresh
      cod1' = S.unabstractKind name cod1
      cod2' = S.unabstractKind name cod2
      ctxExt = Ctx.addTypeVar name dom2 ctx
      cCod = sub ctxExt cod1' cod2'
      scoped = Ctx.implicationConstraint name dom2 cCod
  in C.cAnd [cDom, scoped]

-- [K-SUB-GEN-TYPE]  Gamma, a:k |- k' <: KType ; c
--   ------------------------------------------------
--   Gamma |- KGen a:k. k' <: KType ; forall a:k. c
sub ctx (T.KGen hint domain codomain)
    (T.KBase T.BKType (T.Refined _ T.PTrue)) =
  let fresh = S.freshName
        (hint : Ctx.contextFreshNames ctx ++
          S.allKindNames domain ++ S.allKindNames codomain)
      name = T.typeName fresh
      codomain' = S.unabstractKind name codomain
      ctxExt = Ctx.addTypeVar name domain ctx
      cBody = sub ctxExt codomain' (P.bTrue T.BKType)
  in Ctx.implicationConstraint name domain cBody

sub _ k1 k2 =
  error ("type error: incompatible kinds in subkinding: " ++
    show k1 ++ " and " ++ show k2)

-- Predicate operands may mention deliberately undeclared names. They must
-- remain free when a checker rule introduces a binder with a similar display
-- hint. Include classifier dependencies for nested kind obligations.
selfifyKind :: T.TypeName -> T.Rkind -> T.Rkind
selfifyKind x (T.KBase bk (T.Refined v p)) =
  T.KBase bk (T.Refined v
    (T.PInterp2 T.BAnd p
      (T.PInterp2 T.BEq (T.PBound 0) (T.PVar x))))
selfifyKind _ k = k

-- -----------------------------------------------------------------------------
-- Validated solver boundaries
-- -----------------------------------------------------------------------------

-- This is the kind/SMT boundary. Term rules receive no constraints from it.
validateTypeKind :: Ctx.Context -> T.Type -> T.Rkind -> IO T.Type
validateTypeKind ctx ty kind = do
  prove ctx (checkRaw ctx ty kind)
  pure ty

prove :: Ctx.Context -> C.Cstr -> IO ()
prove context constraint = C.validateConstraint
  (foldl
    (\body (name, kind) -> Ctx.implicationConstraint name kind body)
    constraint (Ctx.ctxProofBinders context))

validateInferredKind :: Ctx.Context -> T.Type -> IO T.Rkind
validateInferredKind ctx ty = do
  let (constraint, kind) = synthRaw ctx ty
  prove ctx constraint
  pure kind

-- Validate both inputs completely before evaluating either one. Conversion is
-- exactly alpha-equivalence of the resulting CBV values.
checkTypeEquality :: Ctx.Context -> T.Rkind -> T.Type -> T.Type -> IO ()
checkTypeEquality ctx kind left right = do
  _ <- validateTypeKind ctx left kind
  _ <- validateTypeKind ctx right kind
  evaluatedLeft <- Eval.evalTy left
  evaluatedRight <- Eval.evalTy right
  if T.alphaEq evaluatedLeft evaluatedRight
    then pure ()
    else error "invalid-kind error: evaluated types are not alpha-equivalent"

-- Experimental opt-in conversion. The default conversion above is unchanged.
checkTypeEqualityWhnf :: Ctx.Context -> T.Rkind -> T.Type -> T.Type -> IO ()
checkTypeEqualityWhnf ctx kind left right = do
  _ <- validateTypeKind ctx left kind
  _ <- validateTypeKind ctx right kind
  if W.structurallyEqual left right
    then pure ()
    else error "invalid-kind error: types are not structurally equal modulo WHNF"


-- -----------------------------------------------------------------------------
-- Bidirectional term checking
-- -----------------------------------------------------------------------------

-- Evaluation boundary --------------------------------------------------------

evalType :: Ctx.Context -> T.Type -> IO T.Type
evalType _ T.TUnit = pure T.TUnit

evalType _ T.TInt = pure T.TInt

evalType _ T.TBool = pure T.TBool

evalType _ T.TString = pure T.TString

evalType _ ty@T.TLabel {} = pure ty

evalType _ T.TRecNil = pure T.TRecNil

evalType _ ty@T.TVar {} = pure ty

evalType _ ty = Eval.evalTy ty

-- Synthesis ------------------------------------------------------------------

synthType :: Ctx.Context -> T.Expr -> IO T.Type
synthType ctx = synthTypeRaw ctx . A.elaborateExpr

-- Inputs to the raw judgments are in ANF. Every kind premise is validated at
-- the equation that generates it. Written types remain unchanged except at
-- full normalization required by eliminators, quotation-demanding construction,
-- and the normalized result of type application.
synthTypeRaw :: Ctx.Context -> T.Expr -> IO T.Type
-- [T-SYN-UNIT]  Gamma |- () => Unit
synthTypeRaw _ T.EUnit = pure T.TUnit

-- [T-SYN-INT]  Gamma |- n => Int
synthTypeRaw _ (T.EInteger _) = pure T.TInt

-- [T-SYN-BOOL]  Gamma |- b => Bool
synthTypeRaw _ (T.EBoolean _) = pure T.TBool

-- [T-SYN-STRING]  Gamma |- s => String
synthTypeRaw _ (T.EString _) = pure T.TString

-- [T-SYN-LABEL]  Gamma |- label(l) => label(l)
synthTypeRaw _ (T.ELabel label) = pure (T.TLabel label)

-- [T-SYN-VAR]  Gamma(x) = T
--              --------------
--              Gamma |- x => T
synthTypeRaw ctx (T.EVar name) = case Ctx.lookupTermVar name ctx of
    Just ty -> pure ty
    Nothing -> error ("type error: unbound term variable: " ++ T.nameText name)

-- Bound term variables are opened before synthesis; reaching one is an
-- invariant violation, not a typing rule with an implicit environment lookup.
synthTypeRaw _ (T.EBound index) = error
    ("type error: unopened term index " ++ show index ++ " in term synthesis")

-- [T-SYN-NOT]  Gamma |- e <= Bool
--              --------------------
--              Gamma |- not e => Bool
synthTypeRaw ctx (T.ENot value) = do
    checkTypeRaw ctx value T.TBool
    pure T.TBool

-- [T-SYN-STRING-CONCAT]  Gamma |- e1 <= String   Gamma |- e2 <= String
--   -------------------------------------------------------------------
--   Gamma |- e1 ++ e2 => String
synthTypeRaw ctx (T.EStringConcat left right) = do
    checkTypeRaw ctx left T.TString
    checkTypeRaw ctx right T.TString
    pure T.TString

-- [T-SYN-ANN]  valid(Gamma |- T : KType)   Gamma |- e <= T
--              --------------------------------------------
--              Gamma |- (e : T) => T
synthTypeRaw ctx (T.EAnn expression declared) = do
    _ <- validateTypeKind ctx declared (P.bTrue T.BKType)
    checkTypeRaw ctx expression declared
    pure declared

-- [T-SYN-APP]  Gamma |- f => F   F ⇓ A -> B   Gamma |- x <= A
--              ----------------------------------------
--              Gamma |- f x => B
synthTypeRaw ctx (T.EApp function argument) = do
    functionType <- synthTypeRaw ctx function
    evalType ctx functionType >>= \case
        T.TArrow domain codomain -> do
            checkTypeRaw ctx argument domain
            pure codomain
        _ -> error "type error: term application requires a concrete arrow type"

-- [T-SYN-TAPP]  Gamma |- f => F   F ⇓ forall a::k. B
--   valid(Gamma |- A : k)   A ⇓ A'   B[a := A'] ⇓ B'
--   ----------------------------------------------------------------
--   Gamma |- f [A] => B'
synthTypeRaw ctx (T.ETApp function argument) = do
    functionType <- synthTypeRaw ctx function
    evalType ctx functionType >>= \case
        T.TForall _ domain body -> do
            _ <- validateTypeKind ctx argument domain
            actual <- evalType ctx argument
            let result = S.substitute actual body
            evalType ctx result
        _ -> error "type error: type application requires a universal type"

-- [T-SYN-RECORD-NIL]  Gamma |- <> => RecNil
synthTypeRaw _ T.ERecordNil = pure T.TRecNil

-- [T-SYN-RECORD-CONS]  Gamma |- e => A   A ⇓ A'
--   Gamma |- r => R   R ⇓ R'
--   R' is a concrete spine   label(l) notin labels(R')
--   -----------------------------------------------
--   Gamma |- <l = e> @ r => <label(l) : A'> @ R'
synthTypeRaw ctx (T.ERecordCons label field rest) = do
    fieldType <- synthTypeRaw ctx field >>= evalType ctx
    restType <- synthTypeRaw ctx rest
    restValue <- evalType ctx restType
    let checkLabels :: T.Type -> IO T.Type
        checkLabels = \case
            T.TRecNil -> pure T.TRecNil
            T.TRecCons (T.TLabel existing) fieldType' tailType ->
                if existing == label
                    then error ("type error: duplicate record label: " ++ label)
                    else T.TRecCons (T.TLabel existing) fieldType'
                        <$> checkLabels tailType
            _ -> error "type error: record extension requires a concrete record type"
    checkedRest <- checkLabels restValue
    pure (T.TRecCons (T.TLabel label) fieldType checkedRest)

-- [T-SYN-CONCAT]  Gamma |- e1 => R1   R1 ⇓ R1'
--   Gamma |- e2 => R2   R2 ⇓ R2'
--   R1' and R2' are concrete disjoint record spines
--   ------------------------------------------------------
--   Gamma |- e1 @ e2 => append(R1', R2')
synthTypeRaw ctx (T.EConcat left right) = do
    leftType <- synthTypeRaw ctx left
    rightType <- synthTypeRaw ctx right
    leftValue <- evalType ctx leftType
    rightValue <- evalType ctx rightType
    let leftLabels = labels "left" leftValue
        rightLabels = labels "right" rightValue
    case firstOverlap leftLabels rightLabels of
        Just duplicate -> error ("type error: duplicate record label: " ++ duplicate)
        Nothing -> pure (appendRecords leftValue rightValue)
  where
    labels side ty = case recordLabels ty of
        Just result -> result
        Nothing -> error
            ("type error: record concatenation requires a concrete " ++
                side ++ " record type")

-- [T-SYN-HEAD]  Gamma |- e => R   R ⇓ <l : A> @ R'
--               -------------------------------
--               Gamma |- head(e) => A
synthTypeRaw ctx (T.EHead record) = do
    recordType <- synthTypeRaw ctx record
    evalType ctx recordType >>= \case
        T.TRecCons _ field _ -> pure field
        _ -> error "type error: head requires a concrete nonempty record type"

-- [T-SYN-HEAD-LABEL]  Gamma |- e => R   R ⇓ <l : A> @ R'
--   ---------------------------------------------
--   Gamma |- headLabel(e) => l
synthTypeRaw ctx (T.EHeadLabel record) = do
    recordType <- synthTypeRaw ctx record
    evalType ctx recordType >>= \case
        T.TRecCons label _ _ -> pure label
        _ -> error "type error: headLabel requires a concrete nonempty record type"

-- [T-SYN-TAIL]  Gamma |- e => R   R ⇓ <l : A> @ R'
--               -------------------------------
--               Gamma |- tail(e) => R'
synthTypeRaw ctx (T.ETail record) = do
    recordType <- synthTypeRaw ctx record
    evalType ctx recordType >>= \case
        T.TRecCons _ _ rest -> pure rest
        _ -> error "type error: tail requires a concrete nonempty record type"

-- [T-SYN-REF]  Gamma |- e => A   A ⇓ A'
--              -----------------------------------
--              Gamma |- ref e => Ref A'
synthTypeRaw ctx (T.ERef expression) = do
    elementType <- synthTypeRaw ctx expression >>= evalType ctx
    pure (T.TRef elementType)

-- [T-SYN-DEREF]  Gamma |- e => R   R ⇓ Ref A
--                --------------------
--                Gamma |- !e => A
synthTypeRaw ctx (T.ERefOf expression) = do
    referenceType <- synthTypeRaw ctx expression
    evalType ctx referenceType >>= \case
        T.TRef element -> pure element
        _ -> error "type error: dereference requires a concrete reference type"

-- [T-SYN-ASSIGN]  Gamma |- r => R   R ⇓ Ref A   Gamma |- e <= A
--                 --------------------------------------
--                 Gamma |- r := e => Unit
synthTypeRaw ctx (T.EAssign reference value) = do
    referenceType <- synthTypeRaw ctx reference
    evalType ctx referenceType >>= \case
        T.TRef element -> do
            checkTypeRaw ctx value element
            pure T.TUnit
        _ -> error "type error: assignment requires a concrete reference type"

-- No synthesis rule exists for the remaining (checking-only) term forms.
synthTypeRaw _ _ = error "type error: cannot synthesize a checking-only term"

recordLabels :: T.Type -> Maybe [T.Identifier]
recordLabels ty = case T.stripAnnotations ty of
    T.TRecNil -> Just []
    T.TRecCons (T.TLabel label) _ rest -> (label :) <$> recordLabels rest
    _ -> Nothing

firstOverlap :: [T.Identifier] -> [T.Identifier] -> Maybe T.Identifier
firstOverlap left right = go left
  where
    rightLabels = Set.fromList right

    go [] = Nothing

    go (label : rest)
        | Set.member label rightLabels = Just label
        | otherwise = go rest

-- The callers have already checked both arguments with recordLabels.  This
-- constructor-only append therefore returns the concrete record spine itself;
-- it never constructs a residual type-level concatenation.
appendRecords :: T.Type -> T.Type -> T.Type
appendRecords left right = case T.stripAnnotations left of
    T.TRecNil -> T.stripAnnotations right
    T.TRecCons label field rest ->
        T.TRecCons label field (appendRecords rest right)
    _ -> error
        "type error: record concatenation requires a concrete left record type"

-- Checking -------------------------------------------------------------------

checkType :: Ctx.Context -> T.Expr -> T.Type -> IO ()
checkType ctx expression expected =
    checkTypeRaw ctx (A.elaborateExpr expression) (A.elaborate expected)

-- The expected type is trusted and well formed.
checkTypeRaw :: Ctx.Context -> T.Expr -> T.Type -> IO ()
-- [T-CHK-LAMBDA]  T ⇓ A -> B   Gamma, x:A |- e[x] <= B
--                 ---------------------------------------------
--                 Gamma |- fun x -> e <= T
checkTypeRaw ctx (T.ELambda hint body) expected =
    evalType ctx expected >>= \case
        T.TArrow domain codomain -> do
            let name = T.termName hint
            checkTypeRaw (Ctx.addTermVar name domain ctx)
                (S.openExprTerm (T.EVar name) body) codomain
        _ -> error "type error: lambda requires a concrete arrow type"

-- [T-CHK-TYPE-LAMBDA]  T ⇓ forall a::k. B
--   Gamma, a:k |- e[a] <= B[a]
--   ----------------------------------------------
--   Gamma |- funType a -> e <= T
checkTypeRaw ctx (T.ETLambda hint body) expected =
    evalType ctx expected >>= \case
        T.TForall _ domain result -> do
            let name = T.typeName hint
                extended = Ctx.addLocalTypeVar name domain ctx
            checkTypeRaw extended
                (S.unabstractExprType name body)
                (S.unabstractType name result)
        _ -> error "type error: type lambda requires a universal type"

-- [T-CHK-LET]  Gamma |- e1 => A   Gamma, x:A |- e2[x] <= T
--               ------------------------------------------
--               Gamma |- let x = e1 in e2 <= T
checkTypeRaw ctx (T.ELet hint definition body) expected = do
    definitionType <- synthTypeRaw ctx definition
    let name = T.termName hint
        extended = Ctx.addTermVar name definitionType ctx
    checkTypeRaw extended
        (S.openExprTerm (T.EVar name) body) expected

-- [T-CHK-LETREC]  valid(Gamma |- A : KType)   A ⇓ A'
--   Gamma, f:A |- e1[f] <= A'   Gamma, f:A |- e2[f] <= T
--   -----------------------------------------------------
--   Gamma |- letrec f : A = e1 in e2 <= T
checkTypeRaw ctx (T.ELetRec hint declared definition body) expected = do
    _ <- validateTypeKind ctx declared (P.bTrue T.BKType)
    goal <- evalType ctx declared
    let name = T.termName hint
        extended = Ctx.addTermVar name declared ctx
        opened = S.openExprTerm (T.EVar name)
    checkTypeRaw extended (opened definition) goal
    checkTypeRaw extended (opened body) expected

-- [T-CHK-IF]  Gamma |- c <= Bool   Gamma |- e1 <= T   Gamma |- e2 <= T
--             ---------------------------------------------------------
--             Gamma |- if c then e1 else e2 <= T
checkTypeRaw ctx (T.EIf condition yes no) expected = do
    checkTypeRaw ctx condition T.TBool
    checkTypeRaw ctx yes expected
    checkTypeRaw ctx no expected

-- [T-CHK-SUB]  Gamma |- e => A   A ⇓ A'   T ⇓ T'
--   A' =alpha T'  or  Gamma |- A' <:term T'
--   ------------------------------------------------
--   Gamma |- e <= T
checkTypeRaw ctx expression expected = do
    inferred <- synthTypeRaw ctx expression
    actual <- evalType ctx inferred
    goal <- evalType ctx expected
    if T.alphaEq actual goal
        then pure ()
        else termSubtype ctx actual goal

-- Structural-alpha term subtyping -------------------------------------------

-- Failures retain both complete evaluated operands.
termSubtype :: Ctx.Context -> T.Type -> T.Type -> IO ()
termSubtype ctx actual expected = compareTypes ctx actual expected
  where
    mismatch = error ("subtype error: " ++ show actual ++
        " is not a subtype of " ++ show expected)

    -- [T-SUB-ARROW]  Gamma |- A2 <:term A1   Gamma |- B1 <:term B2
    --   ------------------------------------------------------------
    --   Gamma |- A1 -> B1 <:term A2 -> B2
    compareTypes environment (T.TArrow a b) (T.TArrow c d) = do
        compareTypes environment c a
        compareTypes environment b d

    -- [T-SUB-RECORD]  l =alpha m   Gamma |- A <:term C   Gamma |- R <:term S
    --   ----------------------------------------------------------------------
    --   Gamma |- <l : A> @ R <:term <m : C> @ S
    compareTypes environment (T.TRecCons l a b) (T.TRecCons m c d)
        | T.alphaEq l m = do
            compareTypes environment a c
            compareTypes environment b d

    -- [T-SUB-ALPHA]  A =alpha B
    --                ------------
    --                Gamma |- A <:term B
    -- Structural constructors recurse before this leaf rule so a late
    -- mismatch does not alpha-compare every remaining suffix repeatedly.
    compareTypes _ left right | T.alphaEq left right = pure ()

    -- [T-SUB-FORALL]  Gamma |- k2 <: k1   Gamma, a:k2 |- B1[a] <:term B2[a]
    --   ----------------------------------------------------------------------
    --   Gamma |- forall a::k1. B1 <:term forall a::k2. B2
    -- The result-classifier treatment remains an explicit follow-up item;
    -- the executable rule discharges the contravariant domain obligation here.
    compareTypes environment (T.TForall h a b) (T.TForall i c d) = do
        let domain = sub environment c a
        prove environment domain
        let name = T.typeName (S.freshName
                (h : i : Ctx.contextFreshNames environment ++
                    S.allTypeNames actual ++ S.allTypeNames expected))
        compareTypes (Ctx.addLocalTypeVar name c environment)
            (S.unabstractType name b) (S.unabstractType name d)

    compareTypes _ _ _ = mismatch
