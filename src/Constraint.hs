{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Constraint construction, SMT encoding, and solving.
module Constraint where

import qualified Control.Exception as Exception
import qualified Data.Aeson as Aeson
import qualified Data.List as List
import qualified Data.Monoid as Monoid
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LazyText
import qualified Data.Text.Lazy.Builder as Builder
import qualified GHC.Generics as Generics
import qualified System.Exit as Exit
import qualified System.Process as Process
import qualified System.Timeout as Timeout
import qualified Substitution as S
import qualified Types as T

-- -----------------------------------------------------------------------------
-- Constraint syntax and smart constructors
-- -----------------------------------------------------------------------------

data Bind = Bind !T.LogicName !T.BaseKind !T.Pred
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

data Cstr
  = CTrue
  | CPred !T.Pred
  | CAll !Bind !Cstr
  | CAnd ![Cstr]
  deriving (Eq, Ord, Show, Generics.Generic, Aeson.ToJSON, Aeson.FromJSON)

bind :: T.LogicName -> T.BaseKind -> T.Pred -> Bind
bind = Bind

cTrue :: Cstr
cTrue = CTrue

cPred :: T.Pred -> Cstr
cPred = CPred

cAnd :: [Cstr] -> Cstr
cAnd = CAnd

cAll :: Bind -> Cstr -> Cstr
cAll b c = CAll b c

-- An implication encoded with an unused witness must never capture a name
-- in either the guard or the obligation it scopes.
cGuard :: [T.Identifier] -> T.Pred -> Cstr -> Cstr
cGuard contextNames guard body =
  let name = T.freshKindBinder
        (contextNames ++ S.freeVariables guard ++ S.freeVariables body) "guard"
  in cAll (Bind (T.TypeSymbol (T.typeName name)) T.BKType guard) body

instance S.FreeVariables Cstr where
  freeNames CTrue = []
  freeNames (CPred p) = S.freeNames p
  freeNames (CAll (Bind n _ p) c) =
    filter (/= n) (S.freeNames p ++ S.freeNames c)
  freeNames (CAnd cs) = List.nub (concatMap S.freeNames cs)

-- Kept while existing clients migrate from the former Types-owned class.
instance T.FreeVariables Cstr where
  freeNames CTrue = []
  freeNames (CPred p) = T.freeNames p
  freeNames (CAll (Bind n _ p) c) =
    filter (/= n) (T.freeNames p ++ T.freeNames c)
  freeNames (CAnd cs) = List.nub (concatMap T.freeNames cs)

-- -----------------------------------------------------------------------------
-- SMT encoding and solver execution
-- -----------------------------------------------------------------------------

data SolverResult
  = Valid
  deriving (Eq, Ord, Show)

-- Translation records definedness separately from the value of an expression.
newtype CheckedConstraint = CheckedConstraint Text.Text
data BooleanCode = BooleanCode Text.Text Text.Text
data TypeCode = TypeCode Text.Text Text.Text
data LabelCode = LabelCode Text.Text Text.Text
data SetCode = SetCode Text.Text Text.Text

checkValid :: Cstr -> IO SolverResult
checkValid constraint = do
  valid <- solveConstraint constraint
  if valid then pure Valid else error "solver error: invalid obligation"

solveConstraint :: Cstr -> IO Bool
solveConstraint CTrue = pure True

solveConstraint constraint =
  let CheckedConstraint smt = prepareConstraint constraint
  in solveScript constraint smt

-- Catch transport failures outside the deadline, so the timeout signal is
-- handled by timeout itself and remains distinct from a process failure.
solveScript :: Cstr -> Text.Text -> IO Bool
solveScript constraint = runSolver options
  where
    options
      | usesConcat constraint = ["--pre-skolem-quant=on", "--pre-skolem-quant-nested"]
      -- Ordinary quantifier instantiation proves concrete record-spine
      -- obligations directly. Finite-model mode can spend the entire solver
      -- budget searching for a model of their negation.
      | concreteRecordFormation constraint = []
      | otherwise = ["--fmf-fun"]

-- Concrete record formation produces only freshness implications whose
-- record binder is pinned to a closed row literal. This deliberately narrow
-- classification changes solver search strategy, not the generated formula.
concreteRecordFormation :: Cstr -> Bool
concreteRecordFormation constraint = valid && sawRecord
  where
    (valid, sawRecord) = go constraint

    go CTrue = (True, False)
    go (CAnd constraints) =
      let results = map go constraints
      in (all fst results, any snd results)
    go (CAll (Bind name T.BKRec guard) body)
      | Just record <- pinnedClosedRecord name guard
      , Just label <- freshnessLabel name body
      , Just labels <- closedRecordLabels record
      , label `notElem` labels = (True, True)
    go _ = (False, False)

    pinnedClosedRecord name = firstPredicate $ \case
      T.PInterp2 T.BEq (T.PVar candidate) record ->
        if sameTypeName candidate name && closedRecord record
          then Just record else Nothing
      T.PInterp2 T.BEq record (T.PVar candidate) ->
        if sameTypeName candidate name && closedRecord record
          then Just record else Nothing
      _ -> Nothing

    freshnessLabel name (CPred predicate) = case predicate of
      T.PInterp1 T.BNot
          (T.PMember label (T.PLabSet (T.PVar candidate))) ->
        if sameTypeName candidate name && null (S.freeNames label)
          then Just label else Nothing
      _ -> Nothing
    freshnessLabel _ _ = Nothing

    closedRecord T.PRecNil = True
    closedRecord record@T.PRecCons {} = null (S.freeNames record)
    closedRecord _ = False

    closedRecordLabels T.PRecNil = Just []
    closedRecordLabels (T.PRecCons label _ rest) =
      (label :) <$> closedRecordLabels rest
    closedRecordLabels _ = Nothing

    sameTypeName candidate (T.TypeSymbol name) = candidate == name
    sameTypeName _ (T.RefSymbol _) = False

    firstPredicate predicate node = case predicate node of
      Just result -> Just result
      Nothing -> firstJust (map (firstPredicate predicate) (T.predChildren node))

    firstJust [] = Nothing
    firstJust (Just result : _) = Just result
    firstJust (Nothing : rest) = firstJust rest

runSolver :: [String] -> Text.Text -> IO Bool
runSolver options smt = do
  attempt <- Exception.try (Timeout.timeout solverTimeoutMicros
    (Process.readProcessWithExitCode "cvc5" (["--lang", "smt2"] ++ options) (Text.unpack smt)))
  case attempt of
    Left (ex :: Exception.IOException) ->
      error ("solver error: execution failed: " ++ show ex)
    Right Nothing -> error "solver error: timeout"
    Right (Just (Exit.ExitSuccess, out, err))
      | "unsat" `Text.isPrefixOf` Text.pack out -> pure True
      | "sat" `Text.isPrefixOf` Text.pack out -> pure False
      | "unknown" `Text.isPrefixOf` Text.pack out ->
          error ("solver error: unknown: " ++ out ++ err)
      | otherwise -> error ("solver error: unexpected response: " ++ out ++ err)
    Right (Just (Exit.ExitFailure _, out, err)) ->
      error ("solver error: " ++ out ++ err)

prepareConstraint :: Cstr -> CheckedConstraint
prepareConstraint c = CheckedConstraint (script c
  (LazyText.toStrict (Builder.toLazyText
    (encodeConstraintBuilder [] c))))

solverTimeoutMicros :: Int
solverTimeoutMicros = 5000000

validateConstraint :: Cstr -> IO ()
validateConstraint c = do
  valid <- solveConstraint c
  if valid then pure () else error "invalid-kind error: constraint is not valid"

toSmt :: Cstr -> Text.Text
toSmt c = let CheckedConstraint result = prepareConstraint c in result

script :: Cstr -> Text.Text -> Text.Text
script c body =
  Text.unlines
    ([ "(set-logic ALL)"
    , ""
    , "; Type Datatype"
    , "(declare-datatypes ((Type 0)) ("
    , "  ((TypeInt)"
    , "   (TypeBool)"
    , "   (TypeTrue)"
    , "   (TypeFalse)"
    , "   (TypeString)"
    , "   (TypeUnit)"
    , "   (TypeLab (labVal String))"
    , "   (TypeArrow (dom Type) (cod Type))"
    , "   (TypeRef (refof Type))"
    , "   (TypeCol (colof Type))"
    , "   (TypeRecEmpty)"
    , "   (TypeRecCons (headlb String) (head Type) (tail Type)))))"
    ]
    ++ recordDefinitions
    ++ concatDefinition
    ++
    [ ""
    , "; Negation of constraint obligation (testing validity via unsatisfiability)"
    , "(assert (not " <> body <> "))"
    , "(check-sat)"
    ])
  where
    recordDefinitions
      | usesRecordTheory c =
          [ ""
          , "; Recursive record functions"
          , "(define-fun-rec labSet ((r Type)) (Set String)"
          , "  (ite (is-TypeRecCons r)"
          , "       (set.union (set.singleton (headlb r)) (labSet (tail r)))"
          , "       (as set.empty (Set String))))"
          , ""
          , "(define-fun-rec isRec ((r Type)) Bool"
          , "  (ite (is-TypeRecEmpty r)"
          , "       true"
          , "       (and (is-TypeRecCons r)"
          , "            (not (set.member (headlb r) (labSet (tail r))))"
          , "            (isRec (tail r)))))"
          ]
      | otherwise = []
    concatDefinition
      | usesConcat c =
          [ ""
          , "(define-fun-rec recConcat ((r1 Type) (r2 Type)) Type"
          , "  (ite (is-TypeRecCons r1)"
          , "       (TypeRecCons (headlb r1) (head r1) (recConcat (tail r1) r2))"
          , "       r2))"
          ]
      | otherwise = []

usesRecordTheory :: Cstr -> Bool
usesRecordTheory = anyConstraint recordBase recordNode
  where
    recordBase T.BKType = True
    recordBase T.BKRec = True
    recordBase _ = False
    recordNode p = case p of
      T.PRecCons {} -> True
      T.PInterp1 operation _ -> recordOperation operation
      T.PInterp2 operation _ _ -> recordOperation operation
      T.PLabSet {} -> True
      _ -> False
    recordOperation operation = operation `elem`
      [T.BIsRec, T.BHead, T.BHeadLabel, T.BTail, T.BConcat]

usesConcat :: Cstr -> Bool
usesConcat = anyConstraint (const False) (\p -> case p of
  T.PInterp2 T.BConcat _ _ -> True
  _ -> False)

anyConstraint :: (T.BaseKind -> Bool) -> (T.Pred -> Bool) -> Cstr -> Bool
anyConstraint base node = go
  where
    predicate = Monoid.getAny . T.foldMapPred (Monoid.Any . node)
    go CTrue = False
    go (CPred p) = predicate p
    go (CAnd cs) = any go cs
    go (CAll (Bind _ k p) c) = base k || predicate p || go c

type LogicalEnv = [T.LogicName]

-- Binder guards must themselves be defined under base membership. Their truth
-- scopes the conclusion; an undefined guard cannot make a proof vacuous.
encodeConstraint :: LogicalEnv -> Cstr -> Text.Text
encodeConstraint environment constraint =
  LazyText.toStrict (Builder.toLazyText
    (encodeConstraintBuilder environment constraint))

encodeConstraintBuilder :: LogicalEnv -> Cstr -> Builder.Builder
encodeConstraintBuilder _ CTrue = Builder.fromText "true"
encodeConstraintBuilder env (CPred p) =
  let BooleanCode defined truth = encodeFormula env p
  in Builder.fromText (conjoin [defined, truth])
encodeConstraintBuilder env (CAnd cs) =
  builderConjoin (map (encodeConstraintBuilder env) cs)
encodeConstraintBuilder env (CAll (Bind n bk p) body) =
  let scoped = n : env
      BooleanCode defined guard = encodeFormula scoped p
      result = encodeConstraintBuilder scoped body
      text = Builder.fromText
      implication = builderApp "=>"
        [ text (baseKindCond bk (smtId n))
        , builderConjoin
            [ text defined
            , builderApp "=>" [text guard, result]
            ]
        ]
  in text "(forall ((" <> text (smtId n) <> text " Type)) " <>
    implication <> text ")"

builderConjoin :: [Builder.Builder] -> Builder.Builder
builderConjoin [] = Builder.fromText "true"
builderConjoin parts = builderApp "and" parts

builderApp :: Text.Text -> [Builder.Builder] -> Builder.Builder
builderApp operation arguments =
  Builder.fromText "(" <> Builder.fromText operation <>
    foldMap (Builder.fromText " " <>) arguments <> Builder.fromText ")"

-- Preserve the generated Boolean structure. CVC5 owns logical simplification;
-- the encoder only supplies the SMT identity for an empty conjunction.
conjoin :: [Text.Text] -> Text.Text
conjoin [] = "true"
conjoin parts = "(" <> Text.unwords ("and" : parts) <> ")"

app :: Text.Text -> [Text.Text] -> Text.Text
app op args = "(" <> Text.unwords (op : args) <> ")"

baseKindCond :: T.BaseKind -> Text.Text -> Text.Text
-- Write the union as a constructor case so recursive record validity is only
-- queried on cons cells. Empty records satisfy isRec by its base equation.
-- This is the same union, but avoids unguarded recursive calls obstructing
-- CVC5's countermodel search on unrelated constructors.
baseKindCond T.BKType v = app "ite"
  [app "is-TypeRecCons" [v], app "isRec" [v],
   app "or" (map (\constructor -> app ("is-" <> constructor) [v])
     ["TypeInt", "TypeBool", "TypeTrue", "TypeFalse", "TypeString", "TypeUnit",
      "TypeLab", "TypeArrow", "TypeRef", "TypeCol", "TypeRecEmpty"])]
baseKindCond T.BKBool v = app "or" [app "=" [v,"TypeTrue"],app "=" [v,"TypeFalse"]]
baseKindCond T.BKLabel v = app "is-TypeLab" [v]
baseKindCond T.BKRec v = app "isRec" [v]
baseKindCond T.BKFun v = app "is-TypeArrow" [v]
baseKindCond T.BKRef v = app "is-TypeRef" [v]
baseKindCond T.BKCol v = app "is-TypeCol" [v]

encodeFormula :: LogicalEnv -> T.Pred -> BooleanCode
encodeFormula env predicate = case predicate of
  T.PTrue -> BooleanCode "true" "true"
  T.PFalse -> BooleanCode "true" "false"
  T.PInterp1 T.BNot p ->
    let BooleanCode d p' = encodeFormula env p
    in BooleanCode d (app "not" [p'])
  T.PInterp2 T.BAnd p q -> ordered "and" id p q
  T.PInterp2 T.BOr p q -> ordered "or" (\p' -> app "not" [p']) p q
  T.PInterp2 T.BEq (p@T.PLabSet {}) (q@T.PLabSet {}) -> sets "=" p q
  T.PInterp2 T.BEq p q ->
    let TypeCode dp p' = encodeType env p
        TypeCode dq q' = encodeType env q
    in BooleanCode (conjoin [dp,dq]) (app "=" [p',q'])
  T.PSubset p q -> sets "set.subset" p q
  T.PApart p q ->
    let SetCode dp p' = encodeSet env p
        SetCode dq q' = encodeSet env q
    in BooleanCode (conjoin [dp,dq])
      (app "=" [app "set.inter" [p',q'],emptySet])
  T.PMember p q ->
    let LabelCode dp p' = encodeLabel env p
        SetCode dq q' = encodeSet env q
    in BooleanCode (conjoin [dp,dq]) (app "set.member" [p',q'])
  T.PInterp1 T.BEmpty p ->
    let TypeCode d p' = encodeType env p
    in BooleanCode d (app "is-TypeRecEmpty" [p'])
  T.PInterp1 operation _
    | T.typeOpArity operation /= 1 -> arityMismatch operation 1
  T.PInterp2 operation _ _
    | T.typeOpArity operation /= 2 -> arityMismatch operation 2
  T.PInterp1 T.BIsRec p -> membership p T.BKRec
  p ->
    let TypeCode d p' = encodeType env p
    in BooleanCode (conjoin [d,baseKindCond T.BKBool p'])
      (app "=" [p',"TypeTrue"])
  where
    ordered op guard p q =
      let BooleanCode dp p' = encodeFormula env p
          BooleanCode dq q' = encodeFormula env q
      in BooleanCode (conjoin [dp,app "=>" [guard p',dq]])
        (app op [p',q'])
    sets op p q =
      let SetCode dp p' = encodeSet env p
          SetCode dq q' = encodeSet env q
      in BooleanCode (conjoin [dp,dq]) (app op [p',q'])
    membership p k =
      let TypeCode d p' = encodeType env p
      in BooleanCode d (baseKindCond k p')

-- Type-level Boolean results use explicit datatype constructors. Definedness
-- is transported alongside them, including through quoted Boolean operands.
encodeType :: LogicalEnv -> T.Pred -> TypeCode
encodeType env ty = case ty of
  T.PInt -> literal "TypeInt"
  T.PBool -> literal "TypeBool"
  T.PString -> literal "TypeString"
  T.PUnit -> literal "TypeUnit"
  T.PTrue -> literal "TypeTrue"
  T.PFalse -> literal "TypeFalse"
  T.PLabel l -> literal (app "TypeLab" [smtString l])
  T.PVar n -> literal (smtId (T.TypeSymbol n))
  T.PRefVar n -> literal (smtId (T.RefSymbol n))
  T.PTypeBound _ -> encodingFailure "unopened bound index at SMT encoding boundary"
  T.PBound _ -> encodingFailure "unopened refinement index at SMT encoding boundary"
  T.PRecNil -> literal "TypeRecEmpty"
  T.PRecCons l t r ->
    let LabelCode dl label = encodeLabel env l
        TypeCode dt field = encodeType env t
        TypeCode dr rest = encodeType env r
    in TypeCode (conjoin [dl,dt,dr,app "isRec" [rest],
      app "not" [app "set.member" [label,app "labSet" [rest]]]])
      (app "TypeRecCons" [label,field,rest])
  T.PArrow a b -> binary "TypeArrow" a b
  T.PRef a -> unary "TypeRef" a
  T.PCol a -> unary "TypeCol" a
  T.PInterp1 T.BRefOf a -> selector "refof" (baseKindCond T.BKRef) a
  T.PInterp1 T.BColOf a -> selector "colof" (baseKindCond T.BKCol) a
  T.PInterp1 T.BHead a -> selector "head" recordGuard a
  T.PInterp1 T.BHeadLabel a ->
    let TypeCode d r = selector "headlb" recordGuard a
    in TypeCode d (app "TypeLab" [r])
  T.PInterp1 T.BTail a -> selector "tail" recordGuard a
  T.PInterp1 T.BDom a -> selector "dom" (baseKindCond T.BKFun) a
  T.PInterp1 T.BImg a -> selector "cod" (baseKindCond T.BKFun) a
  T.PInterp2 T.BConcat a b ->
    let TypeCode da a' = encodeType env a
        TypeCode db b' = encodeType env b
    in TypeCode (conjoin [da,db,app "isRec" [a'],app "isRec" [b'],
      app "=" [app "set.inter" [app "labSet" [a'],app "labSet" [b']],emptySet]])
      (app "recConcat" [a',b'])
  T.PLabSet _ ->
    encodingFailure "label sets cannot be used as Type operands"
  T.PInterp1 operation _
    | T.typeOpArity operation /= 1 -> arityMismatch operation 1
  T.PInterp2 operation _ _
    | T.typeOpArity operation /= 2 -> arityMismatch operation 2
  _ ->
    let BooleanCode d b = encodeFormula env ty
    in TypeCode d (app "ite" [b,"TypeTrue","TypeFalse"])
  where
    literal = TypeCode "true"
    recordGuard r = conjoin [app "is-TypeRecCons" [r],app "isRec" [r]]
    unary op a =
      let TypeCode d a' = encodeType env a
      in TypeCode d (app op [a'])
    binary op a b =
      let TypeCode da a' = encodeType env a
          TypeCode db b' = encodeType env b
      in TypeCode (conjoin [da,db]) (app op [a',b'])
    selector op guard a =
      let TypeCode d a' = encodeType env a
      in TypeCode (conjoin [d,guard a']) (app op [a'])

encodeLabel :: LogicalEnv -> T.Pred -> LabelCode
encodeLabel env ty =
  let TypeCode d t = encodeType env ty
  in LabelCode (conjoin [d,baseKindCond T.BKLabel t]) (app "labVal" [t])

encodeSet :: LogicalEnv -> T.Pred -> SetCode
encodeSet env (T.PLabSet record) =
  let TypeCode d t = encodeType env record
  in SetCode (conjoin [d,app "isRec" [t]]) (app "labSet" [t])

encodeSet _ _ = encodingFailure "expected a label-set predicate"

arityMismatch :: T.TypeOp -> Int -> a
arityMismatch operation actual = encodingFailure
  ("operator " ++ show operation ++ " expects " ++
    show (T.typeOpArity operation) ++ " operands, got " ++
    show actual)

encodingFailure :: String -> a
encodingFailure message = error ("predicate encoding error: " ++ message)

emptySet :: Text.Text
emptySet = "(as set.empty (Set String))"

smtString :: String -> Text.Text
smtString s = "\"" <> Text.replace "\"" "\"\"" (Text.pack s) <> "\""

-- Encode every character, including underscores, so distinct source names can
-- never collide after escaping.
smtId :: T.LogicName -> Text.Text
smtId name = prefix <>
  Text.concat ["_" <> Text.pack (show (fromEnum c)) | c <- T.logicNameText name]
  where prefix = case name of T.TypeSymbol _ -> "var"; T.RefSymbol _ -> "refvar"
