{-# LANGUAGE OverloadedStrings #-}

-- | Checker contexts, freshness, and proof scoping.
module Context
  ( Entry(..)
  , entryKind
  , Env
  , TermEnv
  , Context(..)
  , emptyContext
  , ctxEnv
  , ctxTermEnv
  , ctxProofBinders
  , addTypeVar
  , addTermVar
  , addLocalTypeVar
  , lookupKind
  , lookupTermVar
  , contextNames
  , contextFreshNames
  , implicationConstraint
  ) where

import qualified Constraint as C
import qualified Data.List as List
import qualified Substitution as S
import qualified Types as T

-- -----------------------------------------------------------------------------
-- Context storage
-- -----------------------------------------------------------------------------

newtype Entry
  = KindEntry T.Rkind
  deriving (Eq, Show)

entryKind :: Entry -> T.Rkind
entryKind (KindEntry kind) = kind

type Env = [(T.TypeName, Entry)]
type TermEnv = [(T.TermName, T.Type)]

data Context = Context
  { environment :: !Env
  , termEnvironment :: !TermEnv
  , proofBinders :: ![(T.TypeName, T.Rkind)]
  } deriving (Eq, Show)

emptyContext :: Context
emptyContext = Context [] [] []

ctxEnv :: Context -> Env
ctxEnv = environment

ctxTermEnv :: Context -> TermEnv
ctxTermEnv = termEnvironment

-- Only checker-owned lexical binders enter this scope. Ambient declarations
-- supplied through addTypeVar never close solver queries.
ctxProofBinders :: Context -> [(T.TypeName, T.Rkind)]
ctxProofBinders = proofBinders

-- -----------------------------------------------------------------------------
-- Extension and lookup
-- -----------------------------------------------------------------------------

addTypeVar :: T.TypeName -> T.Rkind -> Context -> Context
addTypeVar name kind context = context
  { environment = (name, KindEntry kind) : ctxEnv context }

addTermVar :: T.TermName -> T.Type -> Context -> Context
addTermVar name ty context = context
  { termEnvironment = (name, ty) : ctxTermEnv context }

addLocalTypeVar :: T.TypeName -> T.Rkind -> Context -> Context
addLocalTypeVar name kind context = (addTypeVar name kind context)
  { proofBinders = (name, kind) : proofBinders context }

lookupKind :: T.TypeName -> Context -> Maybe T.Rkind
lookupKind name context = go (ctxEnv context)
  where
    go [] = Nothing
    go ((entryName, entry) : rest)
      | entryName == name = Just (entryKind entry)
      | otherwise = go rest

lookupTermVar :: T.TermName -> Context -> Maybe T.Type
lookupTermVar name context = lookup name (ctxTermEnv context)

-- -----------------------------------------------------------------------------
-- Freshness
-- -----------------------------------------------------------------------------

contextNames :: Context -> [T.Identifier]
contextNames context =
  map (T.nameText . fst) (ctxEnv context) ++
  map (T.nameText . fst) (ctxTermEnv context)

-- Avoid capturing free dependencies in classifiers and term assumptions. This
-- does not validate entries or close obligations.
contextFreshNames :: Context -> [T.Identifier]
contextFreshNames context = List.nub
  (contextNames context ++
    concatMap (entryNames . snd) (ctxEnv context) ++
    concatMap (S.freeVariables . snd) (ctxTermEnv context) ++
    concatMap proofNames (ctxProofBinders context))
  where
    entryNames (KindEntry kind) = S.freeVariables kind
    proofNames (name, kind) = T.nameText name : S.freeVariables kind

-- -----------------------------------------------------------------------------
-- Proof scoping
-- -----------------------------------------------------------------------------

implicationConstraint
  :: T.TypeName -> T.Rkind -> C.Cstr -> C.Cstr
implicationConstraint name (T.KBase base (T.Refined _ predicate)) constraint =
  C.cAll
    (C.Bind (T.TypeSymbol name) base
      (S.openPredicate (T.PVar name) predicate))
    constraint
implicationConstraint name T.KGen {} constraint
  | T.TypeSymbol name `elem` S.freeNames constraint = error
      ("unsupported obligation: generalized parameter " ++ T.nameText name ++
        " remains in a first-order obligation")
  | otherwise = constraint
implicationConstraint name T.KPi {} constraint
  | T.TypeSymbol name `elem` S.freeNames constraint = error
      ("unsupported obligation: higher-order parameter " ++ T.nameText name ++
        " remains in a first-order obligation")
  | otherwise = constraint
