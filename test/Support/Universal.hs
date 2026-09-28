module Support.Universal (forallType) where

import Types

-- Universal values carry their binder domain directly.
forallType :: Identifier -> Rkind -> Type -> Type
forallType = TForall
