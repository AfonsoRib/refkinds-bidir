module Support.Expected (expected, predicateOf) where
import Types
expected :: Show e => Either e a -> a
expected = either (error . show) id
predicateOf :: Type -> Pred
predicateOf = typeToPred
