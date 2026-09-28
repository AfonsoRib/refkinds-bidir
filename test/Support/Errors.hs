module Support.Errors
  ( assertError
  , assertErrorContaining
  , assertPureError
  , captureError
  ) where

import qualified Control.Exception as Exception
import qualified Data.Char as Char
import qualified Data.List as List
import qualified Test.Tasty.HUnit as HUnit

captureError :: IO value -> IO (Either String value)
captureError action = do
  result <- Exception.try action
  pure $ case result of
    Left failure -> Left (Exception.displayException
      (failure :: Exception.ErrorCall))
    Right value -> Right value

assertError :: Show value => IO value -> HUnit.Assertion
assertError action = captureError (forceShown action) >>= \result -> case result of
  Left _ -> pure ()
  Right _ -> HUnit.assertFailure "expected ErrorCall"

assertErrorContaining :: Show value => String -> IO value -> HUnit.Assertion
assertErrorContaining fragment action = captureError (forceShown action) >>= \result ->
  case result of
    Left message -> HUnit.assertBool
      ("expected error containing " ++ show fragment ++ ", got " ++ show message)
      (map Char.toLower fragment `List.isInfixOf` map Char.toLower message)
    Right _ -> HUnit.assertFailure
      ("expected ErrorCall containing " ++ show fragment)

assertPureError :: Show value => value -> HUnit.Assertion
assertPureError = assertError . pure

forceShown :: Show value => IO value -> IO Int
forceShown action = action >>= Exception.evaluate . length . show
