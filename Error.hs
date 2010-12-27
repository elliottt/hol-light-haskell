{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}

module Error where

import Data.Typeable (cast,Typeable)
import MonadLib


-- Errors ----------------------------------------------------------------------

class (Show e, Typeable e) => Error e where
  toError :: e -> SomeError
  toError  = SomeError
  fromError :: SomeError -> Maybe e
  fromError (SomeError se) = cast se

data SomeError = forall e. (Show e, Typeable e) => SomeError e
    deriving Typeable

instance Error SomeError where
  toError   = id
  fromError = Just

instance Show SomeError where
  showsPrec p (SomeError e)
    | p > 10    = showChar '(' . body . showChar ')'
    | otherwise = body
    where
    body = showString "SomeError " . showsPrec 11 e

raiseE :: (ExceptionM m SomeError, Error e) => e -> m a
raiseE  = raise . toError

tryE :: (RunExceptionM m SomeError, Error e) => m a -> m (Either e a)
tryE m = do
  res <- try m
  case res of
    Right a -> return (Right a)
    Left se ->
      case fromError se of
        Nothing -> raise se
        Just e  -> return (Left e)
