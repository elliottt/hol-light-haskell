{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Hol where

import Error

import Control.Applicative (Applicative)
import Control.DeepSeq (NFData(rnf))
import Data.List (find,delete,union)
import Data.Maybe (fromMaybe)
import Data.Typeable (Typeable,cast)
import MonadLib


-- HOL Monad -------------------------------------------------------------------

newtype Hol a = Hol
  { getHol :: StateT Context (ExceptionT SomeError IO) a
  } deriving (Functor,Applicative)

instance Monad Hol where
  return x = Hol (return x)
  m >>= k  = Hol (getHol m >>= getHol . k)
  fail msg = raiseE (Fail msg)

runHol :: Hol a -> IO (Either SomeError a)
runHol m = do
  res <- runExceptionT $ runStateT initialContext $ getHol m
  case res of
    Left se     -> return (Left se)
    Right (a,_) -> return (Right a)

instance StateM Hol Context where
  get = Hol   get
  set = Hol . set

instance ExceptionM Hol SomeError where
  raise = Hol . raise

instance RunExceptionM Hol SomeError where
  try = Hol . try . getHol


-- Exceptions ------------------------------------------------------------------

-- | What happens when you call fail from the Hol Monad.
data Fail = Fail String
    deriving (Show,Typeable)

instance Error Fail


-- | Variable name clash during typeInst.
data Clash = Clash Term
    deriving (Show,Typeable)

instance Error Clash


-- Types and Terms -------------------------------------------------------------

data Type
  = TVar String
  | TApp String [Type]
    deriving (Eq,Ord,Show)

instance NFData Type where
  rnf (TVar s)    = rnf s
  rnf (TApp s ts) = rnf s `seq` rnf ts

-- | Introduce an arrow type.
introArrow :: Type -> Type -> Type
introArrow a b = TApp "->" [a,b]

-- | Eliminate an arrow type.
destArrow :: Type -> Hol (Type,Type)
destArrow (TApp "->" [a,b]) = return (a,b)
destArrow _                 = fail "destArrow"

tya :: Type
tya  = TVar "a"

tybool :: Type
tybool  = TApp "bool" []

data Term
  = Var String Type
  | Con String Type
  | App Term Term
  | Abs Term Term
    deriving (Eq,Ord,Show)

instance NFData Term where
  rnf (Var s ty) = rnf s `seq` rnf ty
  rnf (Con s ty) = rnf s `seq` rnf ty
  rnf (App f x)  = rnf f `seq` rnf x
  rnf (Abs v b)  = rnf v `seq` rnf b

formatTerm :: Term -> String
formatTerm (Var n ty)  = n
formatTerm (Con n ty)  = n
formatTerm (App f x)   = formatTerm f ++ " " ++ formatTerm x
formatTerm (Abs n b) = '\\' : formatTerm n ++ '.' : formatTerm b

-- | Get the type of a term.
typeOf :: Term -> Hol Type
typeOf (Var _ ty) = return ty
typeOf (Con _ ty) = return ty
typeOf (Abs a b)  = do
  aty <- typeOf a
  introArrow aty `fmap` typeOf b
typeOf (App f x)  = do
  fty   <- typeOf f
  xty   <- typeOf x
  (a,b) <- destArrow fty
  unless (a == xty) (fail "typeOf")
  return b

varFreeIn :: Term -> Term -> Bool
varFreeIn v (Abs bv b) = v /= bv && varFreeIn v b
varFreeIn v (App f x)  = varFreeIn v f || varFreeIn v x
varFreeIn v v'         = v /= v'

frees :: Term -> [Term]
frees tm@Var{}     = [tm]
frees tm@Con{}     = []
frees tm@(Abs v b) = delete v (frees b)
frees tm@(App f x) = union (frees f) (frees x)

destVar :: Term -> Hol (String,Type)
destVar (Var s ty) = return (s,ty)
destVar _          = fail "destVar"

destApp :: Term -> Hol (Term,Term)
destApp (App f x) = return (f,x)
destApp _         = fail "destApp"

destAbs :: Term -> Hol (Term,Term)
destAbs (Abs v t) = return (v,t)
destAbs _         = fail "destAbs"


-- Substitution ----------------------------------------------------------------

newtype Subst a = Subst
  { getSubst :: [(a,a)]
  } deriving (Eq,Show)

emptySubst :: Subst a
emptySubst  = Subst []

nullSubst :: Subst a -> Bool
nullSubst (Subst u) = null u

extendSubst :: a -> a -> Subst a -> Subst a
extendSubst a a' (Subst u) = Subst ((a,a'):u)

anySubst :: (a -> a -> Bool) -> Subst a -> Bool
anySubst p (Subst u) = any (uncurry p) u

allSubst :: (a -> a -> Bool) -> Subst a -> Bool
allSubst p (Subst u) = all (uncurry p) u

-- | Filter the substitution.
filterSubst :: (a -> a -> Bool) -> Subst a -> Subst a
filterSubst p (Subst u) = Subst (filter (uncurry p) u)

lookupSubst :: Eq a => a -> Subst a -> Maybe a
lookupSubst n (Subst env) = snd `fmap` find p env
  where
  p (t,_) = n == t

lookupSubstR :: Eq a => a -> Subst a -> Maybe a
lookupSubstR n (Subst env) = fst `fmap` find p env
  where
  p (_,x) = n == x

type TypeSubst = Subst Type

typeSubst :: TypeSubst -> Type -> Type
typeSubst env (TApp c vs) = TApp c (map (typeSubst env) vs)
typeSubst env var         = fromMaybe var (lookupSubst var env)

type TermSubst = Subst Term

termSubst :: TermSubst -> Term -> Hol Term
termSubst env0
  | nullSubst env0 = return
  | otherwise      = body env0
  where
  body env v@(Var _ _) = return (fromMaybe v (lookupSubst v env))
  body env c@(Con _ _) = return c
  body env (App f x)   = App `fmap` body env f `ap` body env x
  body env t@(Abs v s) = do
    let env'        = filterSubst (\_ x -> x /= v) env
        needsRename = anySubst (\t x -> varFreeIn v t && varFreeIn x s) env'
    if nullSubst env'
       then return t
       else do
         s' <- body env' s
         if needsRename
            then do
              v' <- variant [s'] v
              Abs v' `fmap` body (extendSubst v' v env') s
            else return (Abs v s')

variant :: [Term] -> Term -> Hol Term
variant avoid v
  | not (any (varFreeIn v) avoid) = return v
  | otherwise                     =
    case v of
      Var s ty -> variant avoid (Var (s ++ "'") ty)
      _        -> fail "variant: not a variable"


-- Type Instantiation ----------------------------------------------------------

typeInst :: TypeSubst -> Term -> Hol Term
typeInst env0
  | nullSubst env0 = return
  | otherwise      = body emptySubst env0
  where
  checkClash env t t' =
    case lookupSubstR t env of
      Nothing -> return t'
      Just _  -> raiseE (Clash t')

  body e tye tm@(Var n ty) =
    let ty' = typeSubst tye ty
        tm' = Var n ty'
     in checkClash e tm tm'
  body e tye tm@(Con n ty) = return (Con n (typeSubst tye ty))
  body e tye tm@(App f x)  = App `fmap` body e tye f `ap` body e tye x
  body e tye tm@(Abs y t)  = do
    y'  <- body emptySubst tye y
    let e' = extendSubst y y' e
    res <- tryE (Abs y' `fmap` body e' tye t)
    case res of
      Right t'           -> return t'
      Left ex@(Clash w')
        | w' /= y'  -> raiseE ex
        | otherwise -> do
          ifrees <- mapM (body emptySubst tye) (frees t)
          y''    <- variant ifrees y'
          (n,_)  <- destVar y''
          (_,ty) <- destVar y
          let z = Var n ty
          t'     <- termSubst (extendSubst z y emptySubst) t
          body e tye (Abs z t')


-- Contexts --------------------------------------------------------------------

newtype Context = Context { constants :: [(String,Type)] }

initialContext :: Context
initialContext  = Context
  [ ("=", introArrow tya (introArrow tya tybool))
  ]

lookupConstType :: String -> Context -> Maybe Type
lookupConstType n = lookup n . constants

getConstType :: String -> Hol Type
getConstType n = do
  cxt <- get
  case lookupConstType n cxt of
    Nothing -> fail ("getConstType: " ++ n)
    Just ty -> return ty


-- Operations ------------------------------------------------------------------

mkConst :: String -> TypeSubst -> Hol Term
mkConst n tyenv = do
  cxt <- get
  ty  <- getConstType n
  return (Con n (typeSubst tyenv ty))
