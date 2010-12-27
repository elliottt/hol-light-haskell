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

instance StateM Hol Context where
  get = Hol   get
  set = Hol . set

instance ExceptionM Hol SomeError where
  raise = Hol . raise

instance RunExceptionM Hol SomeError where
  try = Hol . try . getHol

instance BaseM Hol IO where
  inBase = Hol . inBase

runHol :: Hol a -> IO (Either SomeError a)
runHol m = do
  res <- runExceptionT $ runStateT initialContext $ getHol m
  case res of
    Left se     -> return (Left se)
    Right (a,_) -> return (Right a)


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


-- | Lift haskell values into their term representation.
class TermRep a where
  termRep  :: a -> Hol Term
  termType :: a -> Hol Type

instance TermRep Term where
  termRep  = return
  termType = typeOf

instance TermRep Bool where
  termRep True  = return (Con "T" tybool)
  termRep False = return (Con "F" tybool)
  termType _    = return tybool


-- | Assumptions
newtype Assumps a = Assumps
  { getAssumps :: [a]
  } deriving (Eq,NFData)

emptyAssumps :: Assumps a
emptyAssumps  = Assumps []

unconsAssumps :: Assumps a -> Maybe (a,Assumps a)
unconsAssumps (Assumps (a:as)) = Just (a,Assumps as)
unconsAssumps _                = Nothing

consAssumps :: a -> Assumps a -> Assumps a
consAssumps a (Assumps as) = Assumps (a:as)

merge :: (NFData a, Ord a) => Assumps a -> Assumps a -> Assumps a
merge (Assumps as0) (Assumps bs0) = Assumps (loop as0 bs0)
  where
  loop as       [] = as
  loop []       bs = bs
  loop l@(a:as) r@(b:bs)
    | a == b    = a : loop as bs
    | a < b     = a : loop as r
    | otherwise = b : loop l  bs


termRemove :: (NFData a, Ord a) => a -> Assumps a -> Assumps a
termRemove a (Assumps as) = Assumps (loop as)
  where
  loop [] = []
  loop l@(x:xs)
    | a > x     = x : loop xs
    | a == x    = xs
    | otherwise = l

termImage :: (NFData a, Ord a) => (a -> Hol a) -> Assumps a -> Hol (Assumps a)
termImage f as =
  case unconsAssumps as of
    Nothing     -> return emptyAssumps
    Just (h,tl) -> do
      h'  <- f h
      tl' <- termImage f tl
      if h == h' && tl == tl'
         then return as
         else return (merge (consAssumps h' emptyAssumps) tl')

-- | Sequents.
data Sequent a c = Sequent
  { seqAssumps :: Assumps a
  , seqConseq  :: c
  }

instance (NFData a, NFData c) => NFData (Sequent a c) where
  rnf (Sequent as c) = rnf as `seq` rnf c

type Theorem = Sequent Term Term

printTheorem :: Theorem -> IO ()
printTheorem (Sequent as c) = putStrLn (unlines (fas ++ [l,fc]))
  where
  fas = map formatTerm (getAssumps as)
  fc  = formatTerm c
  l   = replicate (length (maximum (fc:fas))) '='

introEq :: Term -> Term -> Hol Term
introEq x y = do
  ty <- typeOf x
  return (App (App (Con "=" (introArrow ty (introArrow ty tybool))) x) y)

destEq :: Term -> Hol (Term,Term)
destEq t = do
  (r,y) <- destApp t
  (_,x) <- destApp r
  return (x,y)

-- | REFL
refl :: TermRep a => a -> Hol Theorem
refl = refl' <=< termRep

refl' :: Term -> Hol Theorem
refl' t = Sequent emptyAssumps `fmap` introEq t t

-- | TRANS
trans :: Theorem -> Theorem -> Hol Theorem
trans ab bc = do
  (a,b)  <- destEq (seqConseq ab)
  (b',c) <- destEq (seqConseq bc)
  unless (b == b') (fail "trans")
  eq'    <- introEq a c
  return (Sequent (merge (seqAssumps ab) (seqAssumps bc)) eq')

-- | MK_COMB
apply :: Theorem -> Theorem -> Hol Theorem
apply f x = do
  (s,t) <- destEq (seqConseq f)
  (u,v) <- destEq (seqConseq x)
  (a,b) <- destArrow =<< typeOf s
  a'    <- typeOf u
  unless (a == a') (fail "apply: types to not agree")
  Sequent (merge (seqAssumps f) (seqAssumps x))
      `fmap` introEq (App s u) (App t v)

-- | ABS
abstract :: TermRep a => a -> Theorem -> Hol Theorem
abstract a t = do
  tm <- termRep a
  abstract' tm t

abstract' :: Term -> Theorem -> Hol Theorem
abstract' v t = do
  _     <- destVar v
  (l,r) <- destEq (seqConseq t)
  Sequent (seqAssumps t) `fmap` introEq (Abs v l) (Abs v r)

-- | BETA
beta :: Term -> Hol Theorem
beta t = do
  (f,x) <- destApp t
  (v,b) <- destAbs f
  unless (v == x) (fail "beta: not a trivial beta-redex")
  Sequent emptyAssumps `fmap` introEq t b

-- | ASSUME
assume :: TermRep a => a -> Hol Theorem
assume  = assume' <=< termRep

assume' :: Term -> Hol Theorem
assume' t = do
  ty <- typeOf t
  unless (ty == tybool) (fail "assume: not a proposition")
  return (Sequent (Assumps [t]) t)

-- | EQ_MP
eqMP :: Theorem -> Theorem -> Hol Theorem
eqMP eq c = do
  (l,r) <- destApp (seqConseq eq)
  unless (l == seqConseq c) (fail "eqMP")
  return (Sequent (merge (seqAssumps eq) (seqAssumps c)) r)

-- | DEDUCT_ANTISYM_RULE
deductAntisymRule :: Theorem -> Theorem -> Hol Theorem
deductAntisymRule a b = do
  let aas = termRemove (seqConseq b) (seqAssumps a)
      bas = termRemove (seqConseq a) (seqAssumps b)
  eq <- introEq (seqConseq a) (seqConseq b)
  return (Sequent (merge aas bas) eq)

-- | INST_TYPE
instType :: TypeSubst -> Theorem -> Hol Theorem
instType theta t =
  Sequent `fmap` termImage instFn (seqAssumps t) `ap` instFn (seqConseq t)
  where
  instFn = typeInst theta

-- | INST_TERM
instTerm :: TermSubst -> Theorem -> Hol Theorem
instTerm theta t =
  Sequent `fmap` termImage instFn (seqAssumps t) `ap` instFn (seqConseq t)
  where
  instFn = termSubst theta
