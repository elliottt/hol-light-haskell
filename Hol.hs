{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Hol where

import Error
import Hol.Assumps
import Hol.Subst
import Hol.Term
import Hol.Type

import Control.Applicative (Applicative)
import Control.Concurrent
    (MVar,newMVar,takeMVar,putMVar,modifyMVar,readMVar,modifyMVar_)
import Control.DeepSeq (NFData(rnf))
import Data.List (find,delete,union,nub)
import Data.Maybe (fromMaybe,isJust)
import Data.Typeable (Typeable,cast)
import MonadLib
import qualified Data.Set as Set


-- HOL Monad -------------------------------------------------------------------

newtype Hol a = Hol
  { getHol :: ReaderT RO (ExceptionT SomeError IO) a
  } deriving (Functor,Applicative)

instance Monad Hol where
  return x = Hol (return x)
  m >>= k  = Hol (getHol m >>= getHol . k)
  fail msg = raiseE (Fail msg)

instance ExceptionM Hol SomeError where
  raise = Hol . raise

instance RunExceptionM Hol SomeError where
  try = Hol . try . getHol

instance BaseM Hol IO where
  inBase = Hol . inBase

runHol :: Hol a -> IO (Either SomeError a)
runHol m = do
  ro  <- initRO
  runExceptionT $ runReaderT ro $ getHol m


-- Environment -----------------------------------------------------------------

data RO = RO
  { roAxioms     :: MVar [Theorem]
  , roTermDefs   :: MVar [Theorem]
  , roTermConsts :: MVar [(String,Type)]
  , roTypes      :: MVar [(String,Int)]
  }

initRO :: IO RO
initRO  = RO
   `fmap` newMVar []             -- axioms
     `ap` newMVar []             -- term defs
     `ap` newMVar initTermConsts -- term consts
     `ap` newMVar initTypes      -- type airitys

initTermConsts :: [(String,Type)]
initTermConsts  =
  [ ("=", introArrow tya (introArrow tya tybool))
  ]

initTypes :: [(String,Int)]
initTypes  =
  [ ("bool", 0)
  , ("->", 2)
  ]

getTypes :: Hol [(String,Int)]
getTypes  = Hol $ do
  ro <- ask
  inBase (readMVar (roTypes ro))

getTypeArity :: String -> Hol Int
getTypeArity s = Hol $ do
  ro    <- ask
  types <- inBase (readMVar (roTypes ro))
  case lookup s types of
    Nothing -> fail ("getTypeArity: " ++ s ++ " not declared")
    Just a  -> return a

newType :: String -> Int -> Hol ()
newType n a = do
  types <- getTypes
  when (isJust (lookup n types))
    (fail ("newType: " ++ n ++ " already declared"))
  Hol $ do
    ro <- ask
    inBase (modifyMVar_ (roTypes ro) (\ts -> return ((n,a):ts)))

newAxiom :: Term -> Hol Theorem
newAxiom tm = do
  ty <- typeOf tm
  unless (ty == tybool) (fail "newAxiom: Not a proposition")
  ro <- Hol ask
  let thm = Sequent emptyAssumps tm
  inBase (modifyMVar (roAxioms ro) (\ axioms -> return (thm:axioms,thm)))

getAxioms :: Hol [Theorem]
getAxioms  = Hol $ do
  ro <- ask
  inBase (readMVar (roAxioms ro))

newConstant :: String -> Type -> Hol ()
newConstant n ty = do
  consts <- getConstants
  when (isJust (lookup n consts))
    (fail ("newConstant: constant " ++ n ++ " is already declared"))
  Hol $ do
    ro <- ask
    inBase (modifyMVar_ (roTermConsts ro) (\cs -> return ((n,ty):cs)))

getConstant :: String -> Hol Type
getConstant n = do
  ro     <- Hol ask
  consts <- inBase (readMVar (roTermConsts ro))
  case lookup n consts of
    Nothing -> fail ("getConstant: " ++ n ++ " not declared")
    Just ty -> return ty

getConstants :: Hol [(String,Type)]
getConstants  = Hol $ do
  ro <- ask
  inBase (readMVar (roTermConsts ro))

getDefinitions :: Hol [Theorem]
getDefinitions  = Hol $ do
  ro <- ask
  inBase (readMVar (roTermDefs ro))

newBasicDefinition :: Term -> Hol Theorem
newBasicDefinition tm = do
  (l,r)      <- destEq tm
  (cname,ty) <- destVar l
  unless (freesin [] r)
    (fail "newBasicDefinition: term not closed")
  unless (freeTypeVars r `Set.isSubsetOf` freeTypeVars ty)
    (fail "newBasicDefinition: type variables not reflected in constant")
  newConstant cname ty
  let c = Con cname ty
  eq <- introEq c r
  let thm = Sequent emptyAssumps eq
  Hol $ do
    ro <- ask
    inBase (modifyMVar (roTermDefs ro) (\defs -> return (thm:defs,thm)))


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

mkType :: String -> [Type] -> Hol Type
mkType op args = do
  arity <- getTypeArity op
    `onError` fail ("mkType: " ++ op ++ " is not defined")
  unless (arity == length args)
    (fail ("mkType: wrong number of arguments to " ++ op))
  return (TApp op args)

-- | Introduce an arrow type.
introArrow :: Type -> Type -> Type
introArrow a b = TApp "->" [a,b]

-- | Eliminate an arrow type.
destArrow :: Type -> Hol (Type,Type)
destArrow (TApp "->" [a,b]) = return (a,b)
destArrow _                 = fail "destArrow"

-- | Eliminate a type application.
destTApp :: Type -> Hol (String,[Type])
destTApp (TApp n ts) = return (n,ts)
destTApp _           = fail "destTApp"

-- | Eliminate a type variable.
destTVar :: Type -> Hol String
destTVar (TVar n) = return n
destTVar _        = fail "destTVar"

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

destVar :: Term -> Hol (String,Type)
destVar (Var s ty) = return (s,ty)
destVar _          = fail "destVar"

destApp :: Term -> Hol (Term,Term)
destApp (App f x) = return (f,x)
destApp _         = fail "destApp"

destAbs :: Term -> Hol (Term,Term)
destAbs (Abs v t) = return (v,t)
destAbs _         = fail "destAbs"

rator :: Term -> Hol Term
rator tm = fst `fmap` destApp tm
  `onError` fail "rator: not an application"

rand :: Term -> Hol Term
rand tm = snd `fmap` destApp tm
  `onError` fail "rand: not an application"

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


-- Substitution ----------------------------------------------------------------

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


-- Assumptions -----------------------------------------------------------------

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


-- Operations ------------------------------------------------------------------

-- | Sequents.
data Sequent a c = Sequent
  { seqAssumps :: Assumps a
  , seqConcl   :: c
  } deriving Show

instance (NFData a, NFData c) => NFData (Sequent a c) where
  rnf (Sequent as c) = rnf as `seq` rnf c

type Theorem = Sequent Term Term

destTheorem :: Theorem -> Hol (Assumps Term, Term)
destTheorem (Sequent as c) = return (as,c)

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
  (r,y) <- destApp t `onError` fail "destEq"
  (_,x) <- destApp r `onError` fail "destEq"
  return (x,y)

-- | REFL
refl :: TermRep a => a -> Hol Theorem
refl = refl' <=< termRep

refl' :: Term -> Hol Theorem
refl' t = Sequent emptyAssumps `fmap` introEq t t

-- | TRANS
trans :: Theorem -> Theorem -> Hol Theorem
trans ab bc = do
  (a,b)  <- destEq (seqConcl ab) `onError` fail "trans"
  (b',c) <- destEq (seqConcl bc) `onError` fail "trans"
  unless (b == b') (fail "trans")
  eq'    <- introEq a c
  return (Sequent (merge (seqAssumps ab) (seqAssumps bc)) eq')

-- | MK_COMB
apply :: Theorem -> Theorem -> Hol Theorem
apply f x = do
  (s,t) <- destEq (seqConcl f)
  (u,v) <- destEq (seqConcl x)
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
  (l,r) <- destEq (seqConcl t)
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
  (l,r) <- destApp (seqConcl eq)
  unless (l == seqConcl c) (fail "eqMP")
  return (Sequent (merge (seqAssumps eq) (seqAssumps c)) r)

-- | DEDUCT_ANTISYM_RULE
deductAntisymRule :: Theorem -> Theorem -> Hol Theorem
deductAntisymRule a b = do
  let aas = termRemove (seqConcl b) (seqAssumps a)
      bas = termRemove (seqConcl a) (seqAssumps b)
  eq <- introEq (seqConcl a) (seqConcl b)
  return (Sequent (merge aas bas) eq)

-- | INST_TYPE
instType :: TypeSubst -> Theorem -> Hol Theorem
instType theta t =
  Sequent `fmap` termImage instFn (seqAssumps t) `ap` instFn (seqConcl t)
  where
  instFn = typeInst theta

-- | INST_TERM
instTerm :: TermSubst -> Theorem -> Hol Theorem
instTerm theta t =
  Sequent `fmap` termImage instFn (seqAssumps t) `ap` instFn (seqConcl t)
  where
  instFn = termSubst theta
