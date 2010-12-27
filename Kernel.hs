{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Kernel (
    TermRep(..)
  , Sequent()
  , Theorem
  , printTheorem

  , refl
  , trans

  , abstract

  , beta

  , assume
  , eqMP
  , deductAntisymRule
  ) where

import Hol

import Control.DeepSeq (NFData(rnf))
import Control.Monad (unless,(<=<),ap)


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
