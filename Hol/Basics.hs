module Hol.Basics where

import Error
import Hol.Monad
import Hol.Subst
import Hol.Term
import Hol.Type

import Control.Monad (unless,MonadPlus(..),ap)


destBoundVar :: Term -> Hol Term
destBoundVar tm = fst `fmap` destAbs tm `onError` fail "destBoundVar"

destAbsBody :: Term -> Hol Term
destAbsBody tm = snd `fmap` destAbs tm `onError` fail "destAbsBody"

destBinop :: Term -> Term -> Hol (Term,Term)
destBinop op tm = do
  let body = do
        (lop,r) <- destApp tm
        (op',l) <- destApp lop
        return (l,op',r)
  (l,op',r) <- body `onError` fail "destBinop"
  unless (op' == op) (fail "destBinop")
  return (l,r)

alpha :: Term -> Term -> Hol Term
alpha v tm = do
  (v0,b) <- destAbs tm `onError` fail "alpha: not an abstraction"
  if v == v0
     then return tm
     else do
       vty  <- typeOf v
       v0ty <- typeOf v0
       if vty == v0ty && not (varFreeIn v b)
          then mkAbs v =<< termSubst (extendSubst v v0 emptySubst) b
          else fail "alpha: Invalid new variable"

splitList :: MonadPlus m => (a -> m (b,a)) -> a -> m ([b],a)
splitList dest x = body `mplus` return ([],x)
  where
  body = do
    (l,r)    <- dest x
    (ls,res) <- splitList dest r
    return (l:ls,res)

splitAbs :: Term -> Hol ([Term],Term)
splitAbs  = splitList destAbs

freeIn :: Term -> Term -> Hol Bool
freeIn tm1 tm2
  | aconv tm1 tm2 = return True
  | isApp tm2     = do
    (l,r) <- destApp tm2
    b1 <- freeIn tm1 l
    b2 <- freeIn tm1 r
    return (b1 || b2)
  | isAbs tm2     = do
    (bv,bod) <- destAbs tm2
    b1 <- freeIn bv tm1
    b2 <- freeIn tm1 bod
    return (not (b1 && b2))
  | otherwise     = return False
