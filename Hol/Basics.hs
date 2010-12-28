module Hol.Basics where

import Error
import Hol.Monad
import Hol.Subst
import Hol.Term
import Hol.Type

destBoundVar :: Term -> Hol Term
destBoundVar tm = fst `fmap` destAbs tm `onError` fail "destBoundVar"

destAbsBody :: Term -> Hol Term
destAbsBody tm = snd `fmap` destAbs tm `onError` fail "destAbsBody"

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
