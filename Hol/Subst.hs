module Hol.Subst where

import Data.List (find)

newtype Subst a = Subst
  { getSubst :: [(a,a)]
  } deriving (Eq,Show)

-- | Substitution with no members.
emptySubst :: Subst a
emptySubst  = Subst []

-- | Check if a substitution is the null substitution.
nullSubst :: Subst a -> Bool
nullSubst (Subst u) = null u

-- | Add a mapping to the substitution.
extendSubst :: a -> a -> Subst a -> Subst a
extendSubst a a' (Subst u) = Subst ((a,a'):u)

-- | True if anything in the substitution passes the predicate.
anySubst :: (a -> a -> Bool) -> Subst a -> Bool
anySubst p (Subst u) = any (uncurry p) u

-- | True if everything in the substitution passes the predicate.
allSubst :: (a -> a -> Bool) -> Subst a -> Bool
allSubst p (Subst u) = all (uncurry p) u

-- | Filter the substitution.
filterSubst :: (a -> a -> Bool) -> Subst a -> Subst a
filterSubst p (Subst u) = Subst (filter (uncurry p) u)

-- | Lookup the replacement part of a substitution.
lookupSubst :: Eq a => a -> Subst a -> Maybe a
lookupSubst n (Subst env) = snd `fmap` find p env
  where
  p (t,_) = n == t

-- | Lookup the key part of a substitution.
lookupSubstR :: Eq a => a -> Subst a -> Maybe a
lookupSubstR n (Subst env) = fst `fmap` find p env
  where
  p (_,x) = n == x
