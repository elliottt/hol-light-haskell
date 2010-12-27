module Hol.Term where

import Hol.Type

import Control.DeepSeq (NFData(rnf))
import Data.List (union,delete)
import qualified Data.Set as Set


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

instance FreeTypeVars Term where
  freeTypeVars (Var _ ty) = freeTypeVars ty
  freeTypeVars (Con _ ty) = freeTypeVars ty
  freeTypeVars (Abs v t)  = freeTypeVars v `Set.union` freeTypeVars t
  freeTypeVars (App f x)  = freeTypeVars f `Set.union` freeTypeVars x

-- | Format a term as a String.
formatTerm :: Term -> String
formatTerm (Var n ty)  = n
formatTerm (Con n ty)  = n
formatTerm (App f x)   = formatTerm f ++ " " ++ formatTerm x
formatTerm (Abs n b) = '\\' : formatTerm n ++ '.' : formatTerm b

-- | Collect the free variables in a term.
frees :: Term -> [Term]
frees tm@Var{}     = [tm]
frees tm@Con{}     = []
frees tm@(Abs v b) = delete v (frees b)
frees tm@(App f x) = union (frees f) (frees x)

-- | Verify that the free variables of the term occur in the list of variables
-- provided.
freesin :: [Term] -> Term -> Bool
freesin acc tm@Var{}  = elem tm acc
freesin acc tm@Con{}  = True
freesin acc (Abs v b) = freesin (v:acc) b
freesin acc (App s t) = freesin acc s && freesin acc t

-- | Whether a variable or constant is free in a term.
varFreeIn :: Term -> Term -> Bool
varFreeIn v (Abs bv b) = v /= bv && varFreeIn v b
varFreeIn v (App f x)  = varFreeIn v f || varFreeIn v x
varFreeIn v v'         = v /= v'

