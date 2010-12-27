module Hol.Type where

import Control.DeepSeq (NFData(rnf))
import qualified Data.Set as Set


data Type
  = TVar String
  | TApp String [Type]
    deriving (Eq,Ord,Show)

instance NFData Type where
  rnf (TVar s)    = rnf s
  rnf (TApp s ts) = rnf s `seq` rnf ts

tya :: Type
tya  = TVar "a"

tybool :: Type
tybool  = TApp "bool" []


class FreeTypeVars a where
  freeTypeVars :: a -> Set.Set Type

instance FreeTypeVars a => FreeTypeVars [a] where
  freeTypeVars = Set.unions . map freeTypeVars

instance FreeTypeVars Type where
  freeTypeVars (TApp _ ts) = freeTypeVars ts
  freeTypeVars var@TVar{}  = Set.singleton var

