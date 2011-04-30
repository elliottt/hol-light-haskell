module Hol.Tactics where

import Hol.Assumps
import Hol.Monad
import Hol.Subst
import Hol.Term
import Hol.Type

data Inst = Inst
  { instData  :: [(Int,Term)]
  , instTerms :: Subst Term
  , instTypes :: Subst Type
  }

data Goal = Goal
  { goalAssumps :: Assumps (String,Theorem)
  , goalTerm    :: Term
  }

type Justification = Inst -> [Theorem] -> Hol Theorem

data GoalState = GoalState
  { gsMetaVars :: [Term]
  , gsInst     :: Inst
  , gsSubGoals :: [Goal]
  , gsJust     :: Justification
  }

type GoalStack = [GoalState]

type Refinement = GoalState -> Hol GoalState

type Tactic = Goal -> Hol GoalState

type ThmTactic = Theorem -> Hol Tactic

type ThmTactical = ThmTactic -> ThmTactic

instGoal :: Inst -> Goal -> Hol Goal
instGoal p g = undefined
