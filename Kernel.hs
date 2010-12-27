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


