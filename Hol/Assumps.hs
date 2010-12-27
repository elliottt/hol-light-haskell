{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Hol.Assumps where

import Control.DeepSeq (NFData(rnf))


newtype Assumps a = Assumps
  { getAssumps :: [a]
  } deriving (Eq,Show,NFData)

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
