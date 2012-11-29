{-# LANGUAGE FlexibleContexts, UndecidableInstances, FlexibleInstances,
             StandaloneDeriving, PolyKinds, MultiParamTypeClasses,
             FunctionalDependencies #-}

module TwoLevelTerms where

import Data.Map

{- Our two levels -}

class TermLevel t where
  mapChildren :: (x -> y) -> t x -> t y
  foldChildren :: (x -> y -> y) -> y -> t x -> y
  match :: t x -> t x -> Maybe [(x,x)]

class MetaLevel (f :: k -> *) (p :: k) v | f -> v p where
  mapTerms :: (v -> v) -> f p -> f p
  liftMeta :: v -> f p

{- Metavariables & Assignments -}  
  
type MVIdentifier = Integer
type Assignment t = Map MVIdentifier t  
  
class HasMetavars t where
  metavar :: MVIdentifier -> t
  matchMeta :: t -> Maybe MVIdentifier

{- Variableless metalevel wrappers 

   Use Id for flat terms, Fix for recursive ones-}
  
newtype Id a = Id a
  deriving (Show, Eq)

instance MetaLevel Id t t where
  mapTerms f (Id a) = Id $ f a
  liftMeta = Id

newtype Fix a = Fix {unFix :: a (Fix a)}

deriving instance Show (a (Fix a)) => Show (Fix a)

instance Eq (a (Fix a)) => Eq (Fix a) where
  (Fix l) == (Fix r) = l == r

instance MetaLevel Fix f (f (Fix f)) where
  mapTerms f (Fix t) = Fix $ f t
  liftMeta = Fix
