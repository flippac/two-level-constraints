{-# LANGUAGE StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances,
             UndecidableInstances #-}

module MetaTerm (MetaTerm, FlatMeta,
                 subst, metavars, deepMetavars, occurs) where

import Data.List

import TwoLevelTerms

{- Basic meta-level type wrapper -}

data MetaTerm o = O (o (MetaTerm o)) | Metavar MVIdentifier

deriving instance Show (a (MetaTerm a)) => Show (MetaTerm a)

instance MetaLevel MetaTerm t (t (MetaTerm t)) where
  mapTerms f (O t) = O $ f t
  mapTerms f m@Metavar{} = m
  liftMeta = O

instance HasMetavars (MetaTerm t) where
  metavar = Metavar
  matchMeta (Metavar mi) = Just mi
  matchMeta _ = Nothing

{- Flat/non-recursive variant -}
  
data FlatMeta t = T t | Meta MVIdentifier
  deriving Show

instance MetaLevel FlatMeta t t where
  mapTerms f (T t) = T $ f t
  mapTerms _  t = t
  liftMeta = T

instance HasMetavars (FlatMeta t) where
  metavar = Meta
  matchMeta (Meta i) = Just i
  matchMeta _ = Nothing

{- FIXME: These should generalise -}
  
{- Substituting an assignment into a term -}

subst a (Metavar mv) = case lookup mv a of
                         Just ty -> subst a ty
                         Nothing -> Metavar mv
subst a (O ty) = O $ mapChildren (subst a) ty

{- Metavariables in a term -}

metavars :: TermLevel t => MetaTerm t -> [MVIdentifier]
metavars (Metavar mv) = [mv]
metavars (O o) = nub $ foldChildren (++) [] (mapChildren metavars o)

deepMetavars a t = deepMetavars' a [] t
  where deepMetavars' a visited (Metavar mv) 
          | mv `elem` visited = []
          | otherwise = case lookup mv a of
                          Nothing -> [mv]
                          Just t -> deepMetavars' a (mv:visited) t
        deepMetavars' a v (O o) = foldChildren (\t v -> deepMetavars' a v t) 
                                               v
                                               o

occurs mv assignment t = mv `elem` deepMetavars assignment t
