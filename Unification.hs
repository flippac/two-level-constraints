module Unification where

{- Derived from Sheard's generic unification paper. 
   Efficiency thrown to the wind in favour of explicit assignments and
   simplicity. -}

{- FIXME: How far can this generalise without being likely horribly unsound? 
          Is there a useful generalisation where unification gives up on some
          constructors?
-}   

import Prelude hiding (lookup)
import Data.Map
import Data.List (nub)
import Control.Monad

import TwoLevelTerms
import MetaTerm

data UnificationError t = OccursCheck MVIdentifier t | Mismatch t t

unify :: TermLevel t =>  MetaTerm t -> MetaTerm t -> 
                         Assignment (MetaTerm t) -> 
                          Either (UnificationError (MetaTerm t)) 
                                 (MetaType t, Assignment (MetaTerm t))
unify mv@(Metavar mv1) (Metavar mv2) a | mv1 == mv2 = return (mv, a)
unify (Metavar mv) t a = case lookup mv a of
                           Nothing -> case occurs mv a t of
                                        True -> Left $ OccursCheck mv t
                                        False -> return (t, insert mv t a)
                           Just t' -> unify t' t a
unify t (Metavar mv) a = case lookup mv a of
                           Nothing -> case occurs mv a t of
                                        True -> Left $ OccursCheck mv t
                                        False -> return (t, insert mv t a)
                           Just t' -> unify t t' a
unify (O o1) (O o2) a = case match o1 o2 of
                          Nothing -> Left $ Mismatch (O o1) (O o2)
                          Just cs -> do (ts, a') <- unifyChildren cs a
                                        return (O o1, a') 

unifyChildren :: TermLevel t =>
                 [(MetaTerm t, MetaTerm t)] -> Assignment (MetaTerm t) -> 
                 Either (UnificationError (MetaTerm t)) 
                        ([MetaTerm t], Assignment (MetaTerm t))
unifyChildren [] a = return ([], a)
unifyChildren ((l,r):cs) a = do (t, a') <- unify l r a
                                (ts, a'') <- unifyChildren cs a'
                                return (t:ts, a'')
