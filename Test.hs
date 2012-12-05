{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, 
             MultiParamTypeClasses, PolyKinds #-}

module Test where

import Data.Map
import Control.Monad.Trans
import Control.Applicative

import TwoLevelTerms
import MetaTerm
import Unification
import ConstraintStore

{- Types for a Hindley-Milner-based language -}

data Monotype fix = Prim TVar |
                    TApp fix fix |
                    Fun fix fix
  deriving Show
data Polytype mt = Forall [TVar] mt
  deriving Show

type TVar = String

{- Doesn't substitute through metavariables - this is okay for HM because a
   polytype will either contain no metavariables after generalisation or be
   lambda-bound and thus not quantified over any type variables -}
substTVars :: Map TVar (MetaTerm Monotype) -> 
              MetaTerm Monotype -> 
              MetaTerm Monotype
substTVars a (O t) = substTVars' a t
substTVars a m@Metavar {} = m
substTVars' :: Map TVar (MetaTerm Monotype) -> 
               Monotype (MetaTerm Monotype) -> 
               MetaTerm Monotype
substTVars' assignment p@(Prim v) = case Data.Map.lookup v assignment of
                                      Nothing -> liftMeta p
                                      Just t -> t
substTVars' assignment (TApp l r) = liftMeta $ TApp (substTVars assignment l)
                                                    (substTVars assignment r)
substTVars' assignment (Fun l r) = liftMeta $ Fun (substTVars assignment l)
                                                  (substTVars assignment r)

{- Constraint-solving monad -}

newtype HMProblem a = HMP (StoreT (MetaTerm Monotype) 
                             (StoreT (FlatMeta (Polytype (MetaTerm Monotype)))
                               NameSupply
                             )
                             a
                          )
  deriving (Monad)
  
instance Allocs (MetaTerm Monotype) HMProblem where
  newVar = HMP $ newVar
  withVar = (newVar >>=)

instance Allocs (FlatMeta (Polytype (MetaTerm Monotype))) HMProblem where
  newVar = HMP $ lift newVar
  withVar = (newVar >>=)

runHMP (HMP f) = runNameSupply 0 (
                   runStoreT Data.Map.empty (
                    runStoreT Data.Map.empty f
                   )
                 )

{- Constraint functions - all solving done on-the-spot -}

mtEquals :: MetaTerm Monotype -> MetaTerm Monotype -> HMProblem ()
l `mtEquals` r = undefined
generalise :: MetaTerm Monotype -> 
              HMProblem (FlatMeta (Polytype (MetaTerm Monotype)))
generalise mty = undefined
instantiate :: FlatMeta (Polytype (MetaTerm Monotype)) -> 
               HMProblem (MetaTerm Monotype)
instantiate (T (Forall vs mty)) = do metavars <- mapM (const newVar) vs
                                     return $
                                       substTVars (fromList (zip vs metavars))
                                                  mty
instantiate (Meta mi) = do pty <- (HMP $ lift $ examine mi)
                           case pty of
                             Nothing -> error "instantiated unknown polytype"
                             Just pty' -> instantiate pty'

{- Terms -}
                             
data Term = Var String | 
            App Term Term | 
            Lam String Term | 
            Let String Term Term

{- Typechecker! -}

infer (Var s) env = case Prelude.lookup s env of
                      Nothing -> error $ "Unbound variable " ++ s
                      Just pt -> instantiate pt
infer (App f p) env = withVar (\rt ->
                        do ft <- infer f env
                           pt <- infer p env
                           ft `mtEquals` liftMeta (pt `Fun` rt)
                           return rt
                        )
infer (Lam i t) env = withVar (\pt -> infer t ((i,liftMeta $ Forall [] pt):env))
infer (Let i t b) env = do pty <- infer t env >>= generalise
                           infer b ((i, pty) : env)
