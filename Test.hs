{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, 
             MultiParamTypeClasses, PolyKinds #-}

module Test where

import Data.Map
import Control.Monad.Trans
import Control.Applicative

import TwoLevelTerms
import MetaTerm
import ConstraintStore

data Monotype fix = Prim TVar | 
                    TApp fix fix | 
                    Fun fix fix
data Polytype mt = Forall [TVar] mt

type TVar = String

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

mtEquals :: MetaTerm Monotype -> MetaTerm Monotype -> HMProblem ()
l `mtEquals` r = undefined
generalise :: MetaTerm Monotype -> 
              HMProblem (FlatMeta (Polytype (MetaTerm Monotype)))
generalise mty = undefined
instantiate :: FlatMeta (Polytype (MetaTerm Monotype)) -> 
               HMProblem (MetaTerm Monotype)
instantiate (T (Forall vs mty)) = undefined 
                                  -- FIXME: needs term-level substitution
instantiate (Meta mi) = do undefined 
                 
data Term = Var String | 
            App Term Term | 
            Lam String Term | 
            Let String Term Term
            
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
