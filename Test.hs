{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, 
             MultiParamTypeClasses #-}

module Test where

import Data.Map
import Control.Monad.Trans

import TwoLevelTerms
import MetaTerm
import ConstraintStore

data Monotype fix = Prim TVar | 
                    TApp (Monotype fix) (Monotype fix) | 
                    Fun (Monotype fix) (Monotype fix)
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
