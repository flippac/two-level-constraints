{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             FlexibleInstances, NoMonomorphismRestriction #-}

module ConstraintStore where

import Prelude hiding (lookup)

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.State

import Data.Map

import TwoLevelTerms

{-class Applicative f => Names f where
  genSym :: f Integer   - preferred, but MonadState is a pain -} 

class Monad m => Names m where
  genSym :: m Integer

newtype NameSupplyT m a = NS (StateT Integer m a)
  deriving (Monad, MonadTrans, Functor, Applicative)

type NameSupply = NameSupplyT Identity

instance (Monad m) => Names (NameSupplyT m) where
  genSym = NS $ do i <- get
                   put $ i+1
                   return i
           -- NS $ get <* modify (+1) - neater, but welcome to instance hell

runNameSupplyT n (NS c) = runStateT n c
runNameSupply n c = runIdentity $ runNameSupplyT n c

class Allocs t f where
  newVar :: f t
  withVar :: (t -> f a) -> f a
  
newtype StoreT t m a = S (StateT (Assignment t) m a)
  deriving (Monad, MonadTrans, Functor, Applicative)
  
examine v = S $ gets $ lookup v
update v t = S $ modify $ insert v t

getAssignment = S get
putAssignment = S . put

runStoreT a (S f) = runStateT f a

instance Names m => Names (StoreT t m) where
  genSym = lift genSym

instance (Names m, HasMetavars t) => 
           Allocs t (StoreT t m) where
  newVar = metavar `liftM` genSym
  withVar = (newVar >>=)
