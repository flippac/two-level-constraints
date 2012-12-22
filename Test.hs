{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, 
             MultiParamTypeClasses, PolyKinds #-}

module Test where

import Data.List
import qualified Data.Map
import Data.Map (Map, fromList)
import Control.Monad
import Control.Monad.Trans
-- import Control.Applicative

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

instance TermLevel Monotype where
  mapChildren f (Prim v) = Prim v
  mapChildren f (TApp l r) = TApp (f l) (f r)
  mapChildren f (Fun l r) = Fun (f l) (f r)
  foldChildren c n (Prim v) = n
  foldChildren c n (TApp l r) = l `c` (r `c` n)
  foldChildren c n (Fun l r) = l `c` (r `c` n)
  match (Prim l) (Prim r) | l == r = Just []
                          | otherwise = Nothing
  match (TApp l r) (TApp l' r') = Just [(l, l'), (r, r')]
  match (Fun l r) (Fun l' r') = Just [(l, l'), (r, r')]
  match _ _ = Nothing

{- Auto-lifting smart constructors for Monotype -}

type MMonotype = MetaTerm Monotype
type MPolytype = FlatMeta (Polytype MMonotype)

prim t = liftMeta $ Prim t 
tApp l r = liftMeta $ TApp l r
fun l r = liftMeta $ Fun l r

forall tvs mty = liftMeta $ Forall tvs mty
  
{- Doesn't substitute through metavariables - this is okay for traditionally
   implemented HM because a polytype will either contain no metavariables after
   generalisation or be lambda-bound and thus not quantified over any type
   variables -}
substTVars :: Map TVar MMonotype ->
              MMonotype ->
              MMonotype
substTVars a (O t) = substTVars' a t
substTVars a m@Metavar {} = m
substTVars' :: Map TVar MMonotype -> 
               Monotype MMonotype ->
               MMonotype
substTVars' assignment p@(Prim v) = case Data.Map.lookup v assignment of
                                      Nothing -> liftMeta p
                                      Just t -> t
substTVars' assignment (TApp l r) = tApp (substTVars assignment l) 
                                         (substTVars assignment r)
substTVars' assignment (Fun l r) = fun (substTVars assignment l)
                                       (substTVars assignment r)

{- Constraint-solving monad -}

newtype HMProblem a = HMP (StoreT MMonotype 
                             (StoreT MPolytype
                               NameSupply
                             )
                             a
                          )
  deriving (Monad)

instance Allocs MMonotype HMProblem where
  newVar = HMP $ newVar
  withVar = (newVar >>=)

instance Allocs MPolytype HMProblem where
  newVar = HMP $ lift $ newVar
  withVar = (newVar >>=)

data HMPResult a = HMPResult {result :: a, 
                              monoStore :: Assignment MMonotype,
                              polyStore :: Assignment MPolytype,
                              varSupply :: Integer}
  deriving Show
  
runHMP (HMP f) = let (((r,ms),ps),c) = runNameSupply 0 (
                                         runStoreT Data.Map.empty (
                                           runStoreT Data.Map.empty f
                                         )
                                       )
                  in HMPResult r ms ps c

{- Constraint functions - all solving done on-the-spot -}

mtEquals :: MMonotype -> MMonotype -> HMProblem ()
l `mtEquals` r = HMP $ do a <- getAssignment
                          case unify l r a of
                            Left e -> error $ show e
                            Right (_, a') -> putAssignment a'

generalise :: [(String, MPolytype)] -> MMonotype -> HMProblem MPolytype
generalise env mty = 
  do mtyAssignment <- HMP $ getAssignment
     ptyAssignment <- HMP $ lift $ getAssignment
     let mvs = nub $ deepMetavars mtyAssignment mty
         envMtys :: [MMonotype]
         envMtys = let getMty (T (Forall _  mty)) = mty
                       getMty (Meta mv) = 
                         case Data.Map.lookup mv ptyAssignment of
                           Nothing -> error "unknown polytype lookup"
                           Just pty -> getMty pty
                    in map (getMty . snd) env
         envFreeMetavars = nub . concat $ 
                             map (deepMetavars mtyAssignment) envMtys
         genVars = map metavar (mvs \\ envFreeMetavars)
         tvars = map (\n -> '#':'t':show n) [0..length genVars]
         tvarTys = map prim tvars
         mtyAssignment' = let unifyVar l r a = case unify l r a of
                                                 Left e -> error $ show e
                                                 Right (_,a') -> a'
                           in foldr (\(l,r) a -> unifyVar l r a)
                                    mtyAssignment 
                                    (zip genVars tvarTys)
     HMP $ putAssignment mtyAssignment'    
     return $ forall tvars mty

instantiate :: MPolytype -> HMProblem MMonotype
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
  deriving Show

{- Typechecker! -}

infer (Var s) env = case Prelude.lookup s env of
                      Nothing -> error $ "Unbound variable " ++ s
                      Just pt -> instantiate pt
infer (App f p) env = withVar (\rt ->
                        do ft <- infer f env
                           pt <- infer p env
                           ft `mtEquals` (pt `fun` rt)
                           return rt
                      )
infer (Lam i t) env = withVar (\pt -> 
                        do rt <- infer t ((i, forall [] pt):env)
                           return $ pt `fun` rt
                      )
infer (Let i t b) env = do pty <- infer t env >>= generalise env
                           infer b ((i, pty) : env)

infer' t e = let c = infer t e >>= generalise e
                 r = runHMP c
                 (T (Forall tvs mty)) = result r
              in subst (monoStore r) mty
