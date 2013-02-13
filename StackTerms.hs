{-# LANGUAGE LiberalTypeSynonyms, FlexibleContexts, FlexibleInstances, UndecidableInstances, TypeOperators #-}

{-  LANGUAGE FlexibleContexts, UndecidableInstances, FlexibleInstances,
             StandaloneDeriving, PolyKinds, MultiParamTypeClasses,
             FunctionalDependencies -}

module StackTerms where

{- I would like this to go away, but have sneaking suspicion I need it 
   for type-level pattern-matching purposes. If nothing else, I may want
   to start composing terms and find they're all made of functors or something
-}
newtype Term t f = Term {unTerm :: t f}
  deriving Show

-- Probably a good idea to keep all this crap handy too
class TermLevel t where
  mapChildren :: (x -> y) -> t x -> t y
  foldChildren :: (x -> y -> y) -> y -> t x -> y
  match :: t x -> t x -> Maybe [(x,x)]
  -- seqChildren :: t [m x] -> m (t x)
  -- Yes, there are standard-on-HackageDB packages/names for these

{- Eye of the syntactic storm -}
newtype Fix a = Fix {unFix :: a (Fix a)}

instance Show (a (Fix a)) => Show (Fix a) where
  show (Fix a) = "Fix (" ++ show a ++ ")"

{- Stack of meta-level gadgetry. It'd be nice if we can get a stronger
   composition such as products, but don't want to require it at this stage -}

-- Q: Do I need t mt, or will t' where t' = t mt do?
newtype Stack f t mt = Stack {unStack :: f (t mt)}
  deriving Show

newtype (g :. f) a = O (g (f a))
  deriving Show

mapOl f (O g) = O (f g)
mapOr f (O g) = O (fmap f g) 

newtype Id a = Id a
  deriving Show

type IdStack t = Stack Id t

newtype Labelled g l f a = L (g (f a))
  deriving Show

{- Some gadgets -}

type MVIdentifier = Integer
data MetaTerm v t = T t | Metavar v
  deriving Show

data Annotation a t = Annotate {annotation :: a, 
                                term :: t}
  deriving Show

{- Demo/test term -}
-- O hai thar, Graham!
data Hutton t = V Integer | Add t t
  deriving Show
type HuttonTerm = Term Hutton

instance TermLevel Hutton where
  mapChildren _ (V n) = V n
  mapChildren f (Add l r) = Add (f l) (f r)
  foldChildren c n v@V{} = n
  foldChildren c n (Add l r) = l `c` (r `c` n)
  match (V a) (V b) | a == b = Just [] 
                    | otherwise = Nothing
  match (Add l1 r1) (Add l2 r2) = Just [(l1,l2), (r1,r2)]
  match _ _ = Nothing

-- By the time we expand this out it's a bit of a mouthful
-- Fix Hutton is bad enough
type TrivialHuttonStack = IdStack HuttonTerm
type HuttonsRazorTrivialEdition = Fix TrivialHuttonStack

-- Yes, "trivial". Honest. Talk about syntactic overhead!
trivialTerm = Fix $ Stack $ Id $ Term $ V 1

type StackInnards a = Annotation a :. MetaTerm MVIdentifier

type RazorMetaStack a = Stack (StackInnards a) 
                              HuttonTerm
type HuttonsRazorWithAllTheMeta annotation = Fix (RazorMetaStack annotation)

allTheMetaTerm = Fix $ Stack $ O $ Annotate "OFFS" $ T $ Term $ V 1

instance Functor Id where
  fmap f (Id a) = Id (f a)

instance (Functor l, Functor r) => 
           Functor (l :. r) where
  fmap f (O gfa) = O (fmap (fmap f) gfa)

instance (Functor l, Functor r) => 
           Functor (Labelled l lab r) where
  fmap f (L gfa) = L (fmap (fmap f) gfa)
  
instance Functor (Annotation a) where
  fmap f (Annotate a t) = Annotate a (f t)

instance Functor (MetaTerm v) where
  fmap f (T t) = T (f t)
  fmap _ (Metavar v) = Metavar v
  
mapToTerm f (Fix (Stack ft)) = Fix $ Stack $ fmap f ft

{- What's the point? -}

class Functor f => Pointed f where
  point :: a -> f a

instance Pointed Id where
  point = Id
  
instance (Pointed l, Pointed r) => Pointed (l :. r) where
  point p = O $ point $ point p
  
instance Pointed (Annotation (Maybe a)) where
  point p = Annotate Nothing p

instance Pointed (MetaTerm v) where
  point = T

{- Copoints -}

class Functor f => CoPointed f where
  extract :: f a -> a
  
instance CoPointed Id where
  extract (Id a) = a

instance (CoPointed l, CoPointed r) => CoPointed (l :. r) where
  extract (O gfa) = extract . extract $ gfa

instance CoPointed (Annotation a) where
  extract = term

-- Would be a copoint, but to the wrong damn category
extractMeta (T t) = Just t
extractMeta _ = Nothing

destack :: (CoPointed f, TermLevel t) => Fix (Stack f (Term t)) -> Fix (Term t)
destack (Fix (Stack s)) = let (Term term) = extract s in
                           Fix $ Term $ mapChildren destack term

{- Compatibility funcs -}

{- Blagged from previous version of unification code -}

data UnificationError t = OccursCheck MVIdentifier t | Mismatch t t
  deriving Show

-- use a unify/unify' worker/wrapper re Fix&Stack(-prefix)?
-- Oh, crap, we need a way to get to the nominated Meta layer
-- Guess it's time to blag sigfpe's tags?

{-
unify l r a = 

unify' mv@(Metavar mv1) (Metavar mv2) a | mv1 == mv2 = return (mv, a)
unify' (Metavar mv) t a = case lookup mv a of
                            Nothing -> case occurs mv a t of
                                         True -> Left $ OccursCheck mv t
                                         False -> return (t, insert mv t a)
                            Just t' -> unify t' t a
unify' t (Metavar mv) a = case lookup mv a of
                            Nothing -> case occurs mv a t of
                                         True -> Left $ OccursCheck mv t
                                         False -> return (t, insert mv t a)
                            Just t' -> unify' t t' a
unify' (T t1) (T t2) a = case match t1 t2 of
                           Nothing -> Left $ Mismatch (T t1) (T t2)
                           Just cs -> do (ts, a') <- unifyChildren cs a
                                         return (T t1, a') 

unifyChildren [] a = return ([], a)
unifyChildren ((l,r):cs) a = do (t, a') <- unify l r a
                                (ts, a'') <- unifyChildren cs a'
                                return (t:ts, a'')
-}
