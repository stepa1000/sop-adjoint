{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}

module SOP.Data.Functor.Adjunction where

import Generics.SOP
import Data.Functor.Adjunction
import Data.Functor.Rep as FR
import Data.Distributive

import Data.Void
{-
type family Concat (x :: [a]) (y :: [a]) :: [a]

type instance Concat '[] '[] = '[]
type instance Concat '[] (y ': ys) = (y ': ys)
type instance Concat (x ': xs) (y ': ys) = (x ': (Concat xs (y ': ys)) )

--data Concatination f1 f2 f3 where
--  Concatination :: Concatination 

class CxtConcact f1 f2 where
  concat :: Proxy f1 -> Proxy f2 -> Proxy (Concat f1 f2)

class ConcatNSF f1 f2 where
  concatNSF :: NSF f1 a -> NSF f2 b -> [NSF (Concat f1 f2) (Either a b)]

instance ConcatNSF xs f2 => ConcatNSF (x ': xs) f2 where
  concatNSF (NSF nsf1) nsf2 = NSF <$> concatNSF nsf1 nsf -- [Right <$> f1 nsf1 nsf2, Left <$> f2 nsf1 nsf2]
  concatNSF (ZF a) nsf = [Left <$> (ZF a), Right <$> (NSF nsf)]
-}
-- instance 

data family AdjL a :: * -> * 
data family AdjR a :: * -> *

data NSF fl a where
  ZF :: (Functor (AdjL f), Adjunction (AdjL f) (AdjR f)) => AdjL f a -> NSF (f ': fs) a
  NSF :: NSF fs a -> NSF (f ': fs) a

-- instance All Functor fl => Functor (NSF fl) where
instance Functor (NSF fl) where
  fmap f (ZF fa) = ZF (fmap f fa)
  fmap f (NSF nsf) = NSF $ fmap f nsf

data NPF fl a where
  NilF :: NPF '[] a 
  (:**) :: ( Functor (AdjR f), Distributive (AdjR f), Representable (AdjR f)
           , Adjunction (AdjL f) (AdjR f) 
           ) 
        => AdjR f a -> NPF fs a -> NPF (f ': fs) a

-- instance All Functor fl => Functor (NPF fl) where
instance Functor (NPF fl) where
  fmap f NilF = NilF 
  fmap f (fa :** npf) = (fmap f fa) :** (fmap f npf)

instance All Distributive '[] => Distributive (NPF '[]) where
  distribute fnpf = NilF

-- instance (All Distributive (x ': xs), All Functor xs, Distributive (NPF xs)) 
--  => Distributive (NPF (x ': xs)) where
instance (Distributive (NPF xs), Representable (AdjR x), Adjunction (AdjL x) (AdjR x)) => Distributive (NPF (x ': xs)) where
  distribute fnpf = (collect headP fnpf) :** (distribute $ fmap tailP fnpf)
    where
      headP :: NPF (x ': xs) a -> AdjR x a
      headP (fa :** npf) = fa
      tailP :: NPF (x ': xs) a -> NPF xs a
      tailP (fa :** npf) = npf

instance Representable (NPF '[]) where
  type Rep (NPF '[]) = Void 
  index _ = absurd
  tabulate _ = NilF

{- instance (All Representable (x ': xs), All Functor xs, All Distributive xs, Distributive (NPF xs)
  , Representable (NPF xs))
  => Representable (NPF (x ': xs)) where
-}
instance ( Distributive (NPF xs), Representable (NPF xs), Representable (AdjR x)
         , Adjunction (AdjL x) (AdjR x))
  => Representable (NPF (x ': xs)) where
  type Rep (NPF (x ': xs)) = Either (FR.Rep (AdjR x) ) (FR.Rep (NPF xs))
  index (a :** b) (Left i) = index a i
  index (a :** b) (Right j) = index b j
  tabulate f = (tabulate (f . Left) ) :** (tabulate (f . Right) )

infixr 5 :**
--infixr 6 :++

data CRF fl a where
  CRE :: a -> CRF '[] a
  CRF :: ( Functor (AdjR f), Distributive (AdjR f), Representable (AdjR f)
         , Adjunction (AdjL f) (AdjR f) 
         ) 
        => AdjR f (CRF fs a) -> CRF (f ': fs) a

instance Functor (CRF fl) where
  fmap f (CRF adjr) = CRF $ (fmap . fmap) f adjr
  fmap f (CRE a) = CRE $ f a

instance Distributive (CRF '[]) where
  distribute f = CRE $ fmap (\(CRE a)-> a) f

instance (Distributive (CRF fl), Adjunction (AdjL f) (AdjR f)) => Distributive (CRF (f ': fl) ) where
  distribute f  = CRF $ fmap distribute $ distribute $ fmap (\(CRF adjr)-> adjr ) f

instance Representable (CRF '[] ) where
  type Rep (CRF '[] ) = ()
  index (CRE a) () = a -- index (index fl i) j
  tabulate f = CRE $ f ()

instance (Representable (CRF fl), Adjunction (AdjL f) (AdjR f)) => Representable (CRF (f ': fl) ) where
  type Rep (CRF (f ': fl)) = (FR.Rep (AdjR f),FR.Rep (CRF fl))
  index (CRF fl) (i,j) = index (index fl i) j
  tabulate = CRF . tabulate . fmap tabulate . curry

data CLF fl a where
  CLF :: (Functor (AdjL f), Adjunction (AdjL f) (AdjR f)) 
      => CLF fs (AdjL f a) -> CLF (f ': fs) a
  CLE :: a -> CLF '[] a

instance Functor (CLF fl) where
  fmap f (CLF clf) = CLF $ (fmap . fmap) f clf
  fmap f (CLE a) = CLE $ f a

{-
type AllAdjunction fl ul 
  = ( Distributive (NPF xs), Representable (NPF xs), Representable (AdjR x)
    , Adjunction (AdjL x) (AdjR x), Adjunction (NSF xs) (NPF xs)) fl
    )
-}

instance Adjunction (CLF '[]) (CRF '[]) where
  leftAdjunct f = CRE . f . CLE
  rightAdjunct f = (\(CRE a)-> a) . f . (\(CLE a)-> a)

instance (Adjunction (AdjL f) (AdjR f), Adjunction (CLF fl) (CRF fl)) => Adjunction (CLF (f ': fl)) (CRF (f ': fl)) where
  unit a = fmap CLF $ CRF $ fmap unit $ unit a
  counit (CLF a) = counit $ fmap counit $ (fmap . fmap) (\(CRF b)-> b) a

instance Adjunction (NSF '[]) (NPF '[]) where
  unit _ = NilF
  counit x = case x of {}  -- undefined

instance ( Distributive (NPF xs), Representable (NPF xs), Representable (AdjR x)
         , Adjunction (AdjL x) (AdjR x), Adjunction (NSF xs) (NPF xs)) 
        => Adjunction (NSF (x ': xs)) (NPF (x ': xs)) where
  unit a = (fmap ZF $ unit a) :** (fmap NSF xs)
    where
      xs = unit a
  counit (ZF adjl) = counit $ fmap (\(h :** _)-> h) adjl
  counit (NSF nsf) = counit $ fmap (\(_ :** h) -> h) nsf


