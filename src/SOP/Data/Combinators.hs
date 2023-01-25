{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts#-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module SOP.Data.Combinators where

import SOP.Data.Functor.Adjunction

import Data.Functor.Adjunction

import Control.Monad.Trans.Adjoint as M
import Control.Comonad.Trans.Adjoint as W

import Control.Monad
import Control.Comonad

(#..) :: (Monad m, Adjunction (AdjL f) (AdjR f), Adjunction (CLF fl) (CRF fl))
      => M.AdjointT (AdjL f) (AdjR f) m a -> M.AdjointT (CLF fl) (CRF fl) m b -> M.AdjointT (CLF (f ': fl)) (CRF (f ': fl)) m (a,b)
(M.AdjointT a) #.. (M.AdjointT b) = M.AdjointT $ 
  (fmap . fmap) CLF $ fmap join $ CRF $
  fmap (\ a2 -> fmap (\b2-> fmap (\b3-> fmap (\a3-> fmap (\bv-> fmap (\av->(av,bv)) a3) b3) a2 ) b2 )  b) a

(#+*) :: (Monad m, Adjunction (AdjL f) (AdjR f))
      => M.AdjointT (AdjL f) (AdjR f) m a -> M.AdjointT (NSF fl) (NPF fl) m b -> M.AdjointT (NSF (f ': fl)) (NPF (f ': fl)) m (Either a b)
(M.AdjointT a) #+* (M.AdjointT b) = M.AdjointT $ 
  ((fmap . fmap . fmap) Left $ (fmap . fmap) ZF a) :** ((fmap . fmap . fmap) Right $ (fmap . fmap) NSF b)

(@..) :: (Comonad m, Adjunction (AdjL f) (AdjR f), Adjunction (CLF fl) (CRF fl), ComonadApply m)
      => W.AdjointT (AdjL f) (AdjR f) m a -> W.AdjointT (CLF fl) (CRF fl) m b -> W.AdjointT (CLF (f ': fl)) (CRF (f ': fl)) m (a,b)
(W.AdjointT a) @.. (W.AdjointT b) = W.AdjointT $ 
  CLF $ 
  fmap (\b2-> fmap (\a2-> liftW2 (\a3 b3-> CRF $ fmap (\av-> fmap (\bv-> (av,bv)) b3) a3) a2 b2) a) b

(@+*) :: (Comonad m, Adjunction (AdjL f) (AdjR f), Adjunction (NSF fl) (NPF fl))
      => W.AdjointT (AdjL f) (AdjR f) m a -> W.AdjointT (NSF fl) (NPF fl) m b -> [W.AdjointT (NSF (f ': fl)) (NPF (f ': fl)) m (Either a b)]
(W.AdjointT a) @+* (W.AdjointT b) = 
  [ W.AdjointT $ (fmap . fmap) (\a2-> (fmap Left a2) :** (fmap Right $ extract $ extractL b)) $ ZF a
  , W.AdjointT $ (fmap . fmap) (\b2-> (fmap Left $ extract $ extractL a) :** (fmap Right b2) ) $ NSF b
  ] 
{- _a $ 
  --(fmap . fmap) CLF $ CRF $
  CRF $
  (fmap . fmap) join $
  (fmap . fmap . fmap) sequenceA $
  fmap (\b2-> (fmap . fmap . fmap) (\av-> (fmap . fmap) (\bv-> (av,bv)) b2) a ) b
-}
