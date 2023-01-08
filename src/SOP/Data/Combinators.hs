{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts#-}

module SOP.Data.Combinators where

import SOP.Data.Functor.Adjunction

import Data.Functor.Adjunction

import Control.Monad.Trans.Adjoint as M
import Control.Comonad.Trans.Adjoint as W

import Control.Monad

(#..) :: (Monad m, Adjunction (AdjL f) (AdjR f), Adjunction (CLF fl) (CRF fl))
      => M.AdjointT (AdjL f) (AdjR f) m a -> M.AdjointT (CLF fl) (CRF fl) m b -> M.AdjointT (CLF (f ': fl)) (CRF (f ': fl)) m (a,b)
(M.AdjointT a) #.. (M.AdjointT b) = M.AdjointT $ 
  (fmap . fmap) CLF $ fmap join $ CRF $
  fmap (\ a2 -> fmap (\b2-> fmap (\b3-> fmap (\a3-> fmap (\bv-> fmap (\av->(av,bv)) a3) b3) a2 ) b2 )  b) a

(#+*) :: (Monad m, Adjunction (AdjL f) (AdjR f), Adjunction (CLF fl) (CRF fl))
      => M.AdjointT (AdjL f) (AdjR f) m a -> M.AdjointT (NSF fl) (NPF fl) m b -> M.AdjointT (NSF (f ': fl)) (NPF (f ': fl)) m (Either a b)
(M.AdjointT a) #+* (M.AdjointT b) = M.AdjointT $ 
  ((fmap . fmap . fmap) Left $ (fmap . fmap) ZF a) :** ((fmap . fmap . fmap) Right $ (fmap . fmap) NSF b)
{-
(@..) :: (Monad m, Adjunction (AdjL f) (AdjR f), Adjunction (CLF fl) (CRF fl))
      => W.AdjointT (AdjL f) (AdjR f) m a -> W.AdjointT (CLF fl) (CRF fl) m b -> W.AdjointT (CLF (f ': fl)) (CRF (f ': fl)) m (a,b)
(M.AdjointT a) #.. (M.AdjointT b) = M.AdjointT $ 
-}

{- _a $ 
  --(fmap . fmap) CLF $ CRF $
  CRF $
  (fmap . fmap) join $
  (fmap . fmap . fmap) sequenceA $
  fmap (\b2-> (fmap . fmap . fmap) (\av-> (fmap . fmap) (\bv-> (av,bv)) b2) a ) b
-}
