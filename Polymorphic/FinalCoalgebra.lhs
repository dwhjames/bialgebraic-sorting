%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators, UndecidableInstances #-}
> module FinalCoalgebra (module HFunctor, Cofix(..), outI, unfold)
> where
> import HFunctor

%endif

> newtype Cofix f a = OutI { out ∷ f (Cofix f) a }

%if False

> outI  ∷  f (Cofix f) a → Cofix f a
> outI  =  OutI

> instance Show (f (Cofix f) a) ⇒ Show (Cofix f a) where
>   show (OutI x) = show x

%endif

> unfold ∷ (HFunctor h) ⇒ (f :→ h f) → (f :→ Cofix h)
> unfold c  =  OutI . hmap (unfold c) . c


