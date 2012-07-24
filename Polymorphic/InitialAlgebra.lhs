%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators, UndecidableInstances #-}
> module InitialAlgebra (module HFunctor, Fix(..), inn, fold)
> where
> import HFunctor

%endif

> newtype Fix f a = In { inI ∷ f (Fix f) a }

%if False

> inn  ∷  f (Fix f) a → Fix f a
> inn  =  In

> instance Show (f (Fix f) a) ⇒ Show (Fix f a) where
>   show (In x) = show x

%endif

> fold ∷ (HFunctor h) ⇒ (h f :→ f) → (Fix h :→ f)
> fold f  =  f . hmap (fold f) . inI