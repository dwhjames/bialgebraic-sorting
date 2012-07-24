%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
> module Intermediate(downcast)
> where
> import InitialAlgebra
> import FinalCoalgebra
> import HFunctor

%endif


> downcast  ∷  (HFunctor f) ⇒ Cofix f :→ Fix f
> downcast  =  inn . hmap downcast . out
