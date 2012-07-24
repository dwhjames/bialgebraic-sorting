%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
> module Apo (module LiftedCoproduct, apo)
> where
> import FinalCoalgebra
> import LiftedCoproduct
> import HFunctor

%endif

> apo  ∷  (HFunctor h) ⇒ (f :→ h (Cofix h :+: f)) → (f :→ Cofix h)
> apo f  =  outI . hmap (id \/ apo f) . f

