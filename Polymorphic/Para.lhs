%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
> module Para(module LiftedProduct, para)
> where
> import InitialAlgebra
> import LiftedProduct

%endif

> para  ∷  (HFunctor h) ⇒ (h (Fix h :*: f) :→ f) → (Fix h :→ f)
> para f  =  f . hmap (id /\ para f) . inI

