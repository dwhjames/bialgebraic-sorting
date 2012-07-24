%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module Copointed (module LiftedProduct, Copointed)
> where
> import LiftedProduct

%endif


> type Copointed h f = f :*: h f


< up ∷ (c → f c) → (c → Copointed f c)
< up a = id /\ a

< down ∷ (c → Copointed f c) → (c → f c)
< down a = outr . a
