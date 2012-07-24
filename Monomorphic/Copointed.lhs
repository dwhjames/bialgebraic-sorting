%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module Copointed (module Product, Copointed)
> where
> import Product

%endif

A type synonym for cofree copointed functors

> type Copointed f a = a :*: f a

The categories of |F|-coalgebras and coalgebras for the cofree
copointed functor of |F| are isomorphic.

< up ∷ (c → f c) → (c → Copointed f c)
< up a = id /\ a

< down ∷ (c → Copointed f c) → (c → f c)
< down a = outr . a
