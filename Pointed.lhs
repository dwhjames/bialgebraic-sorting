%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module Pointed (module Coproduct, Pointed)
> where
> import Coproduct

%endif

A type synonym for free pointed functors.

> type Pointed f a = a :+: f a

The categories of |F|-algebras and algebras for the free pointed
functor of |F| are isomorphic.

< up ∷ (s a → a) → (Pointed s a → a)
< up a = id \/ a

< down ∷ (Pointed s a → a) → (s a → a)
< down a = a . Con
