%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module Pointed (module LiftedCoproduct, Pointed)
> where
> import LiftedCoproduct

%endif

> type Pointed h f = f :+: h f


< up ∷ (s a → a) → (Pointed s a → a)
< up a = id \/ a

< down ∷ (Pointed s a → a) → (s a → a)
< down a = a . Con
