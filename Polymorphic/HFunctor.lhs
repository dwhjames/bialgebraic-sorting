%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
> module HFunctor (module NatTrans, HFunctor(..))
> where
> import NatTrans

%endif

> class HFunctor h where
>   hmap ∷ (f :→ g) -> (h f :→ h g)
