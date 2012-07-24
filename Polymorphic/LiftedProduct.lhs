%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
> module LiftedProduct((:*:)(..), (/\))
> where
> import NatTrans

%endif

> data (f :*: g) a = As { outl ∷ f a, outr ∷ g a }
>
> (/\) ∷ (x :→ f) → (x :→ g) → (x :→ (f :*: g))
> (f /\ g) x  =  As (f x) (g x)
