%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
> module LiftedCoproduct((:+:)(..), play, stop, (\/))
> where
> import NatTrans

%endif

> data (f :+: g) a = Stop (f a) | Play (g a)

> (\/) ∷ (f :→ x) → (g :→ x) → ((f :+: g) :→ x)
> (f   \/ _g) (Stop  a)  =  f a
> (_f  \/ g ) (Play  b)  =  g b


%if False

> play  ∷  g a → (f :+: g) a
> play  =  Play

> stop  ∷  f a → (f :+: g) a
> stop  =  Stop

%endif
