%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
> module ListH(
>   module InitialAlgebra,
>   ListH(..), toListH
> )
> where
> import InitialAlgebra
> import List
> import HFunctor

%endif

> data ListH list a = NilH | ConsH a (list a) | Sink a (list a)

> instance HFunctor ListH where
>   hmap _f  NilH          =  NilH
>   hmap f   (ConsH  i x)  =  ConsH  i (f x)
>   hmap f   (Sink   i x)  =  Sink   i (f x)


%if False

> toListH ∷ Fix List :→ Fix ListH
> toListH (In Nil)         =  In NilH
> toListH (In (Cons a l))  =  In (ConsH a (toListH l))

%endif
