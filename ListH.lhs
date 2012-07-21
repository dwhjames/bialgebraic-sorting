%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module ListH(
>   module InitialAlgebra,
>   ListH(..), toListH
> )
> where
> import InitialAlgebra
> import List

%endif

> data ListH list = NilH | ConsH Integer list | Sink Integer list

> instance Functor ListH where
>   fmap _f  NilH          =  NilH
>   fmap f   (ConsH  i x)  =  ConsH  i (f x)
>   fmap f   (Sink   i x)  =  Sink   i (f x)


%if False

> toListH ∷ Fix List → Fix ListH
> toListH (In Nil)         =  In NilH
> toListH (In (Cons i x))  =  In (ConsH i (toListH x))

%endif
