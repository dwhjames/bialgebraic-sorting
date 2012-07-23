%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module List1(
>   module InitialAlgebra,
>   List1(..), toList1, fromList1
> )
> where
> import InitialAlgebra

%endif

The base functor for non-empty lists.

> data List1 list1  = Single Integer | Push Integer list1
>
> instance Functor List1 where
>   fmap _f  (Single i)  =  Single i
>   fmap f   (Push i l)  =  Push i (f l)


%if False

> instance Show l ⇒ Show (List1 l) where
>   show (Single i)  =  show i ++ " : []"
>   show (Push i l)  =  show i ++ " : " ++ show l

> toList1 ∷ [Integer] → Fix List1
> toList1 []      =  error "toList1: empty list"
> toList1 [x]     =  In (Single x)
> toList1 (x:xs)  =  In (Push x (toList1 xs))

> fromList1 ∷ Fix List1 → [Integer]
> fromList1 (In (Single i))  =  [i]
> fromList1 (In (Push i l))  =  i : fromList1 l

%endif
