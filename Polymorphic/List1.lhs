%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, FlexibleContexts #-}
> module List1(
>   module InitialAlgebra,
>   List1(..), toList1, fromList1
> )
> where
> import InitialAlgebra

%endif

> data List1 list1 a = Single a | Push a (list1 a)
>
> instance HFunctor List1 where
>   hmap _f  (Single i)  =  Single i
>   hmap f   (Push i l)  =  Push i (f l)


%if False

> instance (Show a, Show (l a)) ⇒ Show (List1 l a) where
>   show (Single i)  =  show i ++ " : []"
>   show (Push i l)  =  show i ++ " : " ++ show l

> toList1 ∷ [a] → Fix List1 a
> toList1 []      =  error "toList1: empty list"
> toList1 [x]     =  In (Single x)
> toList1 (x:xs)  =  In (Push x (toList1 xs))

> fromList1 ∷ Fix List1 a → [a]
> fromList1 (In (Single i))  =  [i]
> fromList1 (In (Push i l))  =  i : fromList1 l

%endif
