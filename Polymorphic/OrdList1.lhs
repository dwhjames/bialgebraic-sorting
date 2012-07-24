%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, FlexibleContexts #-}
> module OrdList1(
>   module FinalCoalgebra,
>   OrdList1(..), toOrdList1, fromOrdList1
> )
> where
> import FinalCoalgebra

%endif

> data OrdList1 list1 a = OSingle a | OPush a (list1 a)
>
> instance HFunctor OrdList1 where
>   hmap _f  (OSingle i)  =  OSingle i
>   hmap f   (OPush i l)  =  OPush i (f l)


%if False

> instance (Show a, Show (l a)) ⇒ Show (OrdList1 l a) where
>   show (OSingle i)  =  show i ++ " <= []"
>   show (OPush i l)  =  show i ++ " <= " ++ show l

> toOrdList1 ∷ [a] -> Cofix OrdList1 a
> toOrdList1 []      =  error "toOrdList1: empty list"
> toOrdList1 [x]     =  OutI (OSingle x)
> toOrdList1 (x:xs)  =  OutI (OPush x (toOrdList1 xs))

> fromOrdList1 ∷ Cofix OrdList1 a → [a]
> fromOrdList1 (OutI (OSingle i))  =  [i]
> fromOrdList1 (OutI (OPush i l))  =  i : fromOrdList1 l

%endif
