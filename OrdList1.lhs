%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module OrdList1(
>   module FinalCoalgebra,
>   OrdList1(..), toOrdList1, fromOrdList1
> )
> where
> import FinalCoalgebra

%endif

The base functor for non-empty, ordered lists.

> data OrdList1 list1  = OSingle Integer | OPush Integer list1
>
> instance Functor OrdList1 where
>   fmap _f  (OSingle i)  =  OSingle i
>   fmap f   (OPush i l)  =  OPush i (f l)


%if False

> instance Show l ⇒ Show (OrdList1 l) where
>   show (OSingle i)  =  show i ++ " <= []"
>   show (OPush i l)  =  show i ++ " <= " ++ show l

> toOrdList1 ∷ [Integer] -> Cofix OrdList1
> toOrdList1 []      =  error "toOrdList1: empty list"
> toOrdList1 [x]     =  OutI (OSingle x)
> toOrdList1 (x:xs)  =  OutI (OPush x (toOrdList1 xs))

> fromOrdList1 ∷ Cofix OrdList1 → [Integer]
> fromOrdList1 (OutI (OSingle i))  =  [i]
> fromOrdList1 (OutI (OPush i l))  =  i : fromOrdList1 l

%endif
