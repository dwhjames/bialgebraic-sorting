%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, FlexibleContexts #-}
> module OrdList(
>   module FinalCoalgebra,
>   OrdList(..), toOrdList, fromOrdList
> )
> where
> import FinalCoalgebra

%endif

%format OrdList = "\underline{" List "}"
%format ONil    = "\underline{" Nil "}"
%format OCons   = "\underline{" Cons "}"

> data OrdList list a = ONil | OCons a (list a)

> instance HFunctor OrdList where
>   hmap f ONil            = ONil
>   hmap f (OCons k list)  = OCons k (f list)


%if False

> instance (Show a, Show (l a)) ⇒ Show (OrdList l a) where
>   show ONil         =  "[]"
>   show (OCons i l)  =  show i ++ " <= " ++ show l

> toOrdList ∷ [a] → Cofix OrdList a
> toOrdList []      =  OutI ONil
> toOrdList (x:xs)  =  OutI (OCons x (toOrdList xs))

> fromOrdList ∷ Cofix OrdList a → [a]
> fromOrdList (OutI ONil)          =  []
> fromOrdList (OutI (OCons x xs))  =  x : fromOrdList xs

%endif
