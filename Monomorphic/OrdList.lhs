%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module OrdList(
>   module FinalCoalgebra,
>   OrdList(..), toOrdList, fromOrdList
> )
> where
> import FinalCoalgebra

%endif

First, we start by creating a new
datatype to represent the base functor of sorted lists:
%format OrdList = "\underline{" List "}"
%format ONil    = "\underline{" Nil "}"
%format OCons   = "\underline{" Cons "}"

> data OrdList list = ONil | OCons Integer list

> instance Functor OrdList where
>   fmap f ONil            = ONil
>   fmap f (OCons k list)  = OCons k (f list)

Note that |OrdList| is defined exactly like |List|, but we maintain
the invariant that the elements in a |OrdList| are sorted. As |OCons|
has only one element, how can this be? If we were to write |OrdList|
parametrically,

< data OrdList list a = ONil | OCons a (list a)

where |a| is an instance of the type class |Ord|, then the element of
|OCons| is ordered with respect to the |list| container of |a|'s. In
our simple case, the type parameter is implicitly expected to be a
container of |Integer|s.

%if False

> instance Show l ⇒ Show (OrdList l) where
>   show ONil         =  "[]"
>   show (OCons i l)  =  show i ++ " <= " ++ show l

> toOrdList ∷ [Integer] → Cofix OrdList
> toOrdList []      =  OutI ONil
> toOrdList (x:xs)  =  OutI (OCons x (toOrdList xs))

> fromOrdList ∷ Cofix OrdList → [Integer]
> fromOrdList (OutI ONil)          =  []
> fromOrdList (OutI (OCons x xs))  =  x : fromOrdList xs

%endif
