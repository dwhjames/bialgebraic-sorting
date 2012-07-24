%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, FlexibleContexts #-}
> module List(
>   module InitialAlgebra,
>   List(..), toList, fromList
> )
> where
> import InitialAlgebra

%endif

> data List list a = Nil | Cons a (list a)
>
> instance HFunctor List where
>   hmap f Nil         =  Nil
>   hmap f (Cons a x)  =  Cons a (f x)

%if False

> instance (Show (l a), Show a) ⇒ Show (List l a) where
>   show Nil         =  "[]"
>   show (Cons i l)  =  show i ++ " : " ++ show l

> toList ∷ [a] → Fix List a
> toList []      =  In Nil
> toList (x:xs)  =  In (Cons x (toList xs))

> fromList ∷ Fix List a → [a]
> fromList (In Nil)          =  []
> fromList (In (Cons x xs))  =  x : fromList xs

%endif

