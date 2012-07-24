%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module List(
>   module InitialAlgebra,
>   List(..), toList, fromList
> )
> where
> import InitialAlgebra

%endif

As an example of building a recursive datatype, consider the functor

> data List list = Nil | Cons Integer list

where we use |Integer| to represent some ordered key type. Note that
we deliberately introduce lists that are not parametric because this
simplifies the exposition, and parametricity with type class
constraints can be reintroduced without affecting the underlying
theory. As its name suggests, this datatype is similar to that of
lists with elements of type |Integer|. In this case, however, the
recursive argument to |Cons| has been abstracted into a type
parameter. We call such a datatype the \emph{base functor} of a
recursive datatype, and the functorial action of |fmap| marks the
point of recursion within the datatype:

> instance Functor List where
>   fmap _f  Nil         =  Nil
>   fmap f   (Cons i x)  =  Cons i (f x)

We then tie the recursive knot by taking the least fixed point |Fix
List|, which represents the type of finite lists with elements of type
|Integer|.

%if False

> instance Show l ⇒ Show (List l) where
>   show Nil         =  "[]"
>   show (Cons i l)  =  show i ++ " : " ++ show l

> toList ∷ [Integer] → Fix List
> toList []      =  In Nil
> toList (x:xs)  =  In (Cons x (toList xs))

> fromList ∷ Fix List → [Integer]
> fromList (In Nil)          =  []
> fromList (In (Cons x xs))  =  x : fromList xs

%endif

