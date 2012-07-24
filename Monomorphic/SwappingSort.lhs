%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module SwappingSort
> where
> import InitialAlgebra
> import FinalCoalgebra
> import List
> import OrdList

%endif

The following parametric function is the computational ‘essence’ of
bubble and naïve insertion sorting. It expresses the core step:
swapping \emph{adjacent} elements. It is parametric, but in a
categorical setting we will consider it natural in~|x|. Furthermore,
we will read its type as a so-called \emph{distributive law}---it
distributes the head of a list over the head of an ordered list.

> swap ∷ List (OrdList x) → OrdList (List x)
> swap Nil            =  ONil
> swap (Cons a ONil)  =  OCons a Nil
> swap (Cons a (OCons b x))
>   | a <= b          =  OCons a (Cons b x)
>   | otherwise       =  OCons b (Cons a x)

If we instantiate |swap| to the initial algebra view, we get:

> bub  ∷  List (OrdList (Fix List)) → OrdList (Fix List)
> bub Nil            =  ONil
> bub (Cons a ONil)  =  OCons a (In Nil)
> bub (Cons a (OCons b x))
>   | a <= b         =  OCons a (In (Cons b x))
>   | otherwise      =  OCons b (In (Cons a x))

|fold bub| produces the swapping behaviour seen in bubble sort.

> bubble  ∷  Fix List → OrdList (Fix List)
> bubble = fold bub

Since |bub| is a constant-time operation, bubble sort is a
quadratic-time algorithm.

> bubbleSort  ∷  Fix List → Cofix OrdList
> bubbleSort  =  unfold bubble

Bubble sort is a unfold of a fold, and it can be defined either
directly in terms of the distributive law, |swap|, or in terms of its
instantiation as an algebra.

> bubbleSort'  ∷  Fix List → Cofix OrdList
> bubbleSort'  =  unfold (fold (fmap inn . swap))


If, instead, we instantiate |swap| to the final coalgebra view, we get

> naiveIns  ∷  List (Cofix OrdList) → OrdList (List (Cofix OrdList))
> naiveIns Nil                   =  ONil
> naiveIns (Cons a (OutI ONil))  =  OCons a Nil
> naiveIns (Cons a (OutI (OCons b x)))
>   | a <= b                     =  OCons a (Cons b x)
>   | otherwise                  =  OCons b (Cons a x)

The implementations of |bub| and |naiveIns| are almost identical. The
only difference is that |In| appears on the left in |bub|, and |OutI|
appears on the right in |naiveIns|.

> naiveInsert  ∷  List (Cofix OrdList) → Cofix OrdList
> naiveInsert  =  unfold naiveIns

Why have we labelled our insertion sort as naïve? This is because we
are not making use of the fact that the incoming list is
ordered---compare the types of |bub| and |naiveIns|.

> naiveInsertionSort  ∷  Fix List → Cofix OrdList
> naiveInsertionSort  =  fold naiveInsert

Naïve insertion sort is a fold of an unfold.

> naiveInsertionSort'  ∷  Fix List → Cofix OrdList
> naiveInsertionSort'  =  fold (unfold (swap . fmap out))
