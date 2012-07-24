%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module InsertSelectSort
> where
> import InitialAlgebra
> import Para
> import Copointed
> import FinalCoalgebra
> import Apo
> import Pointed
> import List
> import OrdList

%endif

For swapping sorts, we called the natural transformation |swap|; we
will call our enriched version |swop|, for \emph{swap‘n’stop}.

> swop  ∷  List (Copointed OrdList x) → OrdList (Pointed List x)
> swop Nil                   =  ONil
> swop (Cons a (As x ONil))  =  OCons a (Stop x)
> swop (Cons a (As x (OCons b x')))
>   | a <= b                 =  OCons a (Stop x)
>   | otherwise              =  OCons b (Play (Cons a x'))

The type makes it clear that |As x _| and |Stop x| really go
hand-in-hand.

With |swap|, we had a natural transformation, |List ○ OrdList .→ OrdList ○
List|; now we have one with type, |List ○ Copointed OrdList .→ OrdList
○ Pointed List|.

If we instantiate |swop| to the final coalgebra view, we get:

> ins  ∷  List (Cofix OrdList) →  OrdList (Pointed List (Cofix OrdList))
> ins Nil                   =  ONil
> ins (Cons a (OutI ONil))  =  OCons a (Stop (OutI ONil))
> ins (Cons a (OutI (OCons b x')))
>   | a <= b                =  OCons a  (Stop (OutI (OCons b x')))
>   | otherwise             =  OCons b  (Play (Cons a x'))

The coalgebra |ins| is enriched with the ability to signal that the
recursion should stop. This signal appears in the definition of the
third case, where the element to insert, |a|, is ordered with respect
to the head of the already ordered list, so there is no more work to
be done.

Naïve insertion sort is unable to leverage the fact that the list
being inserted into is already sorted, and so it continues to scan
through the list, even after the element to insert has been placed
appropriately. With apomorphisms we can write the insertion function
as one that avoids scanning needlessly:

> insert ∷ List (Cofix OrdList) → Cofix OrdList
> insert = apo ins
>
> insertionSort  ∷  Fix List → Cofix OrdList
> insertionSort  =  fold insert
>
> insertionSort'  ∷  Fix List → Cofix OrdList
> insertionSort'  =  fold (apo (swop . fmap (id /\ out)))


Just as naïve insertion as an unfold was dual to bubble as a fold,
insertion as an apomorphism can be dualised to selection as a
paramorphism.

> sel ∷ List (Copointed OrdList (Fix List)) → OrdList (Fix List)
> sel Nil                   =  ONil
> sel (Cons a (As x ONil))  =  OCons a x
> sel (Cons a (As x (OCons b x')))
>   | a <= b                =  OCons a x
>   | otherwise             =  OCons b (In (Cons a x'))

The sole difference between |sel| and |bub| is in the case where |a <=
b|: |sel| uses the remainder of the list, supplied by the
paramorphism, rather than the result computed so far. This is why
|para sel| is the true selection function, and |fold bub| is the naïve
variant, if you will.

> select ∷ Fix List → OrdList (Fix List)
> select = para sel
>
> selectionSort  ∷  Fix List → Cofix OrdList
> selectionSort  = unfold select
>
> selectionSort'  ∷  Fix List → Cofix OrdList
> selectionSort'  =  unfold (para (fmap (id \/ inn) . swop))
