%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
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


> swop  ∷  List (Copointed OrdList f) :→ OrdList (Pointed List f)
> swop Nil                   =  ONil
> swop (Cons a (As x ONil))  =  OCons a (Stop x)
> swop (Cons a (As x (OCons b x')))
>   | a <= b                 =  OCons a (Stop x)
>   | otherwise              =  OCons b (Play (Cons a x'))


> ins  ∷  List (Cofix OrdList) :→  OrdList (Pointed List (Cofix OrdList))
> ins Nil                   =  ONil
> ins (Cons a (OutI ONil))  =  OCons a (Stop (OutI ONil))
> ins (Cons a (OutI (OCons b x')))
>   | a <= b                =  OCons a  (Stop (OutI (OCons b x')))
>   | otherwise             =  OCons b  (Play (Cons a x'))
>
> insert ∷ List (Cofix OrdList) :→ Cofix OrdList
> insert = apo ins
>
> insertionSort  ∷  Fix List :→ Cofix OrdList
> insertionSort  =  fold insert
>
> insertionSort'  ∷  Fix List :→ Cofix OrdList
> insertionSort'  =  fold (apo (swop . hmap (id /\ out)))



> sel ∷ List (Copointed OrdList (Fix List)) :→ OrdList (Fix List)
> sel Nil                   =  ONil
> sel (Cons a (As x ONil))  =  OCons a x
> sel (Cons a (As x (OCons b x')))
>   | a <= b                =  OCons a x
>   | otherwise             =  OCons b (In (Cons a x'))
>
> select ∷ Fix List :→ OrdList (Fix List)
> select = para sel
>
> selectionSort  ∷  Fix List :→ Cofix OrdList
> selectionSort  = unfold select
>
> selectionSort'  ∷  Fix List :→ Cofix OrdList
> selectionSort'  =  unfold (para (hmap (id \/ inn) . swop))
