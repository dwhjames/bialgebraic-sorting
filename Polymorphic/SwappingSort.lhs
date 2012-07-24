%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, Rank2Types, TypeOperators #-}
> module SwappingSort
> where
> import InitialAlgebra
> import FinalCoalgebra
> import List
> import OrdList

%endif

> swap ∷ List (OrdList l) :→ OrdList (List l)
> swap Nil            =  ONil
> swap (Cons a ONil)  =  OCons a Nil
> swap (Cons a (OCons b x))
>   | a <= b          =  OCons a (Cons b x)
>   | otherwise       =  OCons b (Cons a x)


> bub  ∷  List (OrdList (Fix List)) :→ OrdList (Fix List)
> bub Nil            =  ONil
> bub (Cons a ONil)  =  OCons a (In Nil)
> bub (Cons a (OCons b x))
>   | a <= b         =  OCons a (In (Cons b x))
>   | otherwise      =  OCons b (In (Cons a x))


> bubble  ∷  Fix List :→ OrdList (Fix List)
> bubble = fold bub


> bubbleSort  ∷  Fix List :→ Cofix OrdList
> bubbleSort  =  unfold bubble


> bubbleSort'  ∷  Fix List :→ Cofix OrdList
> bubbleSort'  =  unfold (fold (hmap inn . swap))


> naiveIns  ∷  List (Cofix OrdList) :→ OrdList (List (Cofix OrdList))
> naiveIns Nil                   =  ONil
> naiveIns (Cons a (OutI ONil))  =  OCons a Nil
> naiveIns (Cons a (OutI (OCons b x)))
>   | a <= b                     =  OCons a (Cons b x)
>   | otherwise                  =  OCons b (Cons a x)


> naiveInsert  ∷  List (Cofix OrdList) :→ Cofix OrdList
> naiveInsert  =  unfold naiveIns


> naiveInsertionSort  ∷  Fix List :→ Cofix OrdList
> naiveInsertionSort  =  fold naiveInsert


> naiveInsertionSort'  ∷  Fix List :→ Cofix OrdList
> naiveInsertionSort'  =  fold (unfold (swap . hmap out))
