%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module QuickTreeSort
> where
> import InitialAlgebra
> import Para
> import Copointed
> import FinalCoalgebra
> import Apo
> import Pointed
> import List
> import Tree
> import Intermediate
> import OrdList

%endif


> type SearchTree  =  Tree


Phase 1

> sprout ∷ List (Copointed SearchTree f) :→ SearchTree (Pointed List f)
> sprout Nil                    =  Empty
> sprout (Cons a (As t Empty))  =  Node (Stop t) a (Stop t)
> sprout (Cons a (As t (Node l b r)))
>   | a <= b                    =  Node (Play (Cons a l)) b (Stop r)
>   | otherwise                 =  Node (Stop l) b (Play (Cons a r))


> pivot ∷ List (SearchTree (Fix List)) :→ SearchTree (Fix List)
> pivot Nil             =  Empty
> pivot (Cons a Empty)  =  Node (In Nil) a (In Nil)
> pivot (Cons a (Node l b r))
>   | a <= b            =  Node (In (Cons a l)) b r
>   | otherwise         =  Node l b (In (Cons a r))
>
> partition  ∷  Fix List :→ SearchTree (Fix List)
> partition  =  fold pivot


> treeIns  ∷   List (Cofix SearchTree)
>          :→  SearchTree (Pointed List (Cofix SearchTree))
> treeIns Nil                    =  Empty
> treeIns (Cons a (OutI Empty))  =  Node (Stop (OutI Empty)) a (Stop (OutI Empty))
> treeIns (Cons a (OutI (Node l b r)))
>   | a <= b                     =  Node (Play (Cons a l)) b (Stop r)
>   | otherwise                  =  Node (Stop l) b (Play (Cons a r))
>
> treeInsert  ∷  List (Cofix SearchTree) :→ Cofix SearchTree
> treeInsert  =  apo treeIns


> grow, grow'  ∷  Fix List :→ Cofix SearchTree
> grow   =  unfold (para (hmap (id \/ inn) . sprout))
>
> grow'  =  fold (apo (sprout . hmap (id /\ out)))


Phase 2

> wither ∷ SearchTree (Copointed OrdList f) :→ OrdList (Pointed SearchTree f)
> wither Empty                                   =  ONil
> wither (Node (As _l ONil) a (As r _))          =  OCons a (Stop r)
> wither (Node (As _l (OCons b l')) a (As r _))  =  OCons b (Play (Node l' a r))


> shear  ∷   SearchTree (Copointed OrdList (Fix SearchTree))
>        :→  OrdList (Fix SearchTree)
> shear Empty                                   =  ONil
> shear (Node (As _l ONil) a (As r _))          =  OCons a r
> shear (Node (As _l (OCons b l')) a (As r _))  =  OCons b (In (Node l' a r))
>
> treeMin ∷ Fix SearchTree :→ OrdList (Fix SearchTree)
> treeMin = para shear


> glue  ∷   SearchTree (Cofix OrdList)
>       :→  OrdList (Pointed SearchTree (Cofix OrdList))
> glue Empty                          =  ONil
> glue (Node (OutI ONil) a r)         =  OCons a (Stop r)
> glue (Node (OutI (OCons b l)) a r)  =  OCons b (Play (Node l a r))
>
> tappend ∷ SearchTree (Cofix OrdList) :→ Cofix OrdList
> tappend = apo glue


> flatten, flatten'  ∷  Fix SearchTree :→ Cofix OrdList
> flatten  =  fold (apo (wither . hmap (id /\ out)))
>
> flatten'  =  unfold (para (hmap (id \/ inn) . wither))


> quickSort, treeSort  ∷  Fix List :→ Cofix OrdList
> quickSort  =  flatten . downcast . grow
>
> treeSort   =  flatten' . downcast . grow'
