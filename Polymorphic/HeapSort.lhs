%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module HeapSort
> where
> import InitialAlgebra
> import Para
> import Copointed
> import FinalCoalgebra
> import Apo
> import Pointed
> import List
> import ListH
> import Tree
> import Intermediate
> import OrdList

%endif


> type Heap = Tree


Phase 1


> pile ∷ List (Copointed Heap f) :→ Heap (Pointed List f)
> pile Nil                    =  Empty
> pile (Cons a (As t Empty))  =  Node (Stop t) a (Stop t)
> pile (Cons a (As t (Node l b r)))
>   | a <= b                  =  Node (Play (Cons b r)) a (Stop l)
>   | otherwise               =  Node (Play (Cons a r)) b (Stop l)


> divvy ∷ List (Heap (Fix List)) :→ Heap (Fix List)
> divvy Nil             =  Empty
> divvy (Cons a Empty)  =  Node (In Nil) a (In Nil)
> divvy (Cons a (Node l b r))
>   | a <= b            =  Node (In (Cons b r)) a l
>   | otherwise         =  Node (In (Cons a r)) b l


> heapIns  ∷   List (Cofix Heap)
>          :→  Heap (Pointed List (Cofix Heap))
> heapIns Nil                    =  Empty
> heapIns (Cons a (OutI Empty))  =  Node (Stop (OutI Empty)) a (Stop (OutI Empty))
> heapIns (Cons a (OutI (Node l b r)))
>   | a <= b                     =  Node (Play (Cons b r)) a (Stop l)
>   | otherwise                  =  Node (Play (Cons a r)) b (Stop l)
>
> heapInsert  ∷  List (Cofix Heap) :→ Cofix Heap
> heapInsert  =  apo heapIns


> heapIns'  ∷   ListH  (Cofix Heap)
>           :→  Heap   (Pointed ListH (Cofix Heap))
> heapIns' NilH                    =  Empty
> heapIns' (ConsH a (OutI Empty))  =  Node (Stop (OutI Empty)) a (Stop (OutI Empty))
> heapIns' (ConsH a (OutI (Node l b r)))
>   | a <= b                       =  Node (Play (Sink b r)) a (Stop l)
>   | otherwise                    =  Node (Play (ConsH a r)) b (Stop l)
> heapIns' (Sink a (OutI (Node l b r)))
>                                  =  Node (Play (Sink b r)) a (Stop l)


Phase 2


> sift ∷ Heap (Copointed OrdList f) :→ OrdList (Pointed Heap f)
> sift Empty                           =  ONil
> sift (Node (As _l ONil) a (As r _))  =  OCons a (Stop r)
> sift (Node (As l _) a (As _r ONil))  =  OCons a (Stop l)
> sift (Node (As l (OCons b l')) a (As r (OCons c r')))
>   | b <= c                           =  OCons a (Play (Node l' b r ))
>   | otherwise                        =  OCons a (Play (Node l  c r'))


> meld  ∷   Heap (Copointed OrdList (Fix Heap))
>       :→  OrdList (Fix Heap)
> meld Empty                           =  ONil
> meld (Node (As _l ONil) a (As r _))  =  OCons a r
> meld (Node (As l _) a (As _r ONil))  =  OCons a l
> meld (Node (As l (OCons b l')) a (As r (OCons c r')))
>   | b <= c                           =  OCons a (In (Node l' b r ))
>   | otherwise                        =  OCons a (In (Node l  c r'))
>
> heapMin  ∷  Fix Heap :→ OrdList (Fix Heap)
> heapMin  =  para meld


> blend  ∷   Heap     (Copointed OrdList  (Cofix OrdList))
>        :→  OrdList  (Pointed Heap       (Cofix OrdList))
> blend Empty                          =  ONil
> blend (Node (As l ONil) a (As r _))  =  OCons a (Stop r)
> blend (Node (As l _) a (As r ONil))  =  OCons a (Stop l)
> blend (Node (As l (OCons b l')) a (As r (OCons c r')))
>   | b <= c                           =  OCons a (Play (Node l' b r ))
>   | otherwise                        =  OCons a (Play (Node l  c r'))
>
> tmerge ∷ Heap (Cofix OrdList) :→ Cofix OrdList
> tmerge = apo (blend . hmap (id /\ out))


> heapSort  ∷  Fix List :→ Cofix OrdList
> heapSort  =  unfold heapMin . downcast . fold heapInsert


> mingleSort  ∷  Fix List :→ Cofix OrdList
> mingleSort  =  fold (apo (blend . hmap (id /\ out)))
>             .  downcast
>             .  unfold (fold divvy)
