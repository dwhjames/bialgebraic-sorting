%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module MergeSort
> where
> import InitialAlgebra
> import Para
> import Copointed
> import FinalCoalgebra
> import Apo
> import Pointed
> import List1
> import Bush
> import Intermediate
> import OrdList1

%endif


Phase 1


> stem ∷ List1 (Copointed Bush f) :→ Bush (Pointed List1 f)
> stem (Single a)                   =  Leaf a
> stem (Push a (As t (Leaf _b)))    =  Fork (Play (Single a)) (Stop t)
> stem (Push a (As _t (Fork x y)))  =  Fork (Play (Push a y)) (Stop x)


> sep ∷ List1 (Bush (Fix List1)) :→ Bush (Fix List1)
> sep (Single a)           =  Leaf a
> sep (Push a (Leaf b))    =  Fork (In (Single a)) (In (Single b))
> sep (Push a (Fork t u))  =  Fork (In (Push a u)) t
>
> cleave  ∷  Fix List1 :→ Bush (Fix List1)
> cleave  =  fold sep


> bushIns  ∷  List1 (Copointed Bush (Cofix Bush)) :→ Bush (Pointed List1 (Cofix Bush))
> bushIns (Single a)                   =  Leaf a
> bushIns (Push a (As t (Leaf _b)))    =  Fork (Play (Single a)) (Stop t)
> bushIns (Push a (As _t (Fork x y)))  =  Fork (Play (Push a y)) (Stop x)
>
> bushInsert  ∷  List1 (Cofix Bush) :→ Cofix Bush
> bushInsert  =  apo (bushIns . hmap (id /\ out))


Phase 2


> prune ∷ Bush (Copointed OrdList1 f) :→ OrdList1 (Pointed Bush f)
> prune (Leaf a)  =  OSingle a
> prune (Fork (As _t (OSingle a)) (As _u (OSingle b)))
>   | a <= b      =  OPush a (Play (Leaf b))
>   | otherwise   =  OPush b (Play (Leaf a))
> prune (Fork (As t (OSingle a)) (As u (OPush b u')))
>   | a <= b      =  OPush a (Stop u)
>   | otherwise   =  OPush b (Play (Fork t u'))
> prune (Fork (As t (OPush a t')) (As u (OSingle b)))
>   | a <= b      =  OPush a (Play (Fork t' u))
>   | otherwise   =  OPush b (Stop t)
> prune (Fork (As t (OPush a t')) (As u (OPush b u')))
>   | a <= b      =  OPush a  (Play (Fork t'  u ))
>   | otherwise   =  OPush b  (Play (Fork t   u'))


> fuse  ∷  Bush (Copointed OrdList1 (Fix Bush)) :→ OrdList1 (Fix Bush)
> fuse (Leaf a)  =  OSingle a
> fuse (Fork (As _t (OSingle a)) (As _u (OSingle b)))
>   | a <= b     =  OPush a (In (Leaf b))
>   | otherwise  =  OPush b (In (Leaf a))
> fuse (Fork (As t (OSingle a)) (As u (OPush b u')))
>   | a <= b     =  OPush a u
>   | otherwise  =  OPush b (In (Fork t u'))
> fuse (Fork (As t (OPush a t')) (As u (OSingle b)))
>   | a <= b     =  OPush a (In (Fork t' u))
>   | otherwise  =  OPush b t
> fuse (Fork (As t (OPush a t')) (As u (OPush b u')))
>   | a <= b     =  OPush a  (In (Fork t'  u ))
>   | otherwise  =  OPush b  (In (Fork t   u'))
>
> bushMin  ∷  Fix Bush :→ OrdList1 (Fix Bush)
> bushMin  =  para fuse


> knit  ∷   Bush (Copointed OrdList1 (Cofix OrdList1))
>       :→  OrdList1 (Pointed Bush (Cofix OrdList1))
> knit (Leaf a)  =  OSingle a
> knit (Fork (As _t (OSingle a)) (As _u (OSingle b)))
>   | a <= b     =  OPush a (Play (Leaf b))
>   | otherwise  =  OPush b (Play (Leaf a))
> knit (Fork (As t (OSingle a)) (As u (OPush b u')))
>   | a <= b     =  OPush a (Stop u)
>   | otherwise  =  OPush b (Play (Fork t u'))
> knit (Fork (As t (OPush a t')) (As u (OSingle b)))
>   | a <= b     =  OPush a (Play (Fork t' u))
>   | otherwise  =  OPush b (Stop t)
> knit (Fork (As t (OPush a t')) (As u (OPush b u')))
>   | a <= b     =  OPush a  (Play (Fork t'  u ))
>   | otherwise  =  OPush b  (Play (Fork t   u'))
>
> merge  ∷ Bush (Cofix OrdList1) :→ Cofix OrdList1
> merge = apo (knit . hmap (id /\ out))


> mergeSort  ∷  Fix List1 :→ Cofix OrdList1
> mergeSort  =  fold merge
>            .  downcast
>            .  unfold cleave


> bushSort  ∷  Fix List1 :→ Cofix OrdList1
> bushSort  =  unfold bushMin
>           .  downcast
>           .  fold bushInsert
