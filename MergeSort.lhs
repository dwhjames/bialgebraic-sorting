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

Quick (tree) sort uses binary trees with the search tree property;
similarly, heap (mingle) sort uses binary trees with the heap
property. Merge sort uses a different tree as an intermediate data
structure, it uses a bush tree where the elements are in the leaves
rather than the branches. A consequence of this is that bush trees can
only represent non-empty collections, and therefore we must also
replace |List| and |OrdList| with non-empty variants, |List1| and
|OrdList1|.

Phase 1

We need a natural transformation build a bush:

> stem ∷ List1 (Copointed Bush x) → Bush (Pointed List1 x)
> stem (Single a)                   =  Leaf a
> stem (Push a (As t (Leaf _b)))    =  Fork (Play (Single a)) (Stop t)
> stem (Push a (As _t (Fork x y)))  =  Fork (Play (Push a y)) (Stop x)

If we instantiate |stem| to the initial algebra view, we get:

> sep ∷ List1 (Bush (Fix List1)) → Bush (Fix List1)
> sep (Single a)           =  Leaf a
> sep (Push a (Leaf b))    =  Fork (In (Single a)) (In (Single b))
> sep (Push a (Fork t u))  =  Fork (In (Push a u)) t

The fold of |sep| cleaves a list into two of equal length.

> cleave  ∷  Fix List1 → Bush (Fix List1)
> cleave  =  fold sep

If we instantiate |stem| to the final coalgebra view, we get:

> bushIns  ∷  List1 (Copointed Bush (Cofix Bush)) → Bush (Pointed List1 (Cofix Bush))
> bushIns (Single a)                   =  Leaf a
> bushIns (Push a (As t (Leaf _b)))    =  Fork (Play (Single a)) (Stop t)
> bushIns (Push a (As _t (Fork x y)))  =  Fork (Play (Push a y)) (Stop x)

We have called it |bushIns| as |apo (bushIns . fmap (id /\ out)) ∷
List1 (Cofix Bush) → Cofix Bush| is the insertion function into a
bush.

> bushInsert  ∷  List1 (Cofix Bush) → Cofix Bush
> bushInsert  =  apo (bushIns . fmap (id /\ out))

Phase 2

We need a natural transformation to flatten a bush:

> prune ∷ Bush (Copointed OrdList1 x) → OrdList1 (Pointed Bush x)
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

If we instantiate |prune| to the initial algebra, we get:

> fuse  ∷  Bush (Copointed OrdList1 (Fix Bush)) → OrdList1 (Fix Bush)
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

If we read |OrdList1 (Fix Bush)| as a min bush---we have immediate
access to the minimum element of the bush---then |fuse| combines two
min bushes into one. The paramorphism of |fuse| is the function that
turns a bush into a min bush: it extracts the minimum.

> bushMin  ∷  Fix Bush → OrdList1 (Fix Bush)
> bushMin  =  para fuse

If we instantiate |prune| to final coalgebra, we get:

> knit  ∷  Bush (Copointed OrdList1 (Cofix OrdList1))
>        →  OrdList1 (Pointed Bush (Cofix OrdList1))
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

The apomorphism of |knit| is the merge function: it takes
a pair of ordered lists and merges them into one.

> merge  ∷ Bush (Cofix OrdList1) → Cofix OrdList1
> merge = apo (knit . fmap (id /\ out))

Merge sort is then the result of recursively cleaving the input list
into a bush and then recursively merging the bush into an ordered
list.

> mergeSort  ∷  Fix List1 → Cofix OrdList1
> mergeSort  =  fold merge
>            .  downcast
>            .  unfold cleave

The dual of merge sort looks a lot like heap sort. We called the dual
of heap sort, mingle sort, as it is remarkable similar to merge sort.
Heap sort is named after its intermediate data structure, therefore we
will name the dual of merge sort, bush sort, as it is remarkably
similar to heap sort, but uses a bush as an intermediate data
structure.

> bushSort  ∷  Fix List1 → Cofix OrdList1
> bushSort  =  unfold bushMin
>           .  downcast
>           .  fold bushInsert
