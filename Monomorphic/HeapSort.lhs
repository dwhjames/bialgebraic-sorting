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

Quicksort and treesort are \emph{sensitive} to their input. Imposing a
horizontal (total) ordering to the tree offers us no flexibility in
how to arrange the elements, thus an unfavourably ordered input list
leads to an unbalanced tree and linear, rather than logarithmic,
operations. (Of course, we could use some balancing scheme.) For this
section we will use |Heap| as our intermediate data structure,

> type Heap = Tree

where the element of a tree node in a heap is less than or equal to
all the elements of the subtrees. This heap property requires that
trees are \emph{vertically} ordered---a more `flexible', partial
order.

Phase 1

The type of our natural transformation, which we will call~|pile|,
will be the same as |sprout| for quick (tree) sort, modulo type
synonyms. However, rather than its implementation being dictated by
the search tree property, we have a choice to make for |pile|.

> pile ∷ List (Copointed Heap x) → Heap (Pointed List x)
> pile Nil                    =  Empty
> pile (Cons a (As t Empty))  =  Node (Stop t) a (Stop t)
> pile (Cons a (As t (Node l b r)))
>   | a <= b                  =  Node (Play (Cons b r)) a (Stop l)
>   | otherwise               =  Node (Play (Cons a r)) b (Stop l)

There is no choice in the first two cases; it is solely in the third
case: we always add to the right and then swap left with right. By
doing so, we will end up building a heap that is a \emph{Braun tree},
where a node's right subtree has, at most, one element less than its
left. Thus we ensure that our heapsort is \emph{insensitive} to the
input, in contrast to quick (tree) sort.

If we instantiate |pile| to the initial algebra view, we get:

> divvy ∷ List (Heap (Fix List)) → Heap (Fix List)
> divvy Nil             =  Empty
> divvy (Cons a Empty)  =  Node (In Nil) a (In Nil)
> divvy (Cons a (Node l b r))
>   | a <= b            =  Node (In (Cons b r)) a l
>   | otherwise         =  Node (In (Cons a r)) b l

It is related to the |pivot| function for quick sort. There, we were
building two lists partitioned around a pivot, but here we are
selecting the least element and collecting the rest into two lists. We
have named the synthesised algebra |divvy|, meaning to divide up.

The function |fold divvy ∷ Fix List → Heap (Fix List)|, selects the
least element and divides the remaining list into two parts of
balanced length (using Braun's trick). The unfold of |divvy| constructs a
heap by repeated selection, rather than by repeated insertion. This is
rather reminiscent of selection and insertion sort, and is an
intriguing variant on building a heap.


If we instantiate |pile| to the final coalgebra view, we get:

> heapIns  ∷  List (Cofix Heap)
>          →  Heap (Pointed List (Cofix Heap))
> heapIns Nil                    =  Empty
> heapIns (Cons a (OutI Empty))  =  Node (Stop (OutI Empty)) a (Stop (OutI Empty))
> heapIns (Cons a (OutI (Node l b r)))
>   | a <= b                     =  Node (Play (Cons b r)) a (Stop l)
>   | otherwise                  =  Node (Play (Cons a r)) b (Stop l)

We have called it |heapIns| as |apo heapIns ∷ List (Cofix Heap) →
Cofix Heap| is the heap insertion function. Thus a |fold| of an |apo|
will build a heap by repeated insertion. (It is instructive to compare
|heapIns| to |treeIns|.)

> heapInsert  ∷  List (Cofix Heap) → Cofix Heap
> heapInsert  =  apo heapIns

As an aside, we can actually do slightly better: sinking the
element,~|b|, into the right subheap~|r|, does not require any
comparisons as the heap property ensures that~|b| is smaller than the
elements in~|r|. One solution would be to introduce a variant of
lists, |ListH|, with a third constructor |Sink|, to signal when no
more comparisons are needed. We can then write |fold (apo heapIns') ·
toList'|, where,

> heapIns'  ∷  ListH  (Cofix Heap)
>           →  Heap   (Pointed ListH (Cofix Heap))
> heapIns' NilH                    =  Empty
> heapIns' (ConsH a (OutI Empty))  =  Node (Stop (OutI Empty)) a (Stop (OutI Empty))
> heapIns' (ConsH a (OutI (Node l b r)))
>   | a <= b                       =  Node (Play (Sink b r)) a (Stop l)
>   | otherwise                    =  Node (Play (ConsH a r)) b (Stop l)
> heapIns' (Sink a (OutI (Node l b r)))
>                                  =  Node (Play (Sink b r)) a (Stop l)


Phase 2

Our natural transformation for describing one step of turning a heap
into a list will take an interesting divergence from |wither| in the
case of quick (tree) sort. There, |wither| described one step of an
in-order traversal. The search tree property provided the correct
ordering for the output list, so no further comparisons were needed.
The choice afforded to us by the heap property now means that further
comparisons \emph{are} needed, to obtain a sorted list.

> sift ∷ Heap (Copointed OrdList x) → OrdList (Pointed Heap x)
> sift Empty                           =  ONil
> sift (Node (As _l ONil) a (As r _))  =  OCons a (Stop r)
> sift (Node (As l _) a (As _r ONil))  =  OCons a (Stop l)
> sift (Node (As l (OCons b l')) a (As r (OCons c r')))
>   | b <= c                           =  OCons a (Play (Node l' b r ))
>   | otherwise                        =  OCons a (Play (Node l  c r'))

The fourth case is where these comparisons must be made: we need to
pick the next minimum element from the left or the right. When
constructing the heap node to continue with, we have the option to
swap left with right, but this buys us nothing.

If we instantiate |sift| to the initial algebra view, we get:

> meld  ∷  Heap (Copointed OrdList (Fix Heap))
>       →  OrdList (Fix Heap)
> meld Empty                           =  ONil
> meld (Node (As _l ONil) a (As r _))  =  OCons a r
> meld (Node (As l _) a (As _r ONil))  =  OCons a l
> meld (Node (As l (OCons b l')) a (As r (OCons c r')))
>   | b <= c                           =  OCons a (In (Node l' b r ))
>   | otherwise                        =  OCons a (In (Node l  c r'))

We have called it |meld| as |para meld :: Fix Heap → OrdList (Fix
Heap)| is a function one might find in a priority queue library, often
called |deleteMin|. It returns the minimum element at the root and a
new heap that is the melding of the left and right subheaps. This
|Heap|-algebra is related to treesort's |SearchTree|-algebra, |shear|,
but due to the contrasting ordering schemes the mechanics of
extracting the next element are quite different.

> heapMin  ∷  Fix Heap → OrdList (Fix Heap)
> heapMin  =  para meld


If we instantiate |sift| to the final coalgebra view, we get:

> blend  ∷  Heap     (Copointed OrdList  (Cofix OrdList))
>        →  OrdList  (Pointed Heap       (Cofix OrdList))
> blend Empty                          =  ONil
> blend (Node (As l ONil) a (As r _))  =  OCons a (Stop r)
> blend (Node (As l _) a (As r ONil))  =  OCons a (Stop l)
> blend (Node (As l (OCons b l')) a (As r (OCons c r')))
>   | b <= c                           =  OCons a (Play (Node l' b r ))
>   | otherwise                        =  OCons a (Play (Node l  c r'))

Note that |apo (blend · fmap (id /\ out)) :: Heap (Cofix OrdList) →
Cofix OrdList| is really a ternary version of merge, just as |apo
glue| for quick sort was a ternary append.

> tmerge ∷ Heap (Cofix OrdList) → Cofix OrdList
> tmerge = apo (blend . fmap (id /\ out))


Fully assembled, our heapsort is defined as:

> heapSort  ∷  Fix List → Cofix OrdList
> heapSort  =  unfold heapMin . downcast . fold heapInsert

We use the names |deleteMin| and |heapInsert| to emphasise that this
is exactly the expected algorithm for a function named |heapSort|.

The dual to heapsort is a strange creature, for which we will invent
the name minglesort:

> mingleSort  ∷  Fix List → Cofix OrdList
> mingleSort  =  fold (apo (blend . fmap (id /\ out)))
>             .  downcast
>             .  unfold (fold divvy)

It uses the same intermediate data structure as heapsort, yet it
behaves suspiciously like mergesort: the input list is recursively
divided into two parts and then merged back together. This, of course
is not quite true, as it actually divides into three parts: two lists
of balanced length along with the minimum element. The merging phase
is a similarly trimerous operation.
