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

Here, we will be using the binary tree type as a binary search tree,

> type SearchTree  =  Tree

where all the values in the left subtree of a node are less than or
equal to the value at the node, and all values in the right subtree
are greater. Such a tree orders the elements horizontally, such that
an in-order traversal of the tree yields a sorted list.

Phase 1

> sprout ∷ List (Copointed SearchTree x) → SearchTree (Pointed List x)
> sprout Nil                    =  Empty
> sprout (Cons a (As t Empty))  =  Node (Stop t) a (Stop t)
> sprout (Cons a (As t (Node l b r)))
>   | a <= b                    =  Node (Play (Cons a l)) b (Stop r)
>   | otherwise                 =  Node (Stop l) b (Play (Cons a r))

The type of |sprout| gives us little choice in its implementation:
|Nil| will be replaced with |Empty|, and |Cons a Empty| will become a
tree of one element. Therefore, the construction of |l| and |r| is
determined by the search tree property and thus the value of the
pivot.

If we instantiate |sprout| to the initial algebra view, we get:

> pivot ∷ List (SearchTree (Fix List)) → SearchTree (Fix List)
> pivot Nil             =  Empty
> pivot (Cons a Empty)  =  Node (In Nil) a (In Nil)
> pivot (Cons a (Node l b r))
>   | a <= b            =  Node (In (Cons a l)) b r
>   | otherwise         =  Node l b (In (Cons a r))

In effect, |fold pivot ∷ Fix List → SearchTree (Fix List)| is a
partitioning function that takes a list and returns its last element
as a pivot, along with the two partitions of that list. At each step,
the enclosing unfold will call this fold on each of the resulting
partitions, which will ultimately yield the entire search tree.

> partition  ∷  Fix List → SearchTree (Fix List)
> partition  =  fold pivot

If we instantiate |sprout| to the final coalgebra view, we get:

> treeIns  ∷  List (Cofix SearchTree)
>          →  SearchTree (Pointed List (Cofix SearchTree))
> treeIns Nil                    =  Empty
> treeIns (Cons a (OutI Empty))  =  Node (Stop (OutI Empty)) a (Stop (OutI Empty))
> treeIns (Cons a (OutI (Node l b r)))
>   | a <= b                     =  Node (Play (Cons a l)) b (Stop r)
>   | otherwise                  =  Node (Stop l) b (Play (Cons a r))

which takes an element of the input list and inserts it one level deep
into a search tree. We call this |treeIns|, since, as we shall see,
this algebra forms the first phase of a treesort. \emph{Efficient
insertion into a tree is necessarily an apomorphism}; because of the
search tree property, the recursion need only go down one of the
branches, which is not possible with an unfold.

> treeInsert  ∷  List (Cofix SearchTree) → Cofix SearchTree
> treeInsert  =  apo treeIns


As before, the algebra and coalgebra can be written in terms of the
natural transformation, so |pivot = fmap (id \/ inn) ·
sprout| and |treeIns = sprout · fmap (id /\ out)|.  This yields two
algorithms for generating search trees:

> grow, grow'  ∷  Fix List → Cofix SearchTree
> grow   =  unfold (para (fmap (id \/ inn) . sprout))
>
> grow'  =  fold (apo (sprout . fmap (id /\ out)))

We can either recursively partition a list, building subtrees from the
resulting sublists, or start with an empty tree and repeatedly insert
the elements into it.


Phase 2

> wither ∷ SearchTree (Copointed OrdList x) → OrdList (Pointed SearchTree x)
> wither Empty                                   =  ONil
> wither (Node (As _l ONil) a (As r _))          =  OCons a (Stop r)
> wither (Node (As _l (OCons b l')) a (As r _))  =  OCons b (Play (Node l' a r))

|wither| captures the notion of flattening by traversing a tree and
collecting the elements in a list. Specifically, this function returns
the leftmost element, along with the combination of the remainder.

If we instantiate |wither| to the initial algebra view, we get:

> shear  ∷  SearchTree (Copointed OrdList (Fix SearchTree))
>           →  OrdList (Fix SearchTree)
> shear Empty                                   =  ONil
> shear (Node (As _l ONil) a (As r _))          =  OCons a r
> shear (Node (As _l (OCons b l')) a (As r _))  =  OCons b (In (Node l' a r))

To understand what is in our hands, let us look at the third case: |a|
is the root of the tree, with |l| and |r| as the left and right
subtrees; |b| is the minimum of the left subtree and |l'| the
remainder of that tree without |b|. In which case, |para shear ∷ Fix
SearchTree → OrdList (Fix SearchTree)| is the function that deletes
the minimum element from a search tree. Thus, the |fold| of this
flattens a tree by removing the elements in order. This should
surprise no one: the second phase of treesort would surely be an
in-order traversal.

> treeMin ∷ Fix SearchTree → OrdList (Fix SearchTree)
> treeMin = para shear

If we instantiate |wither| to the final coalgebra view, we get:

> glue  ∷  SearchTree (Cofix OrdList)
>          →  OrdList (Cofix OrdList :+: SearchTree (Cofix OrdList))
> glue Empty                          =  ONil
> glue (Node (OutI ONil) a r)         =  OCons a (Stop r)
> glue (Node (OutI (OCons b l)) a r)  =  OCons b (Play (Node l a r))

Note that |apo glue ∷ SearchTree (Cofix OrdList) → Cofix OrdList| is
essentially a ternary version of append: it takes a left and a right
sorted list, an element in the middle, and glues it all together. Had
we implemented this naïvely as a plain unfold, the right list would
also have to be traversed and thus induce unnecessary copying.

> tappend ∷ SearchTree (Cofix OrdList) → Cofix OrdList
> tappend = apo glue


We can again define both the algebra and the coalgebra in terms of the
natural transformation, which yields two algorithms for
flattening a tree to a list:

> flatten, flatten'  ∷  Fix SearchTree → Cofix OrdList
> flatten  =  fold (apo (wither . fmap (id /\ out)))
>
> flatten'  =  unfold (para (fmap (id \/ inn) . wither))


Quicksort works by partitioning a list based on comparison around a
pivot, and then recursively descending into the resulting sublists
until it only has singletons left. This is precisely the algorithm
used to create the tree in |grow|, and we have simply stored the
result of this recursive descent in an intermediate data structure.
The |flatten| then reassembles the lists by appending the singletons
together, now in sorted order, and continuing up the tree to append
sorted sublists together to form the final sorted list.

Dually, treesort starts with an empty tree and builds a search tree by
inserting the elements of the input list into it, which is the action
of |grow'|. The sorted list is then obtained by pulling the elements
out of the tree in order and collecting them in a list, which is how
|flatten'| produces a list. In each, tying the two phases together is
|downcast|, which is necessary because |grow| and |grow'|
\emph{produce} trees, but |flatten| and |flatten'| \emph{consume}
them.

> quickSort, treeSort  ∷  Fix List → Cofix OrdList
> quickSort  =  flatten . downcast . grow
>
> treeSort   =  flatten' . downcast . grow'
