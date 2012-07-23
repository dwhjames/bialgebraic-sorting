%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module Bush(Bush(..))
> where

%endif

An intermediate data structure for merge sort. This is another tree
structure, but now the elements are stored in the leaves of the tree,
rather than in the branches. A bush is a non-empty data structure.

> data Bush bush = Leaf Integer | Fork bush bush
>
> instance Functor Bush where
>   fmap _f  (Leaf a)    =  Leaf a
>   fmap f   (Fork l r)  =  Fork (f l) (f r)

%if False

> instance Show b ⇒ Show (Bush b) where
>   show (Leaf i)    =  "L" ++ show i
>   show (Fork l r)  =  "(" ++ show l ++ ")" ++ " //\\\\ " ++ "(" ++ show r ++ ")"

%endif
