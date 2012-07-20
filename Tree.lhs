%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module Tree(Tree(..))
> where

%endif

If we are to do better than the quadratic bound for swapping sorts, we
need sublinear insertion and selection operations. To use such
operations, we must introduce an intermediate data structure that
supports them. We do this by moving to a two-phase algorithm, where
the first phase builds such an intermediate data structure from a
list, and the second phase consumes it to produce a sorted list. Our
intermediate data structure will be binary trees with elements of type
|Integer|.

> data Tree tree = Empty | Node tree Integer tree

> instance Functor Tree where
>   fmap _f  Empty         =  Empty
>   fmap f   (Node l k r)  =  Node (f l) k (f r)

%if False

> instance Show t ⇒ Show (Tree t) where
>   show Empty         =  "E"
>   show (Node l i r)  =  "(" ++ show l ++ ")" ++ " // " ++ show i ++ " \\\\ " ++ "(" ++ show r ++ ")"

%endif
