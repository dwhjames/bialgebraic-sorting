%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, FlexibleContexts #-}
> module Tree(Tree(..))
> where
> import HFunctor

%endif


> data Tree tree a = Empty | Node (tree a) a (tree a)

> instance HFunctor Tree where
>   hmap _f  Empty         =  Empty
>   hmap f   (Node l k r)  =  Node (f l) k (f r)

%if False

> instance (Show a, Show (t a)) ⇒ Show (Tree t a) where
>   show Empty         =  "E"
>   show (Node l i r)  =  "(" ++ show l ++ ")" ++ " // " ++ show i ++ " \\\\ " ++ "(" ++ show r ++ ")"

%endif
