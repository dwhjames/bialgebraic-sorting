%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, FlexibleContexts #-}
> module Bush(Bush(..))
> where
> import HFunctor

%endif


> data Bush bush a = Leaf a | Fork (bush a) (bush a)
>
> instance HFunctor Bush where
>   hmap _f  (Leaf a)    =  Leaf a
>   hmap f   (Fork l r)  =  Fork (f l) (f r)

%if False

> instance (Show a, Show (b a)) ⇒ Show (Bush b a) where
>   show (Leaf i)    =  "L" ++ show i
>   show (Fork l r)  =  "(" ++ show l ++ ")" ++ " //\\\\ " ++ "(" ++ show r ++ ")"

%endif
