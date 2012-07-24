%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module Para(module Product, para)
> where
> import InitialAlgebra
> import Product

%endif

Paramorphisms are a variation of catamorphisms---folds---where the
algebra is given more information about the intermediate state of the
input during the traversal. By analogy with catamorphisms, we call the
argument to a paramorphism an algebra, though this is not strictly
accurate. In a catamorphism, the algebra gets the current element and
the result computed so far; in a paramorphism, the algebra also gets
the remainder of the input. This extra parameter is used in a similar
way to a Haskell \textit{as}-pattern.

> para  ∷  (Functor f) ⇒ (f (Fix f :*: a) → a) → (Fix f → a)
> para f  =  f . fmap (id /\ para f) . inI

Note the similarity with |fold|; the important difference is in the
type of the algebra, which is now |f (Fix f :*: a) → a| instead of
just |f a → a|. In fact, |para| can be defined directly as a fold:

> para'  ∷  (Functor f) ⇒ (f (Fix f :*: a) → a) → (Fix f → a)
> para' f  =  outr . fold ((inn . fmap outl) /\ f)

Another name often given to |para| is |recurse|.
