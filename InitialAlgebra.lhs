%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, UndecidableInstances #-}
> module InitialAlgebra (Fix(..), inn, fold)
> where

%endif

We use folds (catamorphisms) as a recursion scheme for consuming a
data structure. The recursion scheme follows the shape of the
data structure, and the details of combining the elements are given
by the \emph{algebra} of the fold.

We define recursive datatypes in such a way that we can define |fold|
once. To do this, we introduce the view of recursive datatypes as
fixpoints. First, the type

> newtype Fix f = In { inI ∷ f (Fix f) }

takes a functor to its least fixed point. When used in a point-free
manner, |In| will be written as
%format inn = in
|inn|. In a category theoretic context, |((Fix F), inn)| is
the initial algebra of the functor |F|.
%if False

> inn  ∷  f (Fix f) → Fix f
> inn  =  In

> instance Show (f (Fix f)) ⇒ Show (Fix f) where
>   show (In x) = show x

%endif

Now that datatypes and algebras are to be defined in terms of base
functors, it is possible to give a generic definition of |fold|:

> fold ∷ (Functor f) ⇒ (f a → a) → (Fix f → a)
> fold a = a . fmap (fold a) . inI

This definition of |fold| only depends on the base functor; this
determines the type of the algebra, the shape of the data structure,
and the recursive pattern over it (via the definition of |fmap|). The
control flow of any program written as a fold matches the data
structure.
