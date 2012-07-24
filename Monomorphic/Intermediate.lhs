%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax #-}
> module Intermediate(downcast)
> where
> import InitialAlgebra
> import FinalCoalgebra

%endif

Because the type declarations for the fixed points of functors are in
Haskell, the difference between greatest and least fixed points is not
obvious; the definitions are the same except for the names of the
constructors and destructors, and these two datatypes are isomorphic,
a property known as \emph{algebraic compactness}. While this is the
case for Haskell, it is not true in general and we do not depend on
this. We will therefore be explicit about whether we are working with
|Fix F| or |Cofix F| by using different types. We will explicitly
downcast when we move from |Cofix F| to |Fix F|:

> downcast  ∷  (Functor f) ⇒ Cofix f → Fix f
> downcast  =  inn . fmap downcast . out

Again, as they are the same in Haskell, this is a no-op, but in
general this is a lossy operation.
