%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module Apo (module Coproduct, apo)
> where
> import FinalCoalgebra
> import Coproduct

%endif

Apomorphisms generalise anamorphisms---unfolds---and can be used to
provide a stopping condition on production, which in turn improves the
efficiency of the algorithm. Also by analogy, we will call the
argument to an apomorphism a coalgebra.

> apo  ∷  (Functor f) ⇒ (a → f (Cofix f :+: a)) → (a → Cofix f)
> apo f  =  outI . fmap (id \/ apo f) . f

As expected, |apo| is similar to |unfold|, but the corecursion is
split into two branches, with no recursive call on the left.
Another name often given to |apo| is |corecurse|.

Apomorphisms can also be defined in terms of unfolds. However, this is
\emph{not} as efficient: recursion continues in |stop| mode, copying
the data step-by-step:

> apo'  ∷  (Functor f) ⇒ (a → f (Cofix f :+: a)) → (a → Cofix f)
> apo' f  =  unfold ((fmap (stop) . out) \/ f) . play
