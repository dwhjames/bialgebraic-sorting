%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module Product((:*:)(..), (/\))
> where

%endif

To define paramorphisms, we will need products and a \emph{split}
combinator that builds a product from two functions:

> data a :*: b = As { outl ∷ a, outr ∷ b }

> (/\) ∷ (x → a) → (x → b) → (x → a :*: b)
> (f /\ g) x  =  As (f x) (g x)

We have named the constructor of products |As a b|, as we will later
use it like the Haskell \textit{as}-pattern: |a @ b|.