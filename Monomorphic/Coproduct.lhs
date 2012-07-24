%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
> module Coproduct((:+:)(..), play, stop, (\/))
> where

%endif

To define apomorphisms, we will need a disjoint union type and a
combinator that destructs a sum using two functions, implementing a
case analysis:

> data a :+: b = Stop a | Play b

> (\/) ∷ (a → x) → (b → x) → (a :+: b → x)
> (f   \/ _g) (Stop  a)  =  f a
> (_f  \/ g ) (Play  b)  =  g b

We name the constructors of |:+:|, |Stop| and |Play|, alluding to
their behaviour in the context of apomorphisms. When used in a
point-free manner, |Stop| and |Play| will be written as |stop| and
|play|.

%if False

> play  ∷  b → a :+: b
> play  =  Play

> stop  ∷  a → a :+: b
> stop  =  Stop

%endif
