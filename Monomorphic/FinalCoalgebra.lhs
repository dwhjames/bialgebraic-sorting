%if False
Sorting with Bialgebras and Distributive Laws
Ralf Hinze, Daniel W. H. James, Thomas Harper, Nicolas Wu, José Pedro Magalhães
Workshop on Generic programming, Sept. 9, 2012, Copenhagen, Denmark.

> {-# LANGUAGE UnicodeSyntax, UndecidableInstances #-}
> module FinalCoalgebra (Cofix(..), outI, unfold)
> where

%endif

Dual to folds are unfolds, also known as anamorphisms, which provide a
scheme for producing a data structure instead of consuming one. This
requires the dual view of recursive datatypes as greatest fixed points
of functors, which is defined as

> newtype Cofix f = OutI { out ∷ f (Cofix f) }

When used in a point-free manner, |OutI| will be written as |outI|.
%if False

> outI  ∷  f (Cofix f) → Cofix f
> outI  =  OutI

> instance Show (f (Cofix f)) ⇒ Show (Cofix f) where
>   show (OutI x) = show x

%endif

We can now define |unfold| in the same manner as |fold|, where the
details of the recursive scheme depend only on the base functor of the
datatype being produced:

> unfold ∷ (Functor f) ⇒ (c → f c) → (c → Cofix f)
> unfold c = OutI . fmap (unfold c) . c

Again, the placement of the recursive calls is determined by the
definition of |fmap|. As with folds, the control flow of unfolds is
determined by the base functor (and therefore the shape of the data
structure).
