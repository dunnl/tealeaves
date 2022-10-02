From Tealeaves Require Import
  Algebraic.Monads.Decorated.Monad
  Algebraic.Functors.Decorated.Category
  Functors.Writer
  Functors.List.

Definition DecoratedList W A := list (W * A).


Instance: forall W, Decorate W (DecoratedList W) :=
  @Decorate_compose W _ list Fmap_list (W ×) Fmap_writer Decorate_zero Decoat
