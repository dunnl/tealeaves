From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Classes.Decorated.Functor
  Classes.Decorated.Monad
  Classes.Traversable.Functor
  Classes.Traversable.Monad
  Classes.DT.Functor
  Classes.DT.Monad
  Definitions.Natural
  Functors.Identity
  Functors.Batch
  Functors.Compose
  Functors.Constant
  Functors.List
  Functors.Sets
  Theory.List
  Theory.Traversable.Functor
  Theory.Traversable.Monad
  Theory.DT.Functor
  Theory.DT.Monad.

Module Notations.
  Export Coq.Lists.List.ListNotations. (* [] :: *)
  Export Monoid.Notations. (* Ƶ and ● *)
  Export Applicative.Notations. (* <⋆> *)
  Export Traversable.Functor.Notations. (* ⋆2 *)
  Export Traversable.Monad.Notations. (* ⋆3 *)
  Export Comonad.Notations. (* ⋆4 *)
  Export Decorated.Monad.Notations. (* ⋆5 *)
  Export DT.Functor.Notations. (* ⋆6 *)
  Export DT.Monad.Notations. (* ⋆7 *)
  Export Product.Notations. (* × *)
  Export Sets.ElNotations. (* ∈ *)
End Notations.

Module DerivedInstances.
  Export Classes.Decorated.Functor.DerivedInstances.
  Export Classes.Decorated.Monad.DerivedInstances.
  Export Classes.Traversable.Functor.DerivedInstances.
  Export Classes.Traversable.Monad.DerivedInstances.
  Export Classes.DT.Functor.DerivedInstances.
  Export Classes.DT.Monad.DerivedInstances.
End DerivedInstances.
