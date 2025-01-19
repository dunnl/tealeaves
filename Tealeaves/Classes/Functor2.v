From Tealeaves Require Export
  Classes.Functor.

#[local] Generalizable Variables F G A B.

(** * Endofunctors *)
(******************************************************************************)
Class Map2 (F: Type -> Type -> Type): Type :=
  map2: forall (A1 B1 A2 B2: Type) (f1: A1 -> B1) (f2: A2 -> B2),
      F A1 A2 -> F B1 B2.

#[global] Arguments map2 {F}%function_scope {Map2} {A1 B1 A2 B2}%type_scope (f1 f2)%function_scope.

Class Functor2 (F: Type -> Type -> Type) `{map2_F: Map2 F}: Type :=
  { fun2_map_id: forall (A1 A2: Type),
      map2 (@id A1) (@id A2) = @id (F A1 A2);
    fun2_map_map: forall (A1 B1 C1 A2 B2 C2: Type)
                    (f1: A1 -> B1) (g1: B1 -> C1)
                    (f2: A2 -> B2) (g2: B2 -> C2),
      map2 g1 g2 ∘ map2 f1 f2 = map2 (g1 ∘ f1) (g2 ∘ f2);
  }.
