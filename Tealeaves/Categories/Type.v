(** This file contains a [Category] instance for the category of types
    and morphisms, the underlying category of the
    <<Tealeaves.Ordinary.*>> interface. *)
From Tealeaves Require Export
  Classes.Category
  Classes.Functor
  Classes.Categorical.Monad.

#[local] Generalizable Variables T F G ϕ.

(** * [Category] Instance for <<Type>> *)
(**********************************************************************)
#[export] Instance: Arrows Type :=
  fun (a b: Type) => a -> b.

#[export] Instance: Identities Type := @id.

#[export] Instance: Composition Type := fun A B C f g => compose f g.

#[export] Instance: Category Type.
Proof.
  intros. constructor.
  - reflexivity.
  - intros; extensionality i. reflexivity.
  - intros. extensionality i. reflexivity.
Qed.

(** * Coercing <<Monad>> to <<Category.Monad>> *)
(**********************************************************************)
Module SpecializedToGeneral.

  #[export] Instance Fmap_ordinary `{H: Map F}:
  Category.Fmap F := H.

  #[export] Instance Functor_ordinary
    `{Functor.Functor F}:
    Category.Functor F Fmap_ordinary :=
    {| Category.fmap_id := Functor.fun_map_id;
      Category.fmap_fmap := Functor.fun_map_map;
    |}.

  #[export] Instance Natural_ordinary
    `{H: Functor.Natural F G ϕ}:
    Category.Natural ϕ := @Functor.natural F _ G _ ϕ H.

  #[export] Instance Join_ordinary
    `{H: Monad.Join T}: Category.Join T := H.

  #[export] Instance Ret_ordinary
    `{H: Monad.Return T}: Category.Return T := H.

  #[export] Instance Monad_ordinary
    `{H: Monad.Monad T}: Category.Monad T.
  Proof.
    constructor.
    - apply Functor_ordinary.
    - apply Natural_ordinary.
    - apply Natural_ordinary.
    - apply (Monad.mon_join_map_ret (T := T)).
    - apply (Monad.mon_join_ret (T := T)).
    - apply (Monad.mon_join_join (T := T)).
  Qed.

End SpecializedToGeneral.
