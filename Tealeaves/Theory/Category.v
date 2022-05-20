(** This file contains a [Category] instance for the category of types and morphisms, the underlying category of
    the <<Tealeaves.Ordinary.*>> interface. *)
From Tealeaves Require Export
     Util.Prelude
     Classes.Category.

From Tealeaves Require
     Classes.Functor
     Classes.Monad.

(** * [Category] instance *)
Instance: Arrows Type :=
  fun (a b : Type) => a -> b.

Instance: Identities Type := @id.

Instance: Composition Type := fun A B C f g => compose f g.

Instance: Category Type.
Proof.
  intros. constructor.
  - reflexivity.
  - intros; extensionality i. reflexivity.
  - intros. extensionality i. reflexivity.
Qed.

(** * Instances for general categories *)
(******************************************************************************)
Instance Fmap_ordinary `{H : Functor.Fmap F} : Category.Fmap F := H.

Instance Functor_ordinary `{Functor.Functor F} : Category.Functor F Fmap_ordinary :=
  {| Category.fmap_id := Functor.fun_fmap_id F;
     Category.fmap_fmap := fun a b c f g => Functor.fun_fmap_fmap F;
  |}.

Instance Natural_ordinary `{H : Functor.Natural F G ϕ} : Category.Natural ϕ := @Functor.natural F _ G _ ϕ H.

Instance Join_ordinary `{H : Monad.Join T} : Category.Join T := H.

Instance Ret_ordinary `{H : Monad.Return T} : Category.Return T := H.

Instance Monad_ordinary `{H : Monad.Monad T} : Category.Monad T.
Proof.
  constructor.
  - apply Functor_ordinary.
  - apply Natural_ordinary.
  - apply Natural_ordinary.
  - apply (Monad.mon_join_fmap_ret T).
  - apply (Monad.mon_join_ret T).
  - apply (Monad.mon_join_join T).
Qed.
