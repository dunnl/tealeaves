(** This file contains a [Category] instance for the category of types and morphisms, the underlying category of
    the <<Tealeaves.Ordinary.*>> interface. *)
From Tealeaves Require Export
     Util.Prelude Cats.Classes.

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



(*
(** * Instances for general categories *)
(******************************************************************************)
Instance Fmap_ordinary `{H : Fmap F} : Cats.Functors.Fmap F := H.

Instance Functor_ordinary `{Functor F} : Cats.Functors.Functor F Fmap_ordinary :=
  {| Cats.Functors.fmap_id := fmap_id F;
     Cats.Functors.fmap_fmap := @fmap_fmap F _ _;
  |}.

Instance Join_ordinary `{H : Join T} : Cats.Functors.Join T := H.

Instance Ret_ordinary `{H : Return T} : Cats.Functors.Return T := H.

Instance Natural_ordinary `{H : Natural T G η} : Cats.Functors.Natural η := H.

Instance Monad_ordinary `{H : Monad T} : Cats.Functors.Monad T.
Proof.
  constructor.
  - apply Functor_ordinary.
  - apply Natural_ordinary.
  - apply Natural_ordinary.
  - apply (mon_join_fmap_ret T).
  - apply (mon_join_ret T).
  - apply (mon_join_join T).
Qed.
*)
