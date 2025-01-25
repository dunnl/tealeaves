From Tealeaves Require Export
  Classes.Functor.

#[local] Generalizable Variables F G.

  (** It is sometimes necessary to explicitly unfold
<<compose>> in the type arguments of a <<compose>> in order to rewrite
with naturality laws without using <<Set Keyed Unification>>. *)
Ltac unfold_compose_in_compose :=
  repeat match goal with
    | |- context [@compose ?A ?B ?C] =>
        let A' := eval unfold compose in A in
          let B' := eval unfold compose in B in
            let C' := eval unfold compose in C in
              progress (change (@compose A B C) with
                  (@compose A' B' C'))
    end.

(** * The Composition of Two Functors *)
(**********************************************************************)
Section Functor_composition.

  Context
    (G F: Type -> Type)
    `{Functor F}
    `{Functor G}.

  (* bump up the weight from 2~>3 to encourage using <Map_compose>
     only as a last resort during typeclass resolution *)
  #[export] Instance Map_compose: Map (G ∘ F) | 3 :=
    fun A B f => map (F := G) (map (F := F) f).

  #[export, program] Instance Functor_compose: Functor (G ∘ F).

  Solve Obligations with
    (intros; unfold transparent tcs;
     unfold_compose_in_compose;
     (do 2 rewrite fun_map_id) +
        (do 2 rewrite fun_map_map);
     reflexivity).

End Functor_composition.

(** ** Composition with the Identity Functor *)
(**********************************************************************)
Require Import Tealeaves.Functors.Identity.

Section lemmas.

  Context
    `{Functor F}.

  Lemma Map_compose_id1:
    Map_compose (fun A => A) F = @map F _.
  Proof.
    reflexivity.
  Qed.

  Lemma Map_compose_id2:
    Map_compose F (fun A => A) = @map F _.
  Proof.
    reflexivity.
  Qed.

  Lemma map_compose_id1:
    forall {A B: Type} (f: A -> B),
      @map ((fun A => A) ∘ F)
        (Map_compose (fun A => A) F) A B f = @map F _ A B f.
  Proof.
    reflexivity.
  Qed.

  Lemma map_compose_id2:
    forall {A B: Type} (f: A -> B),
      @map (F ∘ (fun A => A))
        (Map_compose F (fun A => A)) A B f = @map F _ A B f.
  Proof.
    reflexivity.
  Qed.

End lemmas.

Import Functor.Notations.

(** ** Composition of Natural Transformations *)
(**********************************************************************)
(* Do not export this instance or typeclass resolution goes hog wild *)
#[local] Instance Natural_compose_Natural
  `{Map F1} `{Map F2} `{Map F3}
  (ϕ1: F1 ⇒ F2)
  (ϕ2: F2 ⇒ F3)
  `{! Natural ϕ1}
  `{! Natural ϕ2}:
  Natural (F := F1) (G := F3) (fun A => ϕ2 A ∘ ϕ1 A).
Proof.
  assert (Functor F1) by now inversion Natural0.
  assert (Functor F3) by now inversion Natural1.
  constructor; try typeclasses eauto.
  intros.
  reassociate <- on left.
  rewrite (natural (ϕ := ϕ2)).
  reassociate -> on left.
  rewrite (natural (ϕ := ϕ1)).
  reflexivity.
Qed.
