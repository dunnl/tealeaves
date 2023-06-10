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
              progress (change (@compose A B C) with (@compose A' B' C'))
    end.

(** * The composition of two functors *)
(******************************************************************************)
Section Functor_composition.

  Context
    (G F : Type -> Type)
    `{Functor F}
    `{Functor G}.

  #[export] Instance Map_compose : Map (G ∘ F) :=
    fun A B f => map G (map F f).

  #[export, program] Instance Functor_compose : Functor (G ∘ F).

  Solve Obligations with
    (intros; unfold transparent tcs;
     unfold_compose_in_compose;
     (rewrite (fun_map_id F), (fun_map_id G)) +
       (rewrite (fun_map_map G), (fun_map_map F));
     reflexivity).

End Functor_composition.

Require Import Tealeaves.Functors.Identity.

Section lemmas.

  Context
    (F : Type -> Type)
    `{Functor F}.

  Lemma map_id_l :
    forall {A B : Type} (f : A -> B),
      @map ((fun A => A) ∘ F) (Map_compose (fun A => A) F) A B f = @map F _ A B f.
  Proof.
    reflexivity.
  Qed.

  Lemma map_id_r :
    forall {A B : Type} (f : A -> B),
      @map (F ∘ (fun A => A)) (Map_compose F (fun A => A)) A B f = @map F _ A B f.
  Proof.
    reflexivity.
  Qed.

End lemmas.
