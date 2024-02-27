From Tealeaves Require Export
  Functors.Batch
  Functors.KStore.

Import Batch.Notations.
Import Applicative.Notations.

About length_Batch.
#[local] Arguments length_Batch {A B C}%type_scope b.

(** * Batch to KStore *)
(******************************************************************************)
Section batch_to.


  Context {A B C : Type}.

  Definition Batch_to_Vector:
    Batch A B C -> @sigT nat (Vector.t A).
  Proof.
    intros b.
    induction b.
    - exists 0. apply Vector.nil.
    - destruct IHb as [n contents].
      exists (S n). apply Vector.cons. assumption.
      assumption.
  Defined.

  Definition Batch_toMakeFn:
    Batch A B C -> @sigT nat (fun n => Vector.t B n -> C).
  Proof.
    intros b.
    induction b.
    - exists 0. intros _. assumption.
    - destruct IHb as [n mk].
      exists (S n). intro v.
      remember (S n). destruct v.
      + inversion Heqn0.
      + inversion Heqn0; subst.
        apply mk.
        assumption.
        assumption.
  Defined.

  Definition deconstruct_Batch:
    Batch A B C -> @sigT nat (fun n => VEC n A * (VEC n B -> C)).
  Proof.
    intros b.
    induction b.
    - exists 0. split. apply Vector.nil. auto.
    - destruct IHb as [n [contents mk]].
      exists (S n). split.
      + apply Vector.cons. assumption. assumption.
      + intro v. apply Vector.uncons in v. destruct v.
        apply mk; auto.
  Defined.

  Definition toKStore_manual : Batch A B C -> KStore A B C.
  Proof.
    intros b.
    destruct (deconstruct_Batch b) as [len [contents mk]].
    econstructor; eassumption.
  Defined.

  Definition Batch_to_KStore: Batch A B C -> KStore A B C.
  Proof.
    eapply (runBatch (KStore A B) kstore).
  Defined.

  Definition Batch_to_Vector'
    (b: Batch A B C): Vector.t A (length_Batch b).
  Proof.
    induction b.
    - apply Vector.nil.
    - cbn.
      apply Vector.cons;
      assumption.
  Defined.

  Definition Batch_to_makeFn'
    (b: Batch A B C): Vector.t B (length_Batch b) -> C.
  Proof.
    induction b.
    - intros ?; assumption.
    - cbn.
      intro X.
      apply VectorDef.uncons in X.
      destruct X.
      apply IHb; auto.
  Defined.

  Definition Batch_to_Vector''
    (b: Batch A B C): Vector.t A (length_Batch b).
  Proof.
    induction b.
    - apply Vector.nil.
    - cbn.
      apply Vector.cons;
      assumption.
  Defined.

  Definition Batch_to_makeFn''
    (b: Batch A B C): Vector.t B (length_Batch b) -> C.
  Proof.
    induction b.
    - intros ?; assumption.
    - cbn.
      intro X.
      apply VectorDef.uncons in X.
      destruct X.
      apply IHb; auto.
  Defined.

End batch_to.

Lemma Batch_to_Vector_step {A B C}: forall (a: A) (b: Batch A B (B -> C)),
    Batch_to_Vector' (b ⧆ a) =
      Vector.cons A a (length_Batch b) (Batch_to_Vector' b).
Proof.
  reflexivity.
Qed.

Lemma Batch_to_makeFn_step {A B C}: forall (a: A) (b: Batch A B (B -> C)),
    Batch_to_makeFn' (b ⧆ a) =
      fun (v:Vector.t B (S (length_Batch b))) =>
          match (Vector.uncons v) with
          | (b', v') => Batch_to_makeFn' b v' b'
          end.
Proof.
  reflexivity.
Qed.

From Tealeaves Require Import
               Classes.Coalgebraic.TraversableFunctor
               Adapters.KleisliToCoalgebraic.TraversableFunctor.

Section aksdjflasdf.

  Context
   T (A:Type) G `{Applicative G}
     `{Kleisli.TraversableFunctor.TraversableFunctor T}.

  Definition toLen: forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := A) (toBatch t)).
  Defined.

  Definition toMake: forall (t : T A),
      Vector.t A (toLen t) -> (T A).
  Proof.
    intros t B.
    unfold toLen.
    apply (Batch_to_makeFn' (toBatch t)).
    assumption.
  Defined.

  Definition toContents: forall (t : T A),
      Vector.t A (toLen t).
  Proof.
    intro t.
    unfold toLen.
    apply (Batch_to_Vector' (toBatch t)).
  Defined.

  Definition toLen' (B:Type): forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := B) (toBatch t)).
  Defined.

  Definition toMake' B: forall (t : T A),
      Vector.t B (toLen' B t) -> (T B).
  Proof.
    intros t.
    unfold toLen.
    apply (Batch_to_makeFn' (toBatch t)).
  Defined.

  Definition toContents' B: forall (t : T A),
      Vector.t A (toLen' B t).
  Proof.
    intro t.
    apply (Batch_to_Vector' (toBatch t)).
  Defined.


  Lemma repr: forall `(t : T A),
      t = toMake t (toContents t).
  Proof.
    intros.
    unfold toMake, toContents.
    change t with (id t) at 1.
    rewrite <- trf_extract.
    unfold compose at 1.
    eapply (
        Batch_ind A A
                  (fun (T1 : Type) (b0 : Batch A A T1) =>
                     extract_Batch b0 =
                       Batch_to_makeFn' b0 (Batch_to_Vector' b0))).
    - reflexivity.
    - intros.
      rewrite Batch_to_makeFn_step.
      rewrite Batch_to_Vector_step.
      cbn.
      rewrite H5.
      reflexivity.
  Qed.

  Lemma repr': forall `(t : T A) B (f : A -> G B),
      traverse f t = pure (toMake' B t) <⋆>
                       (traverse (T := VEC (toLen' B t)) f (toContents' B t)).
  Proof.
    intros.
    unfold toMake', toContents'.
    Search traverse toBatch.
    rewrite traverse_through_runBatch.
    unfold compose at 1.
  Admitted.

End aksdjflasdf.

(** ** <<KStore>> to <<Batch>> *)
(******************************************************************************)
Section toBatch.

  Context (A B : Type).

  Definition toBatch: forall (C : Type), KStore A B C -> Batch A B C
    := cata A B (batch A B).

  Definition toBatch_manual: forall (C : Type), KStore A B C -> Batch A B C.
  Proof.
    intros C k.
    destruct k as [len contents make].
    generalize dependent C.
    induction len.
    - intros C make.
      pose (c := make (Vector.nil B)).
      exact (Done c).
    - intros.
      apply Vector.uncons in contents.
      destruct contents as [a rest].
      specialize (IHlen rest (B -> C)).
      apply Step.
      + apply IHlen.
        intros. apply make. constructor; assumption.
      + assumption.
  Defined.

  Definition toBatch_manual2: forall C, KStore A B C -> Batch A B C.
    intros C k.
    destruct k as [len contents make].
    generalize dependent C.
    induction contents as [| a n rest IHrest].
    - intros C make.
      exact (Done (make (Vector.nil B))).
    - intros C make.
      apply Step.
      apply IHrest.
      intros restB b.
      apply make.
      apply Vector.cons.
      assumption.
      assumption.
      assumption.
  Defined.

End toBatch.

(*
(* ISOS *)
Section isos.

  Context (A B C : Type).

  Goal forall (k : KStore A B C), k = toKStore A B C (toBatch A B C k).
  Proof.
    intros.
    unfold toBatch.
    unfold toKStore.
    compose near k.
    rewrite (cata_appmor _ _ _).
    Check (runBatch kstore B ∘ batch).
    replace (runBatch kstore B ∘ batch) with (kstore (B := B) (A := A)).
    rewrite (cata_kstore A B). reflexivity.
    Fail rewrite (runBatch_batch).
  Admitted.


  Goal forall (k : KStore A B C), k = toKStore_manual A B C (toBatch_manual A B C k).
  Proof.
    intros k.
    destruct k.
    destruct length0.
    - cbn.
      rewrite (toNil contents0).
      fequal.
      ext b. rewrite (toNil b).
      reflexivity.
    - cbn.
      unfold toKStore_manual.
      cbn.
      unfold Batch_rect.
      cbn.
      unfold nat_rect.
  Abort.


  Goal forall (k : KStore A B C), k = toKStore_manual A B C (toBatch_manual2 A B C k).
    intros.
    destruct k.
    cbn. induction contents0.
    cbn.
    + fequal. ext b. fequal.
      apply toNil.
    + cbn. cbv.
  cbv.

End isos.
<<<<<<< ours
<<<<<<< Updated upstream
=======
*)

