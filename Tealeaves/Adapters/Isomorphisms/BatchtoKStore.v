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

  Definition Batch_to_KStore {A B C}: Batch A B C -> KStore A B C.
  Proof.
    eapply (runBatch (KStore A B) kstore).
  Defined.

  Definition KStore_length: forall A B C,
      KStore A B C -> nat.
    intros. destruct X.
    assumption.
  Defined.

  Generalizable All Variables.

  Lemma yo : forall `(b : Batch A B C),
      length_Batch b = KStore.length A B C (Batch_to_KStore b).
    intros.
    induction b.
    - reflexivity.
    - cbn.
      unfold ap.
      unfold length.
      rewrite IHb.
  Abort.


  Context (A B C: Type).

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

  Definition Batch_deconstructed:
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

  Definition Batch_to_KStore2: Batch A B C -> KStore A B C.
  Proof.
    intros b.
    destruct (Batch_deconstructed b) as [len [contents mk]].
    econstructor; eassumption.
  Defined.

End batch_to.

(** ** <<KStore>> to <<Batch>> *)
(******************************************************************************)
Section toBatch.

  Context {A B C: Type}.

  Definition KStore_to_Batch: KStore A B C -> Batch A B C
    := cata A B (batch A B) C.

  (* induction on the length *)
  Definition KStore_to_Batch2: KStore A B C -> Batch A B C.
  Proof.
    intros k.
    destruct k as [len contents make].
    generalize dependent C.
    clear C.
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

  (* induction on the contents themselves *)
  Definition KStore_to_Batch3: KStore A B C -> Batch A B C.
    intros k.
    destruct k as [len contents make].
    generalize dependent C.
    clear C.
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

(* ISOS *)
Section isos.

  Context (A B C : Type).

  Lemma KStore_Batch_iso1: forall (k : KStore A B C),
      k = Batch_to_KStore (KStore_to_Batch k).
  Proof.
    intros.
    unfold KStore_to_Batch.
    unfold Batch_to_KStore.
    compose near k.
    rewrite (cata_appmor _ _ (G1 := Batch A B) (G2 := KStore A B)).
    rewrite runBatch_batch.
    rewrite cata_kstore.
    reflexivity.
    typeclasses eauto.
  Qed.


  Lemma KStore_Batch_iso2: forall (b : Batch A B C),
      b = KStore_to_Batch (Batch_to_KStore b).
  Proof.
    intros.
    unfold KStore_to_Batch.
    unfold Batch_to_KStore.
    compose near b.
    enough (ApplicativeMorphism (KStore A B) (Batch A B)
                   (cata A B (batch A B))).
    rewrite (runBatch_morphism'(G := Batch A B) (F := KStore A B)).
    Search cata kstore.
  Abort.

End isos.
