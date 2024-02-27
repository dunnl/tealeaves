From Tealeaves Require Export
  Functors.Batch
  Functors.KStore.

(** * Batch to KStore *)
(******************************************************************************)
Section batch_to.

  Context (A B C : Type).

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
  Qed.

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

End batch_to.

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
