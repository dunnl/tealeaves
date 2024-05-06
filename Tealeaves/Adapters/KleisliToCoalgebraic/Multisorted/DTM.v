 From Tealeaves Require Export
  Classes.Multisorted.DecoratedTraversableMonad
  Functors.Multisorted.Batch.

Import Product.Notations.
Import TypeFamily.Notations.
Import Multisorted.Batch.Notations.

#[local] Generalizable Variables A B C F G W U T K.

(** * Iterating over a DTM *)
(******************************************************************************)
Section batchm_operation.

  Context
    `{Index}
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Definition batchm {A : Type} (B : Type) : forall (k : K), W * A -> @BatchM _ T W A B (T k B) :=
    fun k '(w, a) => Go (@id (T k B)) ⧆ (w, a).

  Definition toBatchM {A : Type} (B : Type) : U A -> @BatchM _ T W A B (U B) :=
    mbinddt U (@BatchM _ T W A B) (batchm B).

End batchm_operation.

(** ** Representing <<mbinddt>> with <<runBatch>> *)
(******************************************************************************)
Section toBatchM.

  Context
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Theorem mbinddt_to_runBatchM :
    forall `{Applicative F} (A B : Type) (t : U A)
      (f : forall k, W * A -> F (T k B)),
      mbinddt U F f t = runBatchM f (toBatchM U B t).
  Proof.
    intros. unfold toBatchM.
    compose near t on right.
    rewrite (dtp_mbinddt_morphism W T U BatchM F).
    fequal. ext k [w a]. cbn.
    now rewrite ap1.
  Qed.

  Corollary mbindd_to_runBatchM :
    forall (A B : Type) (t : U A)
      (f : forall k, W * A -> T k B),
      mbindd U f t = runBatchM (F := fun A => A) f (toBatchM U B t).
  Proof.
    intros. rewrite mbindd_to_mbinddt. now rewrite mbinddt_to_runBatchM.
  Qed.

  Corollary mbindt_to_runBatchM :
    forall `{Applicative F} (A B : Type) (t : U A)
      (f : forall k, A -> F (T k B)),
      mbindt U F f t = runBatchM (f ◻ allK extract) (toBatchM U B t).
  Proof.
    intros. rewrite mbindt_to_mbinddt. now rewrite mbinddt_to_runBatchM.
  Qed.

  Corollary mmapdt_to_runBatchM  :
    forall `{Applicative F} (A B : Type) (t : U A)
      `(f : K -> W * A -> F B),
      mmapdt U F f t = runBatchM (fun k => map (F := F) (mret T k) ∘ f k) (toBatchM U B t).
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    rewrite mbinddt_to_runBatchM.
    reflexivity.
  Qed.

  Corollary mbind_to_runBatchM :
    forall (A B : Type) (t : U A)
      (f : forall k, A -> T k B),
      mbind U f t = runBatchM (F := fun A => A) (f ◻ allK extract) (toBatchM U B t).
  Proof.
    intros.
    rewrite mbind_to_mbinddt.
    rewrite mbinddt_to_runBatchM.
    reflexivity.
  Qed.

  Corollary mmapd_to_runBatchM `(f : K -> W * A -> B) (t : U A) :
    mmapd U f t = runBatchM (F := fun A => A) (mret T ◻ f) (toBatchM U B t).
  Proof.
    rewrite mmapd_to_mbinddt.
    rewrite mbinddt_to_runBatchM.
    reflexivity.
  Qed.

  Corollary mmapt_to_runBatchM `{Applicative F} `(f : K -> A -> F B) (t : U A) :
    mmapt U F f t = runBatchM (fun k => map (F := F) (mret T k) ∘ f k ∘ extract (W := (W ×))) (toBatchM U B t).
  Proof.
    rewrite mmapt_to_mbinddt.
    rewrite mbinddt_to_runBatchM.
    reflexivity.
  Qed.

  Corollary mmap_to_runBatchM `(f : K -> A -> B) (t : U A) :
    mmap U f t = runBatchM (F := fun A => A) (mret T ◻ f ◻ allK extract) (toBatchM U B t).
  Proof.
    rewrite mmap_to_mbinddt.
    rewrite mbinddt_to_runBatchM.
    reflexivity.
  Qed.

  Lemma id_to_runBatchM `(t : U A) :
    t = runBatchM (F := fun A => A) (mret T ◻ allK extract) (toBatchM U A t).
  Proof.
    change t with (id t) at 1.
    rewrite <- (dtp_mbinddt_mret W T U).
    rewrite mbinddt_to_runBatchM.
    reflexivity.
  Qed.

End toBatchM.
