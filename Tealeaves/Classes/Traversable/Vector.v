From Tealeaves Require Export
  Classes.Listable.Functor
  Classes.Kleisli.Traversable.Functor
  Classes.Traversable.Functor
  Functors.Batch.

#[local] Generalizable Variables T G A M F.

Import Applicative.Notations.

(** ** Misc *)
(******************************************************************************)
Fixpoint batch_length {A B C : Type} (b : Batch A B C) : nat :=
  match b with
  | Done _ => 0
  | Step b' rest => S (batch_length b')
  end.

Lemma batch_length1 : forall (A B C : Type) (b : Batch A B C),
    length (runBatch (F := const (list A)) (ret list (A := A)) b) = batch_length b.
Proof.
  intros.
  induction b.
  - reflexivity.
  - cbn. rewrite <- IHb.
    unfold_ops @Monoid_op_list.
    Search length app.
    rewrite List.app_length.
    cbn. lia.
Qed.

(** ** Vectors *)
(******************************************************************************)
Inductive Vector (A : Type) : forall (n : nat), Type :=
| Vnil : Vector A 0
| Vcons : A -> forall (n : nat), Vector A n -> Vector A (S n).

Section traversable.

  Context
    (G : Type -> Type)
    `{Applicative G}
    (A B : Type).

  Fixpoint dist_Vector (n : nat) : Vector (G A) n -> G (Vector A n).
    refine(match n return Vector (G A) n -> G (Vector A n) with
    | 0 => _
           | (S m) => fun v =>
                       match v return G (Vector A (S m)) with
                       | Vnil _ => _
                       | Vcons _ a m rest => _
                       end
           end).
    - intros. exact (pure G (Vnil A)).
    - destruct v as [|g p rest]. admit. admit.
    - admit.
  Admitted.

End traversable.

(** ** Vector and vargs *)
(******************************************************************************)

Fixpoint varargs (n : nat) (A : Type) (C : Type) :=
  Vector A n -> C.

Definition toMake : forall (A B C : Type), forall (b : Batch A B C),
    Vector B (batch_length b) -> C.
Proof.
  intros. induction b.
  - assumption.
  - cbn in X.
    inversion X.
    subst.
    apply IHb; assumption.
Defined.

Goal forall (A B C : Type), forall (b : Batch A B (B -> C)) (a : A),
    toMake A B C (Step b a) =
      toMake A B C (Step b a).
Proof.
  intros.
  unfold toMake. cbn.
Abort.

Definition toVector : forall (A B C : Type), forall (b : Batch A B C), Vector A (batch_length b).
Proof.
  intros. induction b.
  - constructor.
  - cbn. constructor.
    assumption. assumption.
Defined.

Goal forall (A B C : Type) (b : Batch A A C),
    extract_Batch b = toMake A A C b (toVector A A C b).
Proof.
  intros. induction b.
  - reflexivity.
  - cbn

