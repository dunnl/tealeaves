From Tealeaves Require Export
  Classes.Listable.Functor
  Classes.Kleisli.Traversable.Functor
  Classes.Traversable.Functor
  Functors.Batch.

#[local] Generalizable Variables T G A M.

(** ** Misc *)
(******************************************************************************)
Fixpoint batch_length {A B C : Type} (b : Batch A B C) : nat :=
  match b with
  | Done _ => 0
  | Step b' rest => S (batch_length b')
  end.

(** ** varargs and Vector *)
(******************************************************************************)
Fixpoint varargs (n : nat) (A : Type) (C : Type) :=
  match n with
  | 0 => C
  | S m => A -> varargs m A C
  end.

Inductive Vector (n : nat)  (A : Type) : Type :=
| MkVec : forall (l : list A), length l = n -> Vector n A.

Definition vcons (n : nat) (A : Type) (a : A) (v : Vector n A) : Vector (S n) A :=
  match v with
  | MkVec _ _ l len =>
      MkVec (S n) A (a :: l) (match len with
                             | eq_refl => eq_refl
                             end)
  end.

Definition vargs_cons1 : forall A C (n : nat), varargs n A (A -> C) = (A -> varargs n A C).
Proof.
  intros. induction n.
  - reflexivity.
  - cbn. now rewrite IHn.
Defined.

Definition vargs_cons2 : forall A C (n : nat), varargs n A (A -> C) = varargs (S n) A C.
Proof.
  intros. induction n.
  - reflexivity.
  - cbn. now rewrite IHn.
Defined.

Definition apply_make : forall (n : nat) (A C : Type),
    varargs n A C -> Vector n A -> C.
Proof.
  intros. induction n.
  - apply X.
  - cbn in *.
    destruct X0.
    destruct l.
    * cbn in e. inversion e.
    * specialize (IHn (X a)).
      inversion e.
      apply IHn. econstructor.
      exact H0.
Defined.

(** ** Repr type *)
(******************************************************************************)
Record Repr (n : nat) (A B C : Type) :=
  { contents : Vector n A;
    make : varargs n B C
  }.

Section Repr_traversable.

  Context
    (n : nat)
      (A B C D : Type)
      (F : Type -> Type)
    `{Applicative F}.

  Definition traverse_Repr : forall (f : A -> F B), Repr n A B C -> F (Repr n A B C).
    intros.
    induction X.
    -

Section Batch_To_Repr.

  Context
    (T : Type -> Type)
    `{Classes.Kleisli.Traversable.Functor.TraversableFunctor T}.

  (*
  Definition P A B : forall C : Type, Batch A B C -> Type :=
    fun (C : Type) (b : Batch A B C) => Repr (batch_length b) A B C.

  Definition batch_to_Repr {A B : Type} (bat : Batch A B (T A)) : Repr (batch_length bat) A B (T A).
  Proof.
    apply (Batch_rect (P A B)); unfold P.
    - intros C c. constructor.
      + cbn. apply (MkVec 0 A nil eq_refl).
      + cbn. exact c.
    - intros C bat' repr a. cbn.
      destruct repr. inversion contents0.
      constructor.
      + refine (MkVec (S (batch_length bat')) A (a :: l) _).
        now rewrite <- H1.
      + cbn. rewrite vargs_cons1 in make0. assumption.
  Defined.
   *)

  Definition Batch_to_Repr {A B C : Type} (bat : Batch A B C) : Repr (batch_length bat) A B C :=
    (fix F (A B C : Type) (b : Batch A B C) :=
      match b in (Batch _ _ _) return Repr (batch_length b) A B C with
            | Done c => {| contents := MkVec 0 A (@nil A) eq_refl;
                          make := c
                       |}
      | Step rest a =>
          {| contents := vcons (batch_length rest) A a
                           (contents (batch_length rest) A B (B -> C) (F A B (B -> C) rest));
            make := (@eq_rect Type (varargs (batch_length rest) B (B -> C))
                       (fun A => A) (make (batch_length rest) A B (B -> C) (F A B (B -> C) rest))
                       _ (vargs_cons2 _ _ _))
          |}
      end) A B C bat.

End Batch_To_Repr.

(*
Definition Make (n : nat) (A : Type) (C : Type) := Package n A -> C.


Lemma Make_to_Make2 : forall A T n, Make n A (T A) -> Make2 n A (T A).
Proof.
  intros.
  induction n.
  - cbn in *. apply X. apply (MkPackage 0 A nil). reflexivity.
  - admit.
Abort.

Inductive Decomposition (T : Type -> Type) (A : Type) :=
| MkDec : forall n : nat, Package n A -> Make n A (T A) -> Decomposition T A.

Lemma technical : forall (A B : Type) (n : nat), Make2 n A (A -> B) = Make2 (S n) A B.
Proof.
  intros. cbn. induction n.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Lemma technical2 : forall (A B : Type) (n : nat), Make n A (A -> B) = Make (S n) A B.
Proof.
  intros. unfold Make. induction n.
  - admit.
  - admit.
Admitted.
*)
Section shape.

  Context
    (T : Type -> Type)
    `{Classes.Kleisli.Traversable.Functor.TraversableFunctor T}.

  Definition P A : forall C : Type, Batch A A C -> Type :=
    fun C (b : Batch A A C) => Make2 (batch_length b) A C.

  Definition Q A : forall C : Type, Batch A A C -> Type :=
    fun C (b : Batch A A C) => Make (batch_length b) A C.

  Definition batch_to_Make2 {A : Type} (b : Batch A A (T A)) : Make2 (batch_length b) A (T A).
  Proof.
    apply (Batch_rect (P A)); unfold P.
    - intros B. cbn. apply id.
    - intros B b' mk a. cbn.
      rewrite technical in mk.
      cbn in mk.
      exact mk.
  Defined.

  Definition batch_to_Make {A : Type} (bat : Batch A A (T A)) : Make (batch_length bat) A (T A).
  Proof.
    apply (Batch_rect (Q A)); unfold Q.
    - intros C c contents. apply c.
    - intros B b' mk a. cbn.
      rewrite technical2 in mk.
      auto.
  Defined.

  Print batch_to_decompose.

  Theorem length_is_batch_length {A} : forall B (t : T A),
      length (tolist T t) = batch_length (toBatch T B t).
  Proof.
    intros.
    unfold tolist, Tolist_Traverse, foldMap.
    rewrite (traverse_to_runBatch T).
  Admitted.

  Section section.

  Context
    {A B : Type}
    (t : T A).


  Definition statement (A B C : Type) (b : Batch A B C) := Make T (batch_length b) C.

  Definition getMake : Make (length (tolist T t)) (T B).
  Proof.
    About Batch_rect.
    rewrite (length_is_batch_length B).
    Check iterate T B t.
    change (statement A B (T B) (iterate T B t)).
    induction (iterate T B t).
    - unfold statement in *. cbn.
    apply T0.
    Check (Batch_rect (statement A B)).
    apply (@statement A (iterate T False t).
    unfold tolist, Tolist_Traverse, foldMap in new_contents.
    rewrite (traverse_to_runBatch T) in new_contents.
    unfold compose in new_contents.
    Check (iterate T False t).
    Check Batch_rect.
    induction (Container.iterate T False t).
    - admit.
    - apply IHb.
  Abort.


  Definition getMake : Make B (length (tolist T t)).
    Search False "ap".
    Search False "ap".
    intros new_contents.
    apply (runBatch (F := fun A => A) (@id B)).
    Check Container.iterate T nat t.
    unfold tolist, Tolist_Traverse, foldMap in new_contents.

    rewrite (traverse_to_runBatch T) in new_contents.
    Check Container.iterate T False t.
    unfold compose in new_contents.
    induction (Container.iterate T False t).
    - cbn in *. constructor. admit.
    - admit.
  Admitted.

  End operations.
  End section.

  Theorem rebuild : forall (A : Type) (t : T A), getMake (A := A) t (getPackage t) = t.
  Proof.
    intros.
  Admitted.

  Context
    (A B : Type)
    `{Applicative F}.

  Definition traverse_package (f : A -> F B) : forall n, Package n A -> F (Package n B).
  Proof.
    introv p. destruct p.
    pose (l' := traverse list F f l). destruct l.
    - cbn in *. subst. refine (pure F (MkPackage 0 B [] eq_refl)).
    - admit.
  Admitted.

  Theorem traverse_rebuild : forall (t : T A) (f : A -> F B),
      traverse T F f t = fmap F (getMake t) (traverse_package f (length (tolist T t)) (getPackage t)).
    intros.
  Admitted.


End shape.
