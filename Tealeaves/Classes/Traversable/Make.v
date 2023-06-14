From Tealeaves Require Export
  Classes.Listable.Functor
  Classes.Kleisli.Traversable.Functor
  Classes.Traversable.Functor
  Functors.Batch.

#[local] Generalizable Variables T G A M F.

Import Applicative.Notations.

(** ** Misc *)
(******************************************************************************)
Section properties_of_batch.

  Context (A B : Type).

  Fixpoint length_Batch (C : Type) (b : Batch A B C) : nat :=
    match b with
    | Done _ => 0
    | Step b' rest => S (length_Batch (B -> C) b')
    end.

  (* The length of a batch is the same as the length of the list we can extract from it *)
  Lemma batch_length1 : forall (C : Type) (b : Batch A B C),
      length_Batch C b =
        length (runBatch (F := const (list A)) (ret list (A := A)) b).
  Proof.
    intros C b.
    induction b as [C c | C b IHb a].
    - reflexivity.
    - cbn. rewrite IHb.
      unfold_ops @Monoid_op_list.
      rewrite List.app_length.
      cbn. lia.
  Qed.

End properties_of_batch.

(** ** varargs *)
(* varargs n A C is the type A -> A ->...(n times)...-> A -> C *)
(******************************************************************************)
Fixpoint varargs (n : nat) (A : Type) (C : Type) :=
  match n with
  | 0 => C
  | S m => A -> varargs m A C
  end.

Definition vargs_cons1 : forall A C (n : nat), varargs n A (A -> C) = (A -> varargs n A C).
Proof.
  intros. induction n.
  - reflexivity.
  - cbn. now rewrite IHn.
Defined.

Definition vargs_cons2 : forall A C (n : nat), varargs n A (A -> C) = varargs (S n) A C.
Proof.
  apply vargs_cons1.
Defined.

(** ** Make functions *)
(******************************************************************************)
Import Classes.Traversable.Functor.ToKleisli.

(* makeFnType T A t B is the type
B -> B -> B... -> T B
*)
Definition makeFnType (T : Type -> Type) `{Dist T} `{Fmap T} (A : Type) (t : T A) :=
  forall (B : Type), varargs (length (tolist T t)) B (T B).

(*
Section goal.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Definition coerce : forall A B (pf : A = B), A -> B :=
    fun A B e a => match e with
                | eq_refl => a
                end.

  Definition toMake_step : forall (A B C : Type), forall (b : Batch A B C),
      varargs (batch_length b) B C :=
    fix F A B C b :=
      match b return varargs (batch_length b) B C with
      | Done c => c
      | Step rest a => coerce
                        _ _ (vargs_cons1 B C (batch_length rest))
                        (F A B (B -> C) rest)
      end.

  Lemma toMake1 : forall (A : Type) (t : T A), makeFunction T A t.
  Proof.
    intros.
    change t with (id t).
    rewrite (id_to_runBatch T).
    unfold compose at 1.
    intros B.
  Abort.

  Lemma toMake1 : forall (A : Type) (t : T A), makeFunction T A t.
  Proof.
    intros.
    unfold makeFunction.
    intros.
    unfold_ops @Tolist_Traverse.
    unfold foldMap.
    rewrite <- (traverse_constant_applicative1 T (ret (A := A) list) B).
    rewrite (traverse_to_runBatch T).
    unfold compose at 1.
    rewrite batch_length1.
    apply toMake_step.
  Defined.

End goal.
 *)

(** ** Fixed-length lists *)
(******************************************************************************)
(* Length of a list is preserved by map *)
Lemma length_fmap_list : forall (A B : Type) (f : A -> B) (l : list A),
    length l = length (fmap list f l).
Proof.
  intros. induction l.
  - cbn. reflexivity.
  - cbn. fequal. auto.
Defined.

Section nlist.

  Definition nlist (A : Type) (n : nat) := {l : list A & length l = n}.

  Section fns.

    Context
      `{Applicative G}
        (A : Type).

    Definition sigcons : forall (l : list A) (a : A),
        {la : list A & length la = length l} ->
        {la : list A & length la = S (length l)}.
    Proof.
      intros. destruct X.
      apply (existT _ (cons a x)).
      cbn. auto.
    Defined.

    Definition sigcons2 : forall (a : A) (l : list A),
        {la : list A & length la = S (length l)}.
    Proof.
      intros. refine (existT _ (cons a l) _).
      reflexivity.
    Defined.

    Definition sigcons3 (n : nat) : A -> nlist A n -> nlist A (S n) :=
      fun a l => match l with
              | existT _ l' pf =>
                  existT _ (a :: l') (@f_equal nat nat S (length l') n pf)
              end.

    Definition discard (n : nat) : nlist A n -> list A :=
      projT1 (A := list A) (P := fun l => length l = n).

    Definition inject : forall (l : list A), nlist A (length l) :=
      fun l => existT _ l eq_refl.

    Goal forall (l : list A), discard _ (inject l) = l.
      reflexivity.
    Qed.

    #[program] Definition distr (n : nat) : nlist (G A) n -> G (nlist A n).
    intros [? ?]. rewrite <- e.
    refine ((fix F l := match l return (G (nlist A (length l))) with
                        | nil => pure G (existT (fun l => length l = 0) (@nil A) (eq_refl))
                        | cons a a' =>
                            (pure G (sigcons3 (length a')) <⋆> a <⋆> F a')
                        end) x).
    Qed.

    Definition distr3 (l : list (G A)) : G (nlist A (length l)) :=
      ((fix F l :=
          match l return (G (nlist A (length l))) with
          | nil => pure G (existT (fun l => length l = 0) (@nil A) (eq_refl))
          | cons a a' => pure G (sigcons3 (length a')) <⋆> a <⋆> F a'
          end) l).

    Definition distr2 (n : nat) : nlist (G A) n -> G (nlist A n) :=
      (fun (nl : nlist (G A) n) =>
         match nl with
         | existT _ l pf =>
             match pf in (_ = n) return G (nlist A n) with
             | eq_refl _ => distr3 l
             end
         end).

  End fns.

  Goal forall `{Applicative G} A (n : nat) (l : nlist (G A) n),
      dist list G (discard (G A) n l) = pure G (discard A n) <⋆> distr2 A n l.
  Proof.
    intros. destruct l. rename x into l. generalize dependent l.
    induction n; intros.
    - destruct l.
      + destruct e. cbn. rewrite ap2. reflexivity.
      + inversion e.
    - destruct l.
      + inversion e.
      + cbn in *. inversion e.
        specialize (IHn l H4).
        rewrite IHn. destruct e.
        destruct H4. clear IHn.
        rewrite <- fmap_to_ap.
        rewrite <- fmap_to_ap.
        rewrite <- fmap_to_ap.
        rewrite 2 fmap_ap.
        rewrite (app_pure_natural G).
        change_right (pure G (compose (discard A (S (length l))) ∘ sigcons3 A (length l)) <⋆> g <⋆> distr3 A l).
        Check ap G (fmap G cons g).
        rewrite -> fmap_to_ap.
        rewrite -> fmap_to_ap.
        rewrite <- ap4.
        rewrite <- ap4.
        repeat rewrite ap2.
        Search fmap ap.
  Abort.

End nlist.

(** ** Vectors *)
(* This is a version of vector that is just a wrapped around a
fixed-length list type *)
(******************************************************************************)
Inductive Vector (n : nat)  (A : Type) : Type :=
| MkVec : forall (l : list A), length l = n -> Vector n A.

Definition vcons (n : nat) (A : Type) (a : A) (v : Vector n A) : Vector (S n) A :=
  match v with
  | MkVec _ _ l pf_len =>
      MkVec (S n) A (a :: l)
        match pf_len with eq_refl => eq_refl end
  end.

Section Vector_dist.

  Variable
    (n : nat).

  #[export] Instance Fmap_Vector : Fmap (Vector n).
  Proof.
    refine (fun A B f Vk =>
              match Vk with
              | MkVec _ _ l len => MkVec n B (fmap list f l) _
              end).
    rewrite <- length_fmap_list. auto.
  Defined.

  Lemma list_G_to_G_Vector : forall `{Fmap G} `{Mult G} `{Pure G} (A : Type),
    forall (l : list (G A)), G (Vector (length l) A).
  Proof.
    intros. induction l.
    - cbn. apply (pure G (MkVec 0 A nil eq_refl)).
    - cbn. apply (ap G ((pure G (vcons (length l) A) <⋆> a)) IHl).
  Defined.

  #[export] Instance Pure_Vector : Pure (Vector n) :=
    fun A a => MkVec 1 A (cons a nil) eq_refl.
  Proof.
    cbv.
    intros G ? ?.

  #[export] Instance Dist_Vector : Dist (Vector n).
  Proof.
    intros G ? ? ? A V. destruct V. destruct l.
    - subst. cbn. exact (pure G (MkVec 0 A nil eq_refl)).
    - subst. cbn.
      Check (pure G (vcons (length l) A) <⋆> g).
      apply (ap G ((pure G (vcons (length l) A) <⋆> g))).
      apply (list_G_to_G_Vector A l).
  Defined.

  Instance Dist_Vector_manual : Dist (Vector n).
  Proof.
  refine (fun G map mlt pur A (v : Vector n (G A)) =>
      match v with
      | MkVec _ _ l len =>
          match l return (length l = n -> G (Vector n A)) with
          | nil => fun pf => pure G (MkVec n A nil pf)
          | cons x xs => fun pf => _
          end len
      end).
  Abort.

End Vector_dist.

(** ** Vector and vargs *)
(******************************************************************************)
Definition apply_varargs : forall (n : nat) (A C : Type),
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

Section Repr_split.

  Context
    (n : nat) (A B C : Type).

End Repr_split.

Section Repr_traversable.

  Context
    (n : nat)
      (A B C D : Type)
      (F : Type -> Type)
    `{Applicative F}.

  Definition traverse_Repr : forall (f : A -> F B), Repr n A B C -> F (Repr n A B C).
    intros.
    induction X.
    Check dist (Vector n) F (fmap (Vector n) f contents0).
    Check (pure F (apply_varargs n B C make0)).
    Check (pure F (apply_varargs n B C make0) <⋆>  dist (Vector n) F (fmap (Vector n) f contents0)).
  Abort.

(* Isomorphic representation of Batch *)
Section Batch_To_Repr.

  Context
    (T : Type -> Type)
    `{Classes.Kleisli.Traversable.Functor.TraversableFunctor T}.


  Definition Batch_to_Repr {A B C : Type} (bat : Batch A B C) :
    Repr (length_Batch A B C bat) A B C :=
    (fix F (A B C : Type) (b : Batch A B C) :=
       match b in (Batch _ _ _) return Repr (length_Batch A B C b) A B C with
       | Done c => {| contents := MkVec 0 A (@nil A) eq_refl;
                    make := c
                  |}
       | Step rest a =>
           {| contents :=
               vcons (length_Batch A B (B -> C) rest) A a
                 (contents (length_Batch A B (B -> C) rest) A B (B -> C) (F A B (B -> C) rest));
             make :=
               (@eq_rect Type (varargs (length_Batch A B (B -> C) rest) B (B -> C))
                  (fun A => A) (make (length_Batch A B (B -> C) rest)
                               A B (B -> C) (F A B (B -> C) rest))
                  _ (vargs_cons2 _ _ _))
           |}
       end) A B C bat.

End Batch_To_Repr.

(*
Section shape.

  Context
    (T : Type -> Type)
    `{Classes.Kleisli.Traversable.Functor.TraversableFunctor T}.

  Definition P A : forall C : Type, Batch A A C -> Type :=
    fun C (b : Batch A A C) => Make2 (length_Batch b) A C.

  Definition Q A : forall C : Type, Batch A A C -> Type :=
    fun C (b : Batch A A C) => Make (length_Batch b) A C.

  Definition batch_to_Make2 {A : Type} (b : Batch A A (T A)) : Make2 (length_Batch b) A (T A).
  Proof.
    apply (Batch_rect (P A)); unfold P.
    - intros B. cbn. apply id.
    - intros B b' mk a. cbn.
      rewrite technical in mk.
      cbn in mk.
      exact mk.
  Defined.

  Definition batch_to_Make {A : Type} (bat : Batch A A (T A)) : Make (length_Batch bat) A (T A).
  Proof.
    apply (Batch_rect (Q A)); unfold Q.
    - intros C c contents. apply c.
    - intros B b' mk a. cbn.
      rewrite technical2 in mk.
      auto.
  Defined.

  Print batch_to_decompose.

  Theorem length_is_length_Batch {A} : forall B (t : T A),
      length (tolist T t) = length_Batch (toBatch T B t).
  Proof.
    intros.
    unfold tolist, Tolist_Traverse, foldMap.
    rewrite (traverse_to_runBatch T).
  Admitted.

  Section section.

  Context
    {A B : Type}
    (t : T A).


  Definition statement (A B C : Type) (b : Batch A B C) := Make T (length_Batch b) C.

  Definition getMake : Make (length (tolist T t)) (T B).
  Proof.
    About Batch_rect.
    rewrite (length_is_length_Batch B).
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
*)


Section representation_theorem.

  Context
    `{TraversableFunctor T}.

  Goal forall (A B : Type) `{Applicative G} (f : A -> G B),
      traverse T G f = traverse T G f.
