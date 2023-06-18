From Tealeaves Require Export
  Classes.Listable.Functor
  Classes.Kleisli.Traversable.Functor
  Classes.Traversable.Functor
  Functors.Batch.

#[local] Generalizable Variables T G A M F.

Import Applicative.Notations.

Import Classes.Traversable.Functor.ToKleisli.


Definition coerce : forall A B (pf : A = B), A -> B :=
  fun A B e a => match e with
              | eq_refl => a
              end.

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

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Lemma length_to_Batch_length : forall (t : T A),
      length (tolist T t) = length_Batch (T B) (toBatch T B t).
  Proof.
    intros.
    unfold tolist.
    unfold Tolist_Traverse.
    rewrite (foldMap_to_traverse T B).
  Admitted.

End properties_of_batch.

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

    (* This seems un-useful
    Definition sigcons1 : forall (a : A) (l : list A),
        {la : list A & length la = length l} ->
        {la : list A & length la = S (length l)}.
    Proof.
      intros. destruct X.
      apply (existT _ (cons a x)).
      cbn. auto.
    Defined.


    Definition sigcons2 : forall (a : A) (l : list A),
        {la : list A & length la = S (length l)} :=
      fun a l => existT (fun x => length x = S (length l)) (cons a l) eq_refl.
     *)

    Definition sigcons3 (n : nat) : A -> nlist A n -> nlist A (S n) :=
      fun a l => match l with
              | existT _ (* fun x => length x = n *)
                  l' Hlen (*: length l' = n *) =>
                  existT (fun x => length x = S n) (a :: l') (@f_equal nat nat S (length l') n Hlen)
              end.

    Definition discard (n : nat) : nlist A n -> list A :=
      projT1 (A := list A) (P := fun l => length l = n).

    Definition inject : forall (l : list A), nlist A (length l) :=
      fun l => existT _ l eq_refl.

    Lemma discard_length : forall (n : nat) (l : nlist A n),
        length (discard n l) = n.
    Proof.
      intros. destruct l as [l Hlen].
      cbn. assumption.
    Qed.

    Check f_equal.

    (*
    Goal forall (n : nat) (l : nlist A n), inject (discard n l) = l.
      reflexivity.
    Qed.
    *)

    Lemma discard_inject : forall (l : list A), discard (length l) (inject l) = l.
    Proof.
      reflexivity.
    Qed.

    Definition distr_with_help (n : nat) : nlist (G A) n -> G (nlist A n).
    Proof.
      intros [l Hlen].
      rewrite <- Hlen.
      exact ((fix F l := match l return (G (nlist A (length l))) with
                        | nil => pure G (existT (fun l => length l = 0) (@nil A) (eq_refl))
                          | cons a a' =>
                              (pure G (sigcons3 (length a')) <⋆> a <⋆> F a')
                          end) l).
    Defined.

    Fixpoint distr_helper (l : list (G A)) : G (nlist A (length l)) :=
      match l return (G (nlist A (length l))) with
      | nil => pure G (existT (fun l => length l = 0) (@nil A) (eq_refl))
      | cons a a' => pure G (sigcons3 (length a')) <⋆> a <⋆> distr_helper a'
      end.

    Definition distr (n : nat) : nlist (G A) n -> G (nlist A n) :=
      (fun (nl : nlist (G A) n) =>
         match nl with
         | existT _ l pf =>
             match pf in (_ = n) return G (nlist A n) with
             | eq_refl _ => distr_helper l
             end
         end).

  End fns.

  Goal forall `{Applicative G} A (n : nat) (l : nlist (G A) n),
      dist list G (discard (G A) n l) = pure G (discard A n) <⋆> distr A n l.
  Proof.
    intros. destruct l as [l Hlen].
    generalize dependent l.
    induction n; intros l Hlen.
    - destruct l.
      + cbn.
        destruct Hlen.
        cbn.
        rewrite ap2.
        cbn.
        reflexivity.
      + exfalso.
        inversion Hlen.
    - destruct l as [|a l].
      + inversion Hlen.
      + cbn in Hlen.
        inversion Hlen as [Hlen'].
        specialize (IHn l Hlen').
        destruct Hlen.
        cbn.

        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        do 2 rewrite ap2.

        cbn in IHn.
        destruct Hlen'.
        rewrite IHn.

        rewrite <- ap4.
        rewrite <- ap4.
        repeat rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        fequal. fequal.
        fequal.
        ext a'.
        ext l'.
        unfold compose; cbn.
        unfold sigcons3.
        destruct l' as [l' Hlen'].
        cbn.
        reflexivity.
  Qed.


  (*
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
   *)

End nlist.

(** ** Uncurried make functions *)
(******************************************************************************)
Section batch_to_makeFunction.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Definition Batch_to_MakeFn : forall (A B C : Type), forall (b : Batch A B C),
      nlist B (length_Batch A B C b) -> C.
  Proof.
    induction b.
    - intro. apply a.
    - cbn in *.
      intro l.
      destruct l.
      destruct x0.
      + inversion e.
      + cbn in e. inversion e.
        apply IHb.
        * rewrite <- H3.
          exists x0. reflexivity.
        * exact b0.
  Defined.

  Definition Batch_to_Contents : forall (A B C : Type), forall (b : Batch A B C),
      nlist A (length_Batch A B C b).
  Proof.
    induction b.
    - cbn. exists (@nil A). reflexivity.
    - cbn. apply sigcons3; assumption.
  Defined.

End batch_to_makeFunction.

Module Vectors.

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

  Definition vtail (n : nat) (A : Type) (v : Vector (S n) A) : Vector n A.
  Proof.
    destruct v. destruct l.
    - exfalso. inversion e.
    - exists l. inversion e. reflexivity.
  Defined.

  Definition vhead (n : nat) (A : Type) (v : Vector (S n) A) : A.
  Proof.
    destruct v. destruct l.
    - exfalso. inversion e.
    - exact a.
  Defined.

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

  (*

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

   *)

End Vectors.

(** ** Repr type *)
(******************************************************************************)
Record Repr (n : nat) (A B C : Type) :=
  { contents : nlist A n;
    make : nlist B n -> C;
  }.

(* Isomorphic representation of Batch *)
Section Batch_To_Repr.

  Context
    (T : Type -> Type)
    `{Classes.Kleisli.Traversable.Functor.TraversableFunctor T}.


  Definition Batch_to_Repr {A B C : Type} (bat : Batch A B C) :
    Repr (length_Batch A B C bat) A B C.
    refine(
    (fix F (A B C : Type) (b : Batch A B C) :=
       match b in (Batch _ _ _) return Repr (length_Batch A B C b) A B C with
       | Done c => {| contents := _;
                    make := _;
                  |}
       | Step rest a =>
           {| contents := _;
             make := _;
           |}
       end) A B C bat).
    - cbn. exists (@nil A). reflexivity.
    - cbn. intros _. apply c.
    - cbn.
      specialize (F A B (B -> C) rest).
      destruct F.
      inversion contents0.
      exists (cons a x). cbn. now inversion H1.
    - cbn.
      specialize (F A B (B -> C) rest).
      destruct F.
      intros [Xl Xlen].
      destruct Xl.
      + inversion Xlen.
      + cbn in Xlen. inversion  Xlen.
        apply make0.
        exists Xl. assumption. assumption.
  Defined.

  Definition Repr_to_Batch {A B C : Type} (n : nat) (r : Repr n A B C) : Batch A B C.
  Proof.
    generalize dependent C.
    induction n; intros C r.
    -
      destruct r as [null c].
      Print sigT.
      specialize (c (existT _ (@nil B) eq_refl)).
      exact (pure (Batch A B) c).
    - destruct r.
      apply Step.
      + apply IHn.
        constructor.
        admit.
        admit.
      + admit.
  Admitted.

  Goal forall (A B C : Type) (b : Batch A B C), Repr_to_Batch _ (Batch_to_Repr b) = b.
  Proof.
    intros.
    induction b.
    - cbn. cbv.
    - unfold length_Batch.
      unfold Batch_to_Repr.
      unfold Repr_to_Batch.


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
