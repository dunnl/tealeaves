

(*
Module monomorphic.

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
      apply (Batch_to_makeFn (toBatch t)).
      assumption.
    Defined.

    Definition toContents: forall (t : T A),
        Vector.t A (toLen t).
    Proof.
      intro t.
      unfold toLen.
      apply (Batch_to_contents (toBatch t)).
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
                         Batch_to_makeFn b0 (Batch_to_contents b0))).
      - reflexivity.
      - intros.
        rewrite Batch_to_makeFn_rw2.
        rewrite Batch_to_contents_rw2.
        cbn.
        rewrite H5.
        reflexivity.
    Qed.

  End aksdjflasdf.

End monomorphic.
*)

Section polymorphic.

  Context
    T G
      `{Applicative G}
      `{Kleisli.TraversableFunctor.TraversableFunctor T}
      `{Map T}
      `{ToBatch T}
      `{! Compat_Map_Traverse T}
      `{! Compat_ToBatch_Traverse}.

  Lemma length_toBatch1: forall (A B: Type) (t : T A),
      length_Batch (B := B) (toBatch t) =
        length_Batch (B := B) (toBatch (map (fun _ => tt) t)).
  Proof.
    intros.
    rewrite (batch_length_mapfst (fun _ => tt)
                                 (@toBatch T _ A B t)).
    compose near t on left.
    rewrite <- (toBatch_mapfst (T := T) A unit (fun _ => tt) B).
    unfold compose.
    reflexivity.
  Qed.

  Lemma length_toBatch2: forall (A B B': Type) (t : T A),
      length_Batch (B := B) (toBatch t) =
        length_Batch (B := B') (toBatch t).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite toBatch_to_traverse.
    rewrite batch_length1.
    rewrite batch_length1.
    compose near t.
    rewrite (trf_traverse_morphism
               (G1 := Batch A B)
               (G2 := const (list A))).
    rewrite (trf_traverse_morphism
               (G1 := Batch A B')
               (G2 := const (list A))).
    rewrite runBatch_batch; try typeclasses eauto.
    rewrite runBatch_batch; try typeclasses eauto.
    rewrite <- (traverse_const1 (M := list A) (T := T) B).
    rewrite <- (traverse_const1 (M := list A) (T := T) B').
    reflexivity.
  Defined.

  Lemma toBatch_mapsnd : forall (A B B' : Type) (f : B -> B'),
      mapsnd_Batch B B' f ∘ toBatch (A := A) (A' := B') =
        map (F := Batch A B) (map f) ∘ toBatch (A := A) (A' := B).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism
               (G1 := Batch A B')
               (ϕ := fun A => mapsnd_Batch B B' f)).
    rewrite (map_traverse).
    rewrite ret_dinatural.
    reflexivity.
  Qed.

  (** ** Vector coercions *)
  (******************************************************************************)
  Definition coerce_Vector_length: forall (A: Type) (n: nat),
      Vector.t A n ->
      forall (m: nat), m = n ->
                Vector.t A m :=
    fun A n => @eq_rect_r _ n (Vector.t A).

  Lemma coerce_Vector_length_eq_refl: forall (A: Type) (n: nat)
      (v: Vector.t A n),
      coerce_Vector_length A n v n eq_refl = v.
  Proof.
    reflexivity.
  Qed.

  Lemma coerce_Vector_contents {A}:
    forall (n m: nat) (Heq: m = n)
      (v: Vector.t A n),
      Vector.to_list v =
        Vector.to_list (coerce_Vector_length A n v m Heq).
  Proof.
    intros.
    destruct Heq.
    rewrite coerce_Vector_length_eq_refl.
    reflexivity.
  Qed.

  (** ** Length *)
  (******************************************************************************)

  (* length_Batch with a fixed B *)
  Definition toLen {A}: forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := False) (toBatch t)).
  Defined.

  (* length_Batch with B given *)
  Definition toLen_poly {A} (B: Type): forall (t : T A), nat.
    intro t.
    exact (length_Batch (B := B) (toBatch t)).
  Defined.

  Lemma toLen_poly1: forall A B,
      toLen_poly (A := A) B =
        toLen_poly (A := unit) B ∘ map (fun _ => tt).
  Proof.
    intros.
    ext t.
    unfold toLen_poly.
    rewrite length_toBatch1.
    reflexivity.
  Qed.

  Lemma toLen_poly2: forall A B B', toLen_poly (A := A) B = toLen_poly B'.
  Proof.
    intros.
    ext t.
    unfold toLen_poly.
    erewrite length_toBatch2.
    reflexivity.
  Qed.

  Corollary toLen_toLen_poly: forall (A B: Type) (t: T A),
      toLen t = toLen_poly B t.
  Proof.
    intros. rewrite (toLen_poly2 A B False).
    reflexivity.
  Qed.

  Lemma toLen_foldMap: forall (A: Type) (t: T A),
      toLen t = plength t.
  Proof.
    intros.
    unfold toLen.
    rewrite length_Batch_spec.
    unfold plength.
    rewrite foldMap_through_runBatch1.
    reflexivity.
  Qed.

  (* Package *)

  (*
  Inductive package {A} (t: T A) : Type :=
    pack : forall (n: nat) (pf: plength t = n)
        (contents: Vector.t A n), package t.

  #[program] Definition toPackage {A}: forall (t : T A),
      package t.
  Proof.
    intros.
    apply (pack t (length_Batch (toBatch (A' := False) t))).
    - apply plength_eq_length.
    - apply Batch_to_contents.
  Qed.
  *)

  Inductive package {A} (t: T A) : Type :=
    pack : forall (n: nat) (pf: plength t = n)
             (contents: Vector.t A n)
             (make: forall B, Vector.t B n -> T B)
      , package t.

  #[program] Definition toMake {A}: forall (t : T A),
    forall B, Vector.t B (length_Batch (toBatch (A' := A) t)) -> T B.
  Proof.
    intros.
    rewrite (length_toBatch2 A A B) in X.
    eapply Batch_to_makeFn.
    apply X.
  Defined.

  Lemma toMake_repr {A} (t: T A):
    toMake t A (Batch_to_contents (toBatch t)) = t.
  Proof.
    intros.
    unfold toMake.
    rewrite (proof_irrelevance _ (length_toBatch2 A A A t) eq_refl).
    cbn.
    pose (Batch_repr (toBatch t)).
    rewrite e.
    compose near t on left.
    rewrite toBatch_extract_Kleisli.
    reflexivity.
  Qed.

  #[program] Definition toPackage {A}: forall (t : T A),
      package t.
  Proof.
    intros.
    pose (pack t (length_Batch (toBatch (A' := A) t))).
    specialize (p (plength_eq_length t)).
    specialize (p (Batch_to_contents (toBatch (A' := A) t))).
    specialize (p (toMake t)).
    apply p.
  Qed.

  (** ** Contents *)
  (******************************************************************************)
  Definition toContents_poly {A}: forall (B: Type) (t : T A),
      Vector.t A (toLen_poly B t).
  Proof.
    intros B t.
    apply (Batch_to_contents (toBatch t)).
  Defined.

  Definition toContents {A}: forall (t : T A),
      Vector.t A (toLen t).
  Proof.
    intro t.
    apply (Batch_to_contents (toBatch t)).
  Defined.

  Definition toContents_param {A}:
    forall (t : T A) (n : nat) (Heq: n = toLen t),
      Vector.t A n.
  Proof.
    intros.
    rewrite Heq.
    apply (Batch_to_contents (toBatch t)).
  Defined.

  Definition toContents_plength {A}: forall (B: Type) (t : T A),
      Vector.t A (plength t).
  Proof.
    intros B t.
    unfold plength.
    rewrite foldMap_through_runBatch1.
    unfold compose.
    induction (toBatch t).
    - cbn.
      apply Vector.nil.
    - cbn.
      assert (Heq: (runBatch (@const Type Type nat) (fun _ : A => 1) (False -> C) b + 1 =
                S (runBatch (@const Type Type nat) (fun _ : A => 1) (False -> C) b)             )%nat).
      lia.
      unfold monoid_op.
      unfold NaturalNumbers.Monoid_op_plus at 1.
      rewrite Heq.
      eapply Vector.cons;
      eassumption.
  Defined.

  (** ** Make *)
  (******************************************************************************)
  Definition toMake_poly {A}: forall (t : T A) (B C: Type),
      Vector.t B (toLen_poly C t) -> (T B).
  Proof.
    intros t B C.
    rewrite (toLen_poly2 A C B).
    apply (Batch_to_makeFn (toBatch t)).
  Defined.

  Definition toMake_mono {A}: forall (t : T A) (B: Type),
      Vector.t B (toLen_poly B t) -> (T B).
  Proof.
    intros t B.
    apply (Batch_to_makeFn (toBatch t)).
  Defined.

  Definition toMake_ {A}: forall (t : T A) (B: Type),
      Vector.t B (toLen t) -> (T B).
  Proof.
    intros t B.
    unfold toLen.
    pose (lemma:= toMake_poly t B False).
    unfold toLen_poly in lemma.
    assumption.
  Defined.

  Definition toMake_generic {A}:
    forall (t : T A) (B: Type) (n : nat) (Heq: n = toLen t),
      Vector.t B n -> (T B).
  Proof.
    intros t B.
    unfold toLen.
    introv Heq.
    rewrite Heq.
    pose (lemma:= toMake_poly t B False).
    unfold toLen_poly in lemma.
    assumption.
  Defined.

  Definition toMake_generic2 {A}:
    forall (t : T A) (B: Type) (n : nat) (Heq: toLen t = n),
      Vector.t B n -> (T B).
  Proof.
    intros t B n Heq v.
    apply (Batch_to_makeFn (toBatch t)).
    assert (Heq': length_Batch (toBatch (A' := B) t) = n).
    rewrite <- Heq.
    unfold toLen.
    erewrite length_toBatch2.
    reflexivity.
    apply (coerce_Vector_length B n v _ Heq').
  Defined.

  Definition toMake_generic3 {A}: forall (t : T A) (B: Type),
      Vector.t B (toLen t) -> (T B).
  Proof.
    intros t B v.
    apply (Batch_to_makeFn (toBatch t)).
    eapply coerce_Vector_length.
    eassumption.
    unfold toLen.
    erewrite length_toBatch2.
    reflexivity.
  Defined.

  Lemma toLen_map {A A'} (f: A -> A'):
    forall (t : T A),
      toLen (map f t) = toLen t.
  Proof.
    intros.
    unfold toLen.
    rewrite length_toBatch1.
    compose near t on left.
    rewrite (fun_map_map (F := T)).
    change ((fun _ : A' => tt) ∘ f) with (fun _:A => tt).
    rewrite (length_toBatch1 _ _ t).
    reflexivity.
  Qed.

  Lemma toMake_make_toMake {A A'} (f: A -> A'):
    forall (t : T A) (B: Type),
      toMake_generic3 t B =
        toMake_generic2 (map (F := T) f t) B (toLen t) (toLen_map f t).
  Proof.
    intros.
    ext v.
    unfold toMake_generic3.
    unfold toMake_generic2.
    unfold eq_ind_r, eq_ind.
  Abort.

  Lemma toLen_toMake_poly {A B C D E}:
    forall (t : T A) (v: Vector.t B (toLen_poly C t)),
      toLen_poly D (toMake_poly t B C v) = toLen_poly E (toMake_poly t B C v).
  Proof.
    intros.
    rewrite (toLen_poly2 B D E).
    reflexivity.
  Qed.

  Lemma traverse_repr {A}: forall `(t : T A) B (f : A -> G B),
      traverse f t = pure (toMake_mono t B) <⋆>
                       (traverse (T := VEC (toLen_poly B t)) f
                                 (toContents_poly B t)).
  Proof.
    intros.
    rewrite traverse_through_runBatch.
    unfold compose.
    rewrite runBatch_repr.
    reflexivity.
  Qed.

  (* put get *)
  Lemma repr1 {A}: forall `(t : T A),
      t = toMake_mono t A (toContents_poly A t).
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
                       Batch_to_makeFn b0 (Batch_to_contents b0))).
    - reflexivity.
    - introv Heq.
      intros.
      rewrite Batch_to_makeFn_rw2.
      rewrite Batch_to_contents_rw2.
      cbn.
      rewrite Heq.
      reflexivity.
  Qed.

  Lemma put_put {A} (n: nat) (t: T A) (Heq: toLen t = n)
                (B C: Type)
                (v: Vector.t B n)
                (Heq': toLen (toMake_generic2 t B n Heq v) = n):
      toMake_generic2 t C n Heq =
        toMake_generic2
          (toMake_generic2 t B n Heq v) C n Heq'.
  Proof.
    intros.
    unfold toMake_generic2.
    induction v.
  Abort.

  Lemma toLen_toMake {A B}:
    forall (t : T A) (v: Vector.t B (toLen_poly B t)),
      toLen (toMake_mono t B v) = toLen t.
  Proof.
    intros.
    unfold toLen.
    rewrite batch_length1.
    rewrite batch_length1.
    compose near t.
    rewrite <- (foldMap_through_runBatch2
                 A False (M := list A)
                 (ret (T := list))
              ).
    compose near (toMake_mono t B v).
    rewrite <- (foldMap_through_runBatch2
                 B False (M := list B)
                 (ret (T := list))
              ).
  Abort.

  Lemma toLen_toMake2 {A B}:
    forall (t : T A) (v: Vector.t B (toLen t)),
      toLen (toMake_generic2 t _ (toLen t) eq_refl v) = toLen t.
  Proof.
    intros.
    unfold toMake_generic2.

    unfold toMake_poly.
    unfold toLen.
    rewrite batch_length1.
    rewrite batch_length1.
    (*
    rewrite <- (foldMap_through_runBatch2
                 A False (M := list A)
                 (ret (T := list))
              ).
    compose near (toMake_mono t B v).
    rewrite <- (foldMap_through_runBatch2
                 B False (M := list B)
                 (ret (T := list))
              ).
     *)
  Abort.

End polymorphic.

From Tealeaves Require Import
  Misc.NaturalNumbers
  Classes.Kleisli.TraversableMonad.

Lemma length_foldMap: forall `(l: list A),
    length l = plength l.
Proof.
  intros.
  unfold plength.
  induction l.
  - reflexivity.
  - rewrite foldMap_list_eq.
    rewrite foldMap_list_cons.
    cbn. rewrite IHl.
    rewrite <- foldMap_list_eq.
    reflexivity.
Qed.

Lemma list_toLen: forall (A B: Type) (l: list A),
    length l = toLen_poly list B l.
Proof.
  intros.
  rewrite length_foldMap.
  unfold plength.
  unfold toLen_poly.
  rewrite foldMap_to_traverse1.
  rewrite traverse_through_runBatch.
  unfold compose.
  rewrite (length_toBatch2 list A B False).
  rewrite length_Batch_spec.
  reflexivity.
Qed.

Lemma toMake_helper: forall A B (l:list A) (l' : Vector.t B (toLen_poly list B l)),
    toMake_mono list l B l' = Vector.to_list l'.
Proof.
  intros.
  unfold toMake_mono.
Abort.

Lemma length_helper: forall A B (l:list A) (l' : Vector.t B (toLen list l)),
    length (toMake_ list l B l') = length l.
Proof.
  intros.
  induction l.
  - assert (Heq: l' = Vector.nil B).
    { cbn in l'. Search Vector.t 0.
      apply (Vector.toNil l'). }
    admit.
  - cbn.
    admit.
Abort.

Lemma length_helper_mono: forall A B (l:list A) (l' : Vector.t B (toLen_poly list B l)),
    length (toMake_mono list l B l') = length l.
Proof.
  intros.
Abort.

(** * Element-wise operations *)
(******************************************************************************)
Section pw.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}.

  Existing Instance Elements_Traverse.

  Definition traverse_pw
               {A B} (G : Type -> Type)
               `{Applicative G} : forall (t: T A) `(f1 : {a | a ∈ t} -> G B), G (T B).
  Proof.
    intros t f.
    apply (runBatch_pw G (toBatch (A' := B) t)).
    rewrite (element_through_runBatch2 (T := T) A B) in f.
  Admitted.

  Lemma in_Batch_iff {A} (A':Type) (t: T A):
    forall a, a ∈ t <-> a ∈ (toBatch (A':=A') t).
  Proof.
    intros.
    rewrite (element_through_runBatch2 A A').
    unfold compose.
    induction (toBatch t).
    - cbv. intuition.
    -
      cbn.
      unfold_ops @Monoid_op_subset.
      autorewrite with tea_set.
      unfold_ops @Pure_const.
      unfold_ops @Monoid_unit_subset.
      intuition.
  Qed.

  Definition traverse_fuse
               {A} (G : Type -> Type)
               `{Applicative G}
               (t: T A) (P: A -> Prop) (Hp: forall a, a ∈ t -> P a):
    T ({a : A| P a}).
  Proof.
    intros.
    setoid_rewrite (in_Batch_iff {a: A | P a}) in Hp.
    cbn in *.
    induction (toBatch t).
    - exact c.
    - apply IHb.
      + intros a' Hin_a'.
        specialize (Hp a').
        apply Hp.
        apply element_of_Step1.
          assumption.
        + specialize (Hp a ltac:(now apply element_of_Step2)).
          exists a. apply Hp.
  Defined.

#[export] Instance Compat_Elements_Traverse_List :
  @Compat_Elements_Traverse list Elements_list Traverse_list.
Proof.
  unfold Compat_Elements_Traverse.
  ext A l a.
  induction l.
  - cbn. reflexivity.
  - apply propositional_extensionality.
    autorewrite with tea_list tea_set.
    cbn.
    unfold_ops @Pure_const.
    unfold_ops @Monoid_op_subset.
    autorewrite with tea_set.
    rewrite IHl.
    firstorder.
Qed.

End pw.
