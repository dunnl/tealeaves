From Tealeaves Require Export
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Coalgebraic.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor.

From Tealeaves Require Export
  Classes.Categorical.ShapelyFunctor
  Theory.Batch
  Functors.List.

Import Subset.Notations.
Import Applicative.Notations.
Import ContainerFunctor.Notations.
Import ProductFunctor.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import Batch.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables F T G A B C M ϕ.

(** * Applicative instances for subset *) (* TODO Move me ! *)
(******************************************************************************)
Section subset_applicative_instance.

  #[export] Instance Pure_subset: Pure subset := @eq.

  #[export] Instance Mult_subset: Mult subset :=
    fun A B '(sa, sb) '(a, b) => sa a /\ sb b.

  #[export] Instance Applicative_subset: Applicative subset.
  Admitted.

  Lemma subset_ap_spec:
    forall (A B: Type) (sf: subset (A -> B)) (sa: subset A) (b: B),
      (sf <⋆> sa) b = exists (f: A -> B) (a: A), sa a /\ sf f /\ f a = b.
  Proof.
    intros.
    unfold ap.
    unfold_ops @Map_subset.
    unfold_ops @Mult_subset.
    propext.
    - intros [[f a] [[hyp1 hyp2] hyp3]].
      exists f a. auto.
    - intros [f [a [hyp1 [hyp2 hyp3]]]].
      subst. exists (f, a). tauto.
  Qed.

End subset_applicative_instance.

(** ** Traverse by subset *)
(******************************************************************************)
Lemma traverse_commutative_idem:
  forall `{TraversableFunctor T'}
    `{ToBatch T'}
    `{! Compat_ToBatch_Traverse T'}

    (A B: Type) (f: A -> subset B),
    forwards ∘ traverse (T := T') (G := Backwards subset) (mkBackwards ∘ f) =
      traverse (T := T') f.
Proof.
  intros. ext t. unfold compose.
  do 2 rewrite traverse_through_runBatch.
  unfold compose.
  induction (toBatch t).
  - reflexivity.
  - cbn. rewrite IHb.
    unfold ap.
    ext c.
    unfold_ops @Mult_subset.
    unfold_ops @Map_subset.
    propext.
    { intros [[mk b'] [[[b'' c'] [rest1 rest2]] Heq]].
      cbn in rest2.
      inversion rest2. subst.
      exists (mk, b'). tauto. }
    { intros [[mk b'] [rest1 rest2]].
      subst. exists (mk, b'). split; auto.
      exists (b', mk). tauto. }
Qed.

(** * Theory About Batch *)
Section Batch_theory.

  Lemma Batch_make_precompose1:
    forall {A B C' C D: Type} (b: Batch A B (C -> D)) (f: C' -> C)
      (v: Vector (length_Batch b) B)
      (v': Vector (length_Batch (map (precompose f) b)) B)
      (Hsim: v ~~ v')
      (c: C'),
      Batch_make (map (precompose f) b) v' c =
        Batch_make b v (f c).
  Proof.
    intros.
    rewrite (Batch_make_compose_rw2 b (precompose f) v').
    unfold precompose.
    fequal.
    apply Vector_sim_eq.
    apply Vector_coerce_sim_l'.
    symmetry.
    assumption.
  Qed.

  Lemma Batch_make_precompose2:
    forall {A B C' C D: Type} (b: Batch A B (C -> D)) (f: C' -> C)
      (v: Vector (length_Batch (map (precompose f) b)) B)
      (c: C'),
      Batch_make (map (precompose f) b) v c =
        Batch_make b (coerce eq_sym (batch_length_map (precompose f) b) in v) (f c).
  Proof.
    intros.
    apply Batch_make_precompose1.
    apply Vector_coerce_sim_l.
  Qed.

  Ltac hide_lhs :=
    match goal with
    | |- ?lhs = ?rhs =>
        let name := fresh "lhs" in
        remember lhs as name
    end.

  Lemma Batch_make_natural1:
    forall {A B B' C: Type} (b: Batch A B' C) (f: B -> B')
      (v: Vector (length_Batch b) B)
      (v': Vector (length_Batch (mapsnd_Batch B B' f b)) B),
      v ~~ v' ->
      Batch_make b (map f v) =
        Batch_make (mapsnd_Batch _ _ f b) v'.
  Proof.
    introv Hsim.
    induction b.
    - cbn in v, v'.
      rewrite (Vector_nil_eq v).
      rewrite (Vector_nil_eq v').
      reflexivity.
    - cbn in v, v'.
      (* LHS *)
      rewrite Batch_make_rw2.
      rewrite (Vector_surjective_pairing2 (v := v)).
      rewrite (map_Vector_vcons f (length_Batch b) _ (Vector_hd v)).
      rewrite Vector_tl_vcons.
      rewrite Vector_hd_vcons.
      (* RHS *)
      try rewrite (mapsnd_Batch_rw2 (B := B) f a b).
      (* ^^^ fails for some reason *)
      cbn.
      rewrite (Batch_make_precompose2 (mapsnd_Batch B B' f b) _).
      assert (cut: f (Vector_hd v) = f (Vector_hd v')).
      { inversion Hsim.
        fequal.
        apply (Vector_hd_sim Hsim). }
      rewrite cut.
      specialize (IHb (Vector_tl v)).
      specialize (IHb
                    (coerce eq_sym (batch_length_map (precompose f)
                                      (mapsnd_Batch B B' f b))
                      in Vector_tl v')).
      rewrite IHb.
      + reflexivity.
      + apply Vector_coerce_sim_r'.
        apply Vector_tl_sim.
        assumption.
  Qed.

  Lemma map_coerce_Vector:
    forall (n m: nat) (Heq: n = m)
      (A B: Type) (f: A -> B) (v: Vector n A),
      coerce Heq in (map f v) = map f (coerce Heq in v).
  Proof.
    intros.
    apply Vector_sim_eq.
    apply (transitive_Vector_sim (v2 := map f v)).
    - apply symmetric_Vector_sim.
      apply Vector_coerce_sim_r.
    - apply map_coerce_Vector.
  Qed.

  Lemma Batch_make_natural2:
    forall {A B B' C: Type} (b: Batch A B' C) (f: B -> B')
      (v: Vector (length_Batch (mapsnd_Batch B B' f b)) B),
      Batch_make (mapsnd_Batch _ _ f b) v =
        Batch_make b (coerce (eq_sym (batch_length_mapsnd f b)) in (map f v)).
  Proof.
    intros.
    symmetry.
    rewrite map_coerce_Vector.
    apply (Batch_make_natural1 b f _ v).
    apply Vector_coerce_sim_l.
  Qed.

End Batch_theory.

(** * Theory Concerning Vectors *)
(******************************************************************************)

#[export] Instance Compat_Map_Traverse_Vector {n: nat}:
  Compat_Map_Traverse (Vector n).
Proof.
  hnf. ext A B f.
  unfold_ops @Map_Traverse.
  ext v. induction v using Vector_induction.
  - rewrite map_Vector_vnil.
    rewrite traverse_Vector_vnil.
    reflexivity.
  - rewrite map_Vector_vcons.
    rewrite traverse_Vector_vcons.
    rewrite IHv.
    reflexivity.
Qed.

(** * <<tosubset>> on Vectors *)
(******************************************************************************)

#[export] Instance ToSubset_Vector {n}: ToSubset (Vector n).
Proof.
  unfold Vector.
  intro A.
  intros [contents Pflen].
  intro a.
  exact (a ∈ contents).
Defined.

Lemma tosubset_Vector_vnil: forall (A: Type),
    tosubset (@vnil A) = ∅.
Proof.
  tauto.
Qed.

Lemma tosubset_Vector_vcons: forall (n: nat) (A: Type) (a: A) (v: Vector n A),
    tosubset (vcons n a v) = {{a}} ∪ tosubset v.
Proof.
  intros.
  destruct v.
  cbn. tauto.
Qed.

#[export] Instance Compat_ToSubset_Traverse_Vector {n: nat}:
  Compat_ToSubset_Traverse (Vector n).
Proof.
  hnf. ext A v.
  unfold_ops @ToSubset_Traverse.
  induction v using Vector_induction.
  - reflexivity.
  - rewrite foldMap_Vector_vcons;
      try typeclasses eauto.
    rewrite tosubset_Vector_vcons.
    rewrite IHv.
    reflexivity.
Qed.

(** * Zipping vectors *)
(******************************************************************************)
Definition Vector_zip_eq:
  forall (A B: Type) (n: nat)
    (v1: Vector n A)
    (v2: Vector n B),
    Vector n (A * B).
Proof.
  introv v1 v2.
  induction n.
  - exact vnil.
  - apply vcons.
    exact (Vector_hd v1, Vector_hd v2).
    apply IHn.
    exact (Vector_tl v1).
    exact (Vector_tl v2).
Defined.

Lemma Vector_zip_eq_vcons:
  forall (A B: Type) (n: nat)
    (v1: Vector n A)
    (v2: Vector n B)
    (a: A) (b: B),
    Vector_zip_eq A B (S n)
      (vcons n a v1) (vcons n b v2) =
      vcons n (a, b) (Vector_zip_eq A B n v1 v2).
Proof.
  intros.
  rewrite (Vector_surjective_pairing2).
  rewrite (Vector_surjective_pairing2).
  rewrite Vector_hd_vcons.
  rewrite Vector_tl_vcons.
  cbn.
  rewrite Vector_hd_vcons.
  rewrite Vector_hd_vcons.
  rewrite Vector_hd_vcons.
  rewrite Vector_tl_vcons.
  rewrite Vector_tl_vcons.
  rewrite Vector_tl_vcons.
  reflexivity.
Qed.

Lemma Vector_zip_eq_fst:
  forall (A B: Type) (n: nat)
    (v1: Vector n A)
    (v2: Vector n B),
    map fst (Vector_zip_eq A B n v1 v2) = v1.
Proof.
  intros.
  induction n.
  - rewrite (Vector_nil_eq v1).
    rewrite (Vector_nil_eq v2).
    apply Vector_sim_eq.
    reflexivity.
  - rewrite (Vector_surjective_pairing2 (v := v1)).
    rewrite (Vector_surjective_pairing2 (v := v2)).
    rewrite Vector_zip_eq_vcons.
    rewrite map_Vector_vcons.
    cbn.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Vector_zip_eq_snd:
  forall (A B: Type) (n: nat)
    (v1: Vector n A)
    (v2: Vector n B),
    map snd (Vector_zip_eq A B n v1 v2) = v2.
Proof.
  intros.
  induction n.
  - rewrite (Vector_nil_eq v1).
    rewrite (Vector_nil_eq v2).
    apply Vector_sim_eq.
    reflexivity.
  - rewrite (Vector_surjective_pairing2 (v := v1)).
    rewrite (Vector_surjective_pairing2 (v := v2)).
    rewrite Vector_zip_eq_vcons.
    rewrite map_Vector_vcons.
    cbn.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Vector_zip_eq_sim:
  forall (A B: Type) (n: nat)
    (v1: Vector n A)
    (v2: Vector n B)
    (v3: Vector n B),
    v2 ~~ v3 ->
    Vector_zip_eq A B n v1 v2 =
      Vector_zip_eq A B n v1 v3.
Proof.
  introv Hsim.
  induction n.
  - reflexivity.
  - rewrite (Vector_surjective_pairing2 (v := v1)).
    rewrite (Vector_surjective_pairing2 (v := v2)).
    rewrite Vector_zip_eq_vcons.
    rewrite (Vector_surjective_pairing2 (v := v3)).
    rewrite Vector_zip_eq_vcons.
    rewrite (Vector_hd_sim Hsim).
    assert (Vector_tl v2 ~~ Vector_tl v3)
      by now apply Vector_tl_sim.
    fequal. auto.
Qed.

(** ** Generalized zip operation *)
(******************************************************************************)
Definition Vector_zip
  (A B: Type) (n m: nat)
  (v1: Vector n A)
  (v2: Vector m B)
  (Heq: n = m): Vector n (A * B) :=
  Vector_zip_eq A B n v1 (coerce (eq_sym Heq) in v2).

(* This verison is less convenient than the above one in some
 respects because it cannot reduce unless the proof of equality is
 eq_refl. *)
Definition Vector_zip_alt
  (A B: Type) (n m: nat)
  (v1: Vector n A)
  (v2: Vector m B)
  (Heq: n = m): Vector n (A * B) :=
    (match Heq in (_ = m) return Vector m B -> Vector n (A * B) with
     | eq_refl => Vector_zip_eq A B n v1
     end) v2.

Lemma Vector_zip_eq_spec:
  forall (A B: Type) (n: nat)
    (v1: Vector n A)
    (v2: Vector n B),
    Vector_zip_eq A B n v1 v2 =
      Vector_zip A B n n v1 v2 eq_refl.
Proof.
  intros.
  unfold Vector_zip.
  change (@eq_sym nat n n (@eq_refl nat n))
    with (@eq_refl nat n).
  rewrite coerce_Vector_eq_refl.
  reflexivity.
Qed.

(* This lemma is not (apparently?) provable for Vector_zip_alt.
It is only provable here because the applied lemmas already depend on proof irrelevance internally *)
Lemma Vector_zip_proof_irrelevance:
  forall (A B: Type) (n m: nat)
    (v1: Vector n A)
    (v2: Vector m B)
    (Heq1: n = m)
    (Heq2: n = m),
    Vector_zip A B n m v1 v2 Heq1 =
      Vector_zip A B n m v1 v2 Heq2.
Proof.
  intros.
  unfold Vector_zip.
  apply Vector_zip_eq_sim.
  apply (transitive_Vector_sim (v2 := v2)).
  apply Vector_coerce_sim_l.
  apply Vector_coerce_sim_r.
Qed.

Lemma Vector_zip_proof_irrelevance2:
  forall (A B: Type) (n: nat)
    (v1: Vector n A)
    (v2: Vector n B)
    (Heq: n = n),
    Vector_zip A B n n v1 v2 Heq =
      Vector_zip_eq A B n v1 v2.
Proof.
  intros.
  unfold Vector_zip.
  apply Vector_zip_eq_sim.
  apply Vector_coerce_sim_l.
Qed.

Lemma Vector_zip_fst:
  forall (A B: Type) (n m: nat)
    (v1: Vector n A)
    (v2: Vector m B)
    (Heq: n = m),
    map fst (Vector_zip A B n m v1 v2 Heq) = v1.
Proof.
  intros.
  subst.
  apply Vector_zip_eq_fst.
Qed.

Lemma Vector_zip_snd:
  forall (A B: Type) (n m: nat)
    (v1: Vector n A)
    (v2: Vector m B)
    (Heq: n = m),
    map snd (Vector_zip A B n m v1 v2 Heq) ~~ v2.
Proof.
  intros.
  subst.
  rewrite <- Vector_zip_eq_spec.
  rewrite Vector_zip_eq_snd.
  reflexivity.
Qed.

Lemma Vector_zip_vcons1:
  forall (A B: Type) (n m: nat)
    (v1: Vector n A)
    (v2: Vector m B)
    (Heq: n = m)
    (a: A) (b: B),
    Vector_zip A B (S n) (S m)
      (vcons n a v1) (vcons m b v2) (f_equal S Heq) =
      vcons n (a, b) (Vector_zip A B n m v1 v2 Heq).
Proof.
  intros. destruct Heq.
  rewrite <- Vector_zip_eq_spec.
  rewrite Vector_zip_proof_irrelevance2.
  rewrite Vector_zip_eq_vcons.
  reflexivity.
Qed.

Lemma Vector_zip_vcons2:
  forall (A B: Type) (n m: nat)
    (v1: Vector n A)
    (v2: Vector m B)
    (Heq: S n = S m)
    (a: A) (b: B),
    Vector_zip A B (S n) (S m)
      (vcons n a v1) (vcons m b v2) Heq =
      vcons n (a, b) (Vector_zip A B n m v1 v2 (S_uncons Heq)).
Proof.
  intros.
  inversion Heq.
  subst.
  rewrite Vector_zip_proof_irrelevance2.
  rewrite Vector_zip_proof_irrelevance2.
  apply Vector_zip_eq_vcons.
Qed.

(** ** Relating vectors *)
(******************************************************************************)
Lemma vcons_eq_inv: forall (n: nat) (A: Type) (a1 a2: A) (v1 v2: Vector n A),
    vcons n a1 v1 = vcons n a2 v2 ->
    a1 = a2 /\ v1 = v2.
Proof.
  intros.
  assert (proj1_sig (vcons n a1 v1) = proj1_sig (vcons n a2 v2)).
  { now rewrite H. }
  rewrite proj_vcons in *.
  rewrite proj_vcons in *.
  inversion H0. split. auto.
  apply Vector_sim_eq; auto.
Qed.

Lemma Forall_zip_spec:
  forall (A B: Type) (n: nat) (R: A -> B -> Prop)
    (v1: Vector n A) (v2: Vector n B),
    traverse (G := subset) (T := Vector n) R v1 v2 =
      foldMap (M := Prop)
        (op := Monoid_op_and) (unit := Monoid_unit_true)
        (uncurry R) (Vector_zip_eq A B n v1 v2).
Proof.
  intros.
  induction n.
  - rewrite (Vector_nil_eq v1).
    rewrite (Vector_nil_eq v2).
    cbn. propext; easy.
  - rewrite (Vector_surjective_pairing2 (v := v1)).
    rewrite (Vector_surjective_pairing2 (v := v2)).
    rewrite Vector_zip_eq_vcons.
    rewrite traverse_Vector_vcons.
    rewrite foldMap_Vector_vcons.
    2: typeclasses eauto.
    rewrite subset_ap_spec.
    propext.
    + intros [f_vcons [a_hdv2 [hyp1 [hyp2 hyp3]]]].
      rewrite <- map_to_ap in hyp2.
      unfold map, Map_subset in hyp2.
      destruct hyp2 as [b [hyp21 hyp22]].
      subst.
      apply vcons_eq_inv in hyp3.
      destruct hyp3; subst.
      rewrite <- IHn.
      split; auto.
    + intros [hyp1 hyp2].
      rewrite <- IHn in hyp2.
      exists (vcons n (Vector_hd v2)).
      exists (Vector_tl v2). split; auto.
      split; auto. rewrite <- map_to_ap.
      unfold_ops @Map_subset.
      exists (Vector_hd v2). auto.
Qed.

(** * Miscellaneous Properties Concerning <<toBatch>>*)
(******************************************************************************)
Section stuff.

  Context
    `{TraversableFunctor T}
      `{Map T}
      `{ToBatch T}
      `{! Compat_Map_Traverse T}
      `{! Compat_ToBatch_Traverse T}.

  (** ** Relating <<tolist>> and <<Batch_contents ∘ toBatch>> *)
  (******************************************************************************)
  Lemma Batch_contents_tolist:
    forall {A B} (t: T A),
      Vector_to_list A (Batch_contents (toBatch (A' := B) t)) =
        List.rev (tolist t).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite (foldMap_through_runBatch2 A B).
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn.
      rewrite Vector_to_list_vcons.
      rewrite IHb.
      unfold_ops @Monoid_op_list @Return_list.
      rewrite List.rev_unit.
      reflexivity.
  Qed.

  (** ** <<Batch_contents ∘ toBatch>> is Independent of <<B>> *)
  (******************************************************************************)
  Lemma Batch_contents_toBatch_sim:
    forall {A B B'} (t: T A),
      Batch_contents
        (toBatch (A' := B) t) ~~
        Batch_contents (toBatch (A' := B') t).
  Proof.
    intros.
    unfold Vector_sim.
    change (proj1_sig ?v) with (Vector_to_list _ v).
    rewrite Batch_contents_tolist.
    rewrite Batch_contents_tolist.
    reflexivity.
  Qed.

  (** ** <<shape>> commutes with <<toBatch>> *)
  (******************************************************************************)
  Lemma shape_toBatch_spec: forall (A B: Type) (t: T A),
      shape (toBatch (A' := B) t) =
        toBatch (A' := B) (shape t).
  Proof.
    intros.
    compose near t on right.
    unfold shape at 2.
    rewrite toBatch_mapfst.
    reflexivity.
  Qed.

  (** ** Similar <<shape>>d terms have similar <<toBatch>> <<shape>>s*)
  (******************************************************************************)
  Lemma toBatch_shape:
    forall {A' B} `(t1: T A) (t2: T A'),
      shape t1 = shape t2 ->
      shape (F := BATCH1 B (T B))
        (toBatch (A' := B) t1) =
        shape (F := BATCH1 B (T B))
          (toBatch (A' := B) t2).
  Proof.
    introv Hshape.
    do 2 rewrite shape_toBatch_spec.
    rewrite Hshape.
    reflexivity.
  Qed.

  (** ** Similar <<shape>>d <<toBatch>> implies similar <<shape>>s*)
  (******************************************************************************)
  Lemma toBatch_shape_inv:
    forall {A' B} `(t1: T A) (t2: T A'),
      shape (F := BATCH1 B (T B))
        (toBatch (A' := B) t1) =
        shape (F := BATCH1 B (T B))
          (toBatch (A' := B) t2) ->
      shape t1 = shape t2.
  Proof.
    introv Hshape.
    unfold shape.
    do 2 rewrite map_through_runBatch.
    do 2 rewrite shape_toBatch_spec in Hshape.
    unfold shape in Hshape.
    do 2 rewrite map_through_runBatch in Hshape.
    unfold compose in Hshape.
    unfold compose.
    destruct (@toBatch T _ A unit t1).
  Abort.

End stuff.

(** * Batch_to_list *)
(******************************************************************************)
Section Batch.

  Definition Batch_to_list: forall `(b: Batch A B C), list A.
  Proof.
    intros. apply (tolist (F := BATCH1 B C) b).
  Defined.

  Lemma Batch_contents_list: forall `(b: Batch A B C),
      proj1_sig (Batch_contents b) = List.rev (Batch_to_list b).
  Proof.
    intros.
    induction b.
    - reflexivity.
    - cbn.
      rewrite proj_vcons.
      rewrite IHb.
      rewrite <- List.rev_unit.
      reflexivity.
  Qed.

  Lemma Batch_to_list_rw2 {A B C}: forall (b: Batch A B (B -> C)) (a: A),
      Batch_to_list (b ⧆ a) = Batch_to_list b ++ (a::nil).
  Proof.
    intros.
    cbn.
    reflexivity.
  Qed.

End Batch.

(** * Proof that traversable functors are shapely over lists *)
(******************************************************************************)
Section shapeliness.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse T}.

  Lemma shapeliness_tactical: forall (A: Type) (b1 b2: Batch A A (T A)),
      runBatch (const (list A)) (ret (T := list)) _ b1 =
        runBatch (const (list A)) (ret (T := list) (A := A)) _ b2 ->
      mapfst_Batch A unit (const tt) b1 = mapfst_Batch A unit (const tt) b2 ->
      runBatch (fun A => A) id (T A) b1 = runBatch (fun A => A) id (T A) b2.
  Proof.
    introv Hlist Hshape.
    induction b1 as [C c1 | C rest1 IHrest1 a1];
      destruct b2 as [c2 | rest2 a2]; cbn in *.
    - inversion Hshape. reflexivity.
    - inversion Hshape.
    - inversion Hshape.
    - unfold monoid_op, Monoid_op_list in *.
      assert (Hleft := Hlist); apply list_app_inv_l2 in Hleft.
      rename Hlist into Hright;  apply list_app_inv_r2 in Hright.
      injection Hshape; clear Hshape; intro Hshape.
      subst. erewrite IHrest1; auto.
  Qed.

  Theorem shapeliness: forall A (t1 t2: T A),
      shape t1 = shape t2 /\ tolist t1 = tolist t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    assert (hyp1': (toBatch (A := unit) (A' := A) ∘ shape) t1 =
                      (toBatch (A := unit) (A' := A) ∘ shape) t2).
    { unfold compose, shape in *. now rewrite hyp1. }
    clear hyp1; rename hyp1' into hyp1.
    unfold shape in hyp1.
    rewrite toBatch_mapfst in hyp1.
    rewrite (tolist_through_runBatch A t1) in hyp2.
    rewrite (tolist_through_runBatch A t2) in hyp2.
    change (id t1 = id t2).
    rewrite id_through_runBatch.
    unfold compose. auto using shapeliness_tactical.
  Qed.

End shapeliness.

(** * Pointwise reasoning for operations *)
(******************************************************************************)
Section pointwise.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{ToMap_inst: Map T}
    `{ToSubset_inst: ToSubset T}
    `{ToBatch_inst: ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Lemma traverse_respectful :
    forall `{Applicative G} `(f1: A -> G B) `(f2: A -> G B) (t: T A),
      (forall (a: A), a ∈ t -> f1 a = f2 a) -> traverse f1 t = traverse f2 t.
  Proof.
    introv ? hyp.
    do 2 rewrite traverse_through_runBatch.
    unfold element_of in hyp.
    rewrite (tosubset_through_runBatch2 A B) in hyp.
    unfold compose in *.
    unfold ret in *.
    induction (toBatch t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros.
        apply hyp. now left.
      + apply hyp. now right.
  Qed.

  (** *** Corollaries *)
  (******************************************************************************)
  Corollary traverse_respectful_pure :
    forall `{Applicative G} `(f1: A -> G A) (t: T A),
      (forall (a: A), a ∈ t -> f1 a = pure a) -> traverse f1 t = pure t.
  Proof.
    intros.
    rewrite <- traverse_purity1.
    now apply traverse_respectful.
  Qed.

  Corollary traverse_respectful_map {A B} :
    forall `{Applicative G} (t: T A) (f: A -> G B) (g: A -> B),
      (forall a, a ∈ t -> f a = pure (g a)) -> traverse f t = pure (map g t).
  Proof.
    intros. rewrite <- (traverse_purity1 (G := G)).
    compose near t on right.
    rewrite traverse_map.
    apply traverse_respectful.
    assumption.
  Qed.

  Corollary traverse_respectful_id {A} :
    forall (t: T A) (f: A -> A),
      (forall a, a ∈ t -> f a = id a) -> traverse (G := fun A => A) f t = t.
  Proof.
    intros.
    change t with (pure (F := fun A => A) t) at 2.
    apply (traverse_respectful_pure (G := fun A => A)).
    assumption.
  Qed.

  Corollary map_respectful: forall `(f1: A -> B) `(f2: A -> B) (t: T A),
      (forall (a: A), a ∈ t -> f1 a = f2 a) -> map f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite map_to_traverse.
    rewrite map_to_traverse.
    apply (traverse_respectful (G := fun A => A)).
    assumption.
  Qed.

  #[export] Instance ContainerFunctor_Traverse:
    ContainerFunctor T.
  Proof.
    constructor.
    - rewrite compat_tosubset_traverse.
      typeclasses eauto.
    - typeclasses eauto.
    - intros. now apply map_respectful.
  Qed.

End pointwise.

(** * <<plength>> *)
(******************************************************************************)
Section length.

  Context
    `{Map T}
      `{ToBatch T}
      `{Traverse T}
      `{! TraversableFunctor T}
      `{! Compat_Map_Traverse T}
      `{! Compat_ToBatch_Traverse T}.

  Lemma plength_eq_length :
    forall {A} {B} (t: T A),
      length_Batch (toBatch (A' := B) t) = plength t.
  Proof.
    intros.
    unfold plength.
    rewrite (foldMap_through_runBatch2 A B).
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn.
      rewrite IHb.
      unfold_ops @NaturalNumbers.Monoid_op_plus.
      lia.
  Qed.

  Lemma plength_eq_length': forall {A} (t: T A),
      plength t = length_Batch (toBatch (A' := False) t).
  Proof.
    intros.
    symmetry.
    apply plength_eq_length.
  Qed.

  Lemma length_Batch_independent: forall `(t: T A) B C,
      length_Batch (toBatch (A' := B) t) =
        length_Batch (toBatch (A' := C) t).
  Proof.
    intros.
    rewrite length_Batch_spec.
    rewrite length_Batch_spec.
    compose near t on left.
    compose near t on right.
    rewrite <- traverse_through_runBatch.
    rewrite <- traverse_through_runBatch.
    rewrite (traverse_const2 _ B C).
    reflexivity.
  Qed.

End length.

(** * Factorizing Terms into <<shape>> and <<contents>> *)
(******************************************************************************)
Section deconstruction.

  Definition trav_contents
    {T: Type -> Type} {toBatch_T: ToBatch T} {traverse_T: Traverse T} {map_T: Map T}
    {cmt: Compat_Map_Traverse T}
    {cbt: Compat_ToBatch_Traverse T}
    {Trav_T: TraversableFunctor T}
    {A} (t: T A): Vector (plength t) A :=
    let v: Vector
             (length_Batch (toBatch (ToBatch := toBatch_T) (A' := False) t)) A
      := Batch_contents (toBatch t)
    in coerce_Vector_length (plength_eq_length t) v.

  Definition trav_make
    {T: Type -> Type}
    {map_T: Map T}
    {traverse_T: Traverse T}
    {toBatch_T: ToBatch T}
    {cmt: Compat_Map_Traverse T}
    {cmt: Compat_ToBatch_Traverse T}
    {Trav_T: TraversableFunctor T}
    {A B: Type} (t: T A):
    Vector (plength t) B -> T B :=
    (fun v =>
       let v' := coerce_Vector_length (eq_sym (plength_eq_length t)) v
       in Batch_make (toBatch t) v').

  Context
    `{Traverse T}
      `{Map T}
      `{ToBatch T}
      `{ToSubset T}
      `{! TraversableFunctor T}
      `{! Compat_Map_Traverse T}
      `{! Compat_ToBatch_Traverse T}
      `{! Compat_ToSubset_Traverse T}.

  #[local] Generalizable Variables v.


  (** ** Operations on Vectors *)
  (******************************************************************************)
  Section traverse_vector.

    #[export] Instance ToBatch_Vector {n: nat}:
    ToBatch (Vector n) := ToBatch_Traverse.

    Lemma plength_Vector {n: nat} {A: Type}:
      forall (v: Vector n A), plength v = n.
    Proof.
      intros.
      induction v using Vector_induction.
      - reflexivity.
      - unfold plength.
        rewrite foldMap_Vector_vcons.
        auto.
        typeclasses eauto.
    Qed.

    (*
    Lemma trav_contents_Vector_list {n: nat} {A: Type}:
      forall (l: list A) (Heq: length l = n)
        trav_contents {exists l | Heq} = v.
        *)

    Lemma trav_contents_Vector {n: nat} {A: Type}:
      forall (v: Vector n A),
        trav_contents v ~~ v.
    Proof.
      intros.
      unfold Vector_sim.
      destruct v.
      generalize dependent n.
      cbn.
      unfold trav_contents.
      induction x; intros.
      - cbn. reflexivity.
      - rewrite <- coerce_Vector_contents.
        specialize (IHx (length x)).
        specialize (IHx (eq_refl)).
        rewrite <- coerce_Vector_contents in IHx.
        cbn in IHx.
        rewrite <- IHx at 2.
        fequal.
        rewrite toBatch_to_traverse.
        subst.
        unfold traverse.
        unfold Traverse_Vector.
        unfold traverse_Vector.
        cbn.
        unfold mult_Batch.
        unfold Batch_contents.
    Abort.

    Lemma trav_make_Vector {n: nat} {A B: Type}:
      forall (v1: Vector n A) (v2: Vector (plength v1) B),
        (trav_make (B := B) v1 v2) ~~ v2.
    Proof.
      intros.
      induction v1 using Vector_induction.
      - assert (Hey: v2 = vnil).
        { apply Vector_nil_eq. }
        rewrite Hey.
        reflexivity.
      - cbn in v2.
        unfold trav_make.
        unfold toBatch.
        unfold ToBatch_Vector.
        unfold ToBatch_Traverse.
    Abort.

  End traverse_vector.

  (** ** Lemmas regarding <<trav_make>> *)
  (******************************************************************************)
  Section trav_make_lemmas.

    Context
      {A B: Type}.

    Lemma trav_make_sim:
      forall (t: T A), trav_make (B := B) t ~!~ trav_make t.
    Proof.
      intros.
      unfold trav_make.
      unfold Vector_fun_sim. split.
      - reflexivity.
      - intros.
        apply Batch_make_sim1.
        apply Vector_coerce_sim_l'.
        apply Vector_coerce_sim_r'.
        assumption.
    Qed.

    Lemma toBatch_trav_make {A'} {t: T A} {v: Vector (plength t) B}:
      toBatch (A' := A') (trav_make t v) =
        Batch_replace_contents (toBatch (A' := A') t)
          (coerce eq_sym (plength_eq_length t) in v).
    Proof.
      unfold trav_make.
      rewrite Batch_make_compose_rw1.
      rewrite Batch_replace_spec.
      apply Batch_make_sim2.
      - compose near t.
        rewrite trf_duplicate.
        rewrite compat_toBatch_traverse.
        reflexivity.
      - vector_sim.
    Qed.

  (** ** Naturality of <<trav_contents>> and <<trav_make>> *)
  (******************************************************************************)
  Lemma trav_contents_natural:
    forall (A B: Type) (t: T A) (f: A -> B),
      trav_contents (map f t) ~~ map f (trav_contents t).
  Proof.
    intros.
    unfold Vector_sim.
    unfold trav_contents.
    rewrite <- coerce_Vector_contents.
    rewrite <- map_coerce_Vector.
    compose near t on left.
    rewrite toBatch_mapfst.
    unfold compose at 2.
    rewrite <- coerce_Vector_contents.
    rewrite Batch_contents_natural.
    reflexivity.
  Qed.

  Lemma trav_make_natural:
    forall (A B C: Type) (t: T A) (f: B -> C) (v: Vector (plength t) B),
      trav_make t (map f v) = map f (trav_make t v).
  Proof.
    intros.
    unfold trav_make.
    rewrite (Batch_make_compose_rw1 (toBatch t) (map f)).
    assert (cut: map (map f) (toBatch t) =
                   mapsnd_Batch _ _ f (toBatch t)).
    { compose near t.
      now rewrite (toBatch_mapsnd). }
    rewrite (Batch_make_rw_alt
               (map (map f) (toBatch t))
               (mapsnd_Batch _ _ f (toBatch t))
               cut).
    rewrite Batch_make_natural2.
    apply Batch_make_sim1.
    rewrite map_coerce_Vector.
    rewrite map_coerce_Vector.
    rewrite coerce_Vector_compose.
    rewrite coerce_Vector_compose.
    rewrite coerce_Vector_compose.
    fequal; fequal; apply Vector_sim_eq.
    apply Vector_coerce_sim_r'.
    apply Vector_coerce_sim_l'.
    reflexivity.
  Qed.

    (*
    Lemma toBatch_trav_make {A A' B} {t: T A} {v: Vector (plength t) B}:
      toBatch (A' := A') (trav_make t v) =
        Batch_replace_contents
          (toBatch (A' := A') t)
          (coerce eq_sym (plength_eq_length t) in v).
    Proof.
      unfold trav_make.
      rewrite Batch_make_compose_rw1.
      rewrite Batch_replace_spec.
      apply Batch_make_sim2; vector_sim.
      compose near t.
      now rewrite <- trf_duplicate.
    Qed.
    *)

    (*
    Lemma trav_make_sim1:
      forall (t: T A) `{v1 ~~ v2},
        trav_make (B := B) t v1 = trav_make t v2.
    Proof.
      intros.
      unfold trav_make.
      apply Batch_make_sim1.
      vector_sim.
    Qed.

    Lemma trav_make_sim2:
      forall `(t1: T A) (t2: T A)
        `(v1: Vector (plength t1) B)
        `(v2: Vector (plength t2) B),
        t1 = t2 ->
        v1 ~~ v2 ->
        trav_make t1 v1 = trav_make t2 v2.
    Proof.
      intros.
      subst.
      now apply trav_make_sim1.
    Qed.
    *)

  End trav_make_lemmas.

  (** ** Relating <<tolist>> and <<trav_contents>> *)
  (******************************************************************************)
  Lemma tolist_trav_contents `{t: T A}:
    Vector_to_list A (trav_contents t) = List.rev (tolist t).
  Proof.
    intros.
    unfold trav_contents.
    rewrite (tolist_through_runBatch False).
    generalize (plength_eq_length (B := False) t).
    intros Heq.
    generalize dependent (plength t).
    induction (toBatch (A' := False) t); intros n Heq.
    - reflexivity.
    - rewrite runBatch_rw2.
      rewrite Batch_contents_rw2.
      unfold Vector_to_list.
      rewrite <- coerce_Vector_contents.
      unfold length_Batch at 1. (* hidden *)
      rewrite proj_vcons.
      cbn.
      unfold_ops @Monoid_op_list.
      unfold_ops @Return_list.
      rewrite List.rev_unit.
      fequal.
      cbn in Heq.
      assert (Hlen: length_Batch b = (n -1)) by lia.
      specialize (IHb (n - 1) Hlen).
      change (fun a => a :: nil) with (@ret list _ A).
      cbn in IHb.
      change (@app A) with (@Monoid_op_list A).
      rewrite <- IHb.
      unfold Vector_to_list.
      rewrite <- coerce_Vector_contents.
      reflexivity.
  Qed.

  (** ** Lens-like laws *)
  (******************************************************************************)
  Section lens_laws.

    (** *** get-put *)
    (******************************************************************************)
    Lemma trav_get_put `{t: T A}:
      trav_make t (trav_contents t) = t.
    Proof.
      unfold trav_make, trav_contents.
      enough (cut: Batch_make
                     (toBatch t)
                     (coerce eq_sym (plength_eq_length t)
                       in coerce (plength_eq_length (B := False) t)
                         in Batch_contents (toBatch t)) =
                     Batch_make (toBatch t) (Batch_contents (toBatch t))).
      rewrite cut.
      rewrite Batch_make_contents.
      compose near t.
      now rewrite trf_extract.
      { apply Batch_make_sim1.
        vector_sim.
        apply Batch_contents_toBatch_sim.
      }
    Qed.

    (** *** put-get *)
    (******************************************************************************)
    Lemma trav_contents_make {A B} {t: T A} {v: Vector (plength t) B}:
      trav_contents (trav_make t v) ~~ v.
    Proof.
      unfold trav_contents.
      vector_sim.
      rewrite toBatch_trav_make.
      rewrite Batch_put_get.
      vector_sim.
    Qed.

    (** *** put-put *)
    (******************************************************************************)
    Lemma trav_make_make
            `(t: T A) `(v: Vector (plength t) B)
            `(v1: Vector (plength (trav_make t v)) B')
            (v2: Vector (plength t) B')
            (pf: v1 ~~ v2):
      trav_make (trav_make t v) v1 =
        trav_make t v2.
    Proof.
      unfold trav_make at 1.
      unfold trav_make at 7.
      apply Batch_make_sim3.
      - symmetry.
        rewrite toBatch_trav_make.
        apply Batch_shape_replace_contents.
      - vector_sim.
    Qed.

    (** ** Lemmas regarding <<plength>> *)
    (******************************************************************************)
    Lemma plength_trav_make: forall `(t: T A) `(v: Vector _ B),
        plength t = plength (trav_make t v).
    Proof.
      intros.
      unfold plength at 1 2.
      do 2 change (fun (x:?X) => 1) with (const (A := X) 1).
      do 2 rewrite (foldMap_through_runBatch2 _ B).
      unfold compose.
      rewrite (@toBatch_trav_make A B B t v).
      rewrite <- (runBatch_const_contents (G := @const Type Type nat)).
      reflexivity.
    Qed.

    Lemma trav_make_make2:
      forall `(t: T A) `(v: Vector (plength t) B) (C: Type),
      trav_make (B := C) (trav_make t v) ~!~
        trav_make t.
    Proof.
      intros.
      unfold Vector_fun_sim. split.
      - rewrite <- plength_trav_make.
        reflexivity.
      - intros.
        rewrite (trav_make_make t v v1 v2); auto.
    Qed.

    (** ** Lemmas regarding <<shape>> and <<trav_make>> *)
    (******************************************************************************)
    Lemma trav_same_shape
            `(t1: T A) `(t2: T A'):
      shape t1 = shape t2 ->
      forall B, trav_make (B := B) t1 ~!~ trav_make t2.
    Proof.
      intros.
      unfold trav_make.
      apply Vector_coerce_fun_sim_l'.
      apply Vector_coerce_fun_sim_r'.
      apply Batch_make_shape.
      apply toBatch_shape.
      assumption.
    Qed.

  End lens_laws.

  (** ** Representation theorems *)
  (******************************************************************************)
  Lemma traverse_repr:
    forall `{Applicative G} (A B: Type) (t: T A) (f: A -> G B),
      traverse f t =
        map (trav_make t) (forwards (traverse (mkBackwards ∘ f) (trav_contents t))).
  Proof.
    intros.
    rewrite traverse_through_runBatch.
    unfold compose.
    rewrite runBatch_repr2.
    unfold trav_make, trav_contents.
    rewrite (traverse_Vector_coerce _ _ _ (plength_eq_length t)).
    change_left (
        map (Batch_make (toBatch t))
            (map
               (fun v: Vector (plength t) B =>
                  coerce eq_sym (plength_eq_length (B := B) t) in v)
               (forwards
                  (traverse (mkBackwards ∘ f)
                            (coerce (plength_eq_length (B := B) t) in
                              Batch_contents (toBatch t)))))).
    compose near ((forwards
                     (traverse (mkBackwards ∘ f)
                               (coerce (plength_eq_length (B := B) t)
                                 in Batch_contents (toBatch t))))).
    rewrite (fun_map_map).
    fequal.
    fequal.
    fequal.
    apply Vector_eq.
    apply Vector_coerce_sim_l'.
    apply Vector_coerce_sim_r'.
    eapply Batch_contents_toBatch_sim.
  Qed.

End deconstruction.

(** * Auto-refining <<Batch>> *)
(******************************************************************************)
Require Import ContainerFunctor.

Import ContainerFunctor.Notations.
Import Applicative.Notations.

#[export] Instance ToSubset_Batch1 {B C}: ToSubset (BATCH1 B C) :=
  ToSubset_Traverse.

Section pw_Batch.

  Lemma foldMap_Batch_rw2: forall {A B C: Type} `{Monoid M}
      (f: A -> M) (a: A) (rest: Batch A B (B -> C)),
      foldMap (T := BATCH1 B C) f (rest ⧆ a) =
        foldMap f rest ● f a.
  Proof.
    intros.
    unfold foldMap.
    rewrite traverse_Batch_rw2.
    reflexivity.
  Qed.

  Definition tosubset_Step1 {A B C:Type}:
    forall (a': A) (rest: Batch A B (B -> C)),
      forall (a: A),
        tosubset (F := BATCH1 B (B -> C)) rest a ->
        tosubset (F := BATCH1 B C) (Step rest a') a.
  Proof.
    introv.
    unfold_ops @ToSubset_Batch1 @ToSubset_Traverse.
    introv Hin.
    change ((evalAt a ∘ foldMap (T := BATCH1 B (B -> C))
                    (ret (T := subset))) rest) in Hin.
    change ((evalAt a ∘ foldMap (T := BATCH1 B C)
                    (ret (T := subset))) (rest ⧆ a')).
    rewrite (foldMap_morphism
               (T := BATCH1 B (B -> C))
               _ _ (ϕ := evalAt a)) in Hin.
    rewrite (foldMap_morphism
               (T := BATCH1 B C)
               _ _ (ϕ := evalAt a)).
    rewrite foldMap_Batch_rw2.
    now left.
  Defined.

  Definition tosubset_Step2 {A B C:Type}:
    forall (rest: Batch A B (B -> C)) (a: A),
      tosubset (F := BATCH1 B C) (Step rest a) a.
  Proof.
    intros.
    unfold_ops @ToSubset_Batch1 @ToSubset_Traverse.
    change ((evalAt a ∘ foldMap (T := BATCH1 B C)
                    (ret (T := subset))) (rest ⧆ a)).
    rewrite (foldMap_morphism
               (T := BATCH1 B C)
               _ _ (ϕ := evalAt a)).
    rewrite foldMap_Batch_rw2.
    now right.
  Qed.

  Lemma element_of_Step_spec: forall `(b: Batch A B (B -> C)) a a',
      a' ∈ (b ⧆ a) = (a' ∈ b \/ a' = a).
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite element_of_to_foldMap.
    rewrite foldMap_Batch_rw2.
    reflexivity.
  Qed.

  Definition sigMapP (A: Type) (P Q: A -> Prop) (Himpl: forall a, P a -> Q a):
    sig P -> sig Q :=
    fun σ => match σ with
          | exist _ a h => exist Q a (Himpl a h)
          end.

  Fixpoint elt_decorate
   {A B C: Type}
   (b: Batch A B C):
    Batch {a| tosubset (F := BATCH1 B C) b a} B C :=
    match b with
    | Done c => Done c
    | Step rest a =>
        Step (map (F := BATCH1 B (B -> C))
                  (sigMapP A
                           (tosubset (F := BATCH1 B (B -> C)) rest)
                           (tosubset (F := BATCH1 B C) (Step rest a))
                           (tosubset_Step1 a rest)
                  )
                  (elt_decorate rest))
             (exist _ a (tosubset_Step2 rest a))
    end.


  Definition runBatch_pw
               {A B C} (G: Type -> Type)
               `{Applicative G}:
    forall (b: Batch A B C) `(f1: {a | tosubset (F := BATCH1 B C) b a} -> G B), G C.
  Proof.
    intros.
    induction b.
    - apply (pure c).
    - apply (ap G (A := B)).
      apply IHb.
      + intros [a' a'in].
        apply f1.
        exists a'.
        change (a' ∈ (b ⧆ a)).
        rewrite element_of_Step_spec.
        now left.
      + apply f1.
        exists a.
        change (a ∈ (b ⧆ a)).
        rewrite element_of_Step_spec.
        now right.
  Defined.

End pw_Batch.

(** * Unclassified Stuff??? *)
(******************************************************************************)
Section misc.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{ToMap_inst: Map T}
    `{ToSubset_inst: ToSubset T}
    `{ToBatch_inst: ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Lemma map_sim_function `{Functor F} (A B: Type) (n m: nat):
    forall (f: Vector n A -> B) (g: Vector m A -> B)
      (Heq: n = m), (* This is derivable from f ~!~ g, but it's more convenient to let the caller give a proof than to wrap the output in an existential quantifier *)
      f ~!~ g ->
      map (F := F) f = map (precoerce Heq in g).
  Proof.
    introv Hsim.
    rewrite (Vector_coerce_fun_coerce Heq Hsim).
    reflexivity.
  Qed.

  Lemma map_sim_function_traverse_Vector
    `{Applicative G} (A B: Type) (n m: nat):
    forall (f: A -> G B) (Heq: n = m) (v1: Vector n A) (v2: Vector m A),
      v1 ~~ v2 ->
      map (coerce_Vector_length Heq) (traverse f v1) =
        (traverse f v2).

  Proof.
    introv Hsim.
    destruct Heq.
    rewrite coerce_Vector_eq_refl_pf.
    rewrite (fun_map_id).
    rewrite (Vector_sim_eq _ _ Hsim).
    reflexivity.
  Qed.

  Lemma traverse_trav_make:
    forall `{Applicative G} (X A B: Type) (t: T X) (f: A -> G B) (v: Vector (plength t) A),
      traverse (T := T) f (trav_make t v) =
        map (trav_make t) (forwards (traverse (mkBackwards ∘ f) v)).
  Proof.
    intros.
    rewrite traverse_repr.
    assert (Hlen: plength (trav_make t v) = plength t).
    { now rewrite <- plength_trav_make. }
    rewrite (map_sim_function B (T B) _ _ (trav_make (trav_make t v))
               (trav_make t (B := B)) Hlen).
    2: { apply trav_make_make2. }
    change (?f ○ ?pre) with (f ∘ pre).
    rewrite <- (fun_map_map).
    unfold compose at 1.
    fequal.
    compose near (traverse (mkBackwards ∘ f) (trav_contents (trav_make t v))).
    rewrite (natural (Natural := Natural_forwards)).
    unfold compose.
    fequal.
    apply map_sim_function_traverse_Vector.
    apply trav_contents_make.
  Qed.

  Lemma id_spec:
    forall (A: Type) (t: T A),
      id t = trav_make t (trav_contents t).
  Proof.
    intros.
    rewrite trav_get_put.
    reflexivity.
  Qed.

  Lemma map_spec:
    forall (A B: Type) (t: T A) (f: A -> B),
      map f t = trav_make t (map f (trav_contents t)).
  Proof.
    intros A B t f.
    rewrite <- trav_get_put at 1.
    apply Vector_fun_sim_eq.
    - apply trav_same_shape.
      rewrite shape_map.
      reflexivity.
    - apply trav_contents_natural.
  Qed.

  Lemma tosubset_spec:
    forall (A: Type) (t: T A),
      tosubset t =  tosubset (trav_contents t).
  Proof.
    intros A t.
    rewrite <- trav_get_put at 1.
    rewrite tosubset_to_foldMap.
    unfold foldMap.
    rewrite (traverse_trav_make).
    rewrite (map_const_spec (M := A -> Prop) (Vector (@plength T H A t) False) (T False)).
    change (id ?x) with x.
    rewrite tosubset_to_foldMap.
    unfold foldMap.
    compose near (trav_contents t) on left.
    (* Need to generalize this rewriting to commutative idempotent monoids,
not just subset applicative. *)
    Fail rewrite (traverse_commutative_idem (T' := Vector (plength t))
               _ _ (@ret subset _ A)).
  Admitted.

  Lemma shape_spec_lemma:
    forall (A: Type) (t: T A),
      trav_contents (shape t) ~~ Vector_tt (plength t).
  Proof.
    intros.
    (* LHS *)
    unfold trav_contents.
    apply Vector_coerce_sim_l'.
    unfold shape.
    replace (toBatch (A' := False) (map (const tt) t))
      with (mapfst_Batch A unit (B := False) (const tt) (toBatch t)).
    2:{ compose near t.
        now rewrite toBatch_mapfst. }
    unfold Vector_tt.
    unfold plength.
    rewrite foldMap_through_runBatch1.
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn.
      unfold_ops @NaturalNumbers.Monoid_op_plus.
      rewrite PeanoNat.Nat.add_1_r.
      cbn.
      apply vcons_sim.
      assumption.
  Qed.

  Lemma shape_spec:
    forall (A: Type) (t: T A),
      shape t = trav_make (B := unit) t (Vector_tt (plength t)).
  Proof.
    intros A t.
    unfold shape.
    rewrite map_spec.
    fequal.
    apply Vector_sim_eq.
    unfold Vector_sim.
    rewrite <- (trav_contents_natural A unit t (const tt)).
    change (map (const tt) t) with (shape t).
    rewrite shape_spec_lemma.
    reflexivity.
  Qed.

  Lemma trav_make_shape_spec:
    forall (A B: Type) (t: T A),
      trav_make (B := B) t ~!~ trav_make (B := B) (shape t).
  Proof.
    intros A B t.
    apply trav_same_shape.
    rewrite shape_shape.
    reflexivity.
  Qed.

  Lemma same_shape_implies_make:
    forall (A B C: Type) (t: T A) (u: T B),
      shape t = shape u ->
      trav_make (B := C) t ~!~ trav_make u.
  Proof.
    introv Hshape.
    eapply (transitive_Vector_fun_sim).
    apply (trav_make_shape_spec A C t).
    rewrite Hshape.
    apply symmetric_Vector_fun_sim.
    apply (trav_make_shape_spec B C u).
  Qed.

  Lemma shape_plength:
    forall (A: Type) (t: T A),
      plength t = plength (shape t).
  Proof.
    intros.
    unfold plength.
    unfold shape.
    compose near t on right.
    rewrite (foldMap_map).
    reflexivity.
  Qed.

  Lemma same_shape_implies_plength:
    forall (A B: Type) (t: T A) (u: T B),
      shape t = shape u ->
      plength t = plength u.
  Proof.
    introv Hshape.
    rewrite shape_plength.
    rewrite (shape_plength B u).
    rewrite Hshape.
    reflexivity.
  Qed.

  Lemma same_shape_implies_contents:
    forall (A B: Type) (t: T A) (u: T B)
      (Hshape: shape t = shape u),
      t = trav_make u
            (coerce (same_shape_implies_plength A B t u Hshape)
              in (trav_contents t)).
  Proof.
    intros.
    change t with (id t) at 1.
    rewrite id_spec.
    pose (same_shape_implies_make A B A t u (Hshape)) as cut.
    destruct cut as [ _ cut].
    apply cut.
    apply Vector_coerce_sim_r.
  Qed.

  Definition same_shape_zip_contents
    (A B: Type) (t: T A) (u: T B)
      (Hshape: shape t = shape u):
    Vector (plength t) (A * B) :=
      Vector_zip A B (plength t) (plength u) (trav_contents t) (trav_contents u)
        (same_shape_implies_plength A B t u Hshape).

  Lemma same_shape_zip_contents_fst
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    map fst (same_shape_zip_contents A B t u Hshape) = trav_contents t.
  Proof.
    unfold same_shape_zip_contents.
    now rewrite Vector_zip_fst.
  Qed.

  Lemma same_shape_zip_contents_snd
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    map snd (same_shape_zip_contents A B t u Hshape) ~~ trav_contents u.
  Proof.
    unfold same_shape_zip_contents.
    apply (Vector_zip_snd A B
            (plength t) (plength u)
            (trav_contents t) (trav_contents u)
            (same_shape_implies_plength A B t u Hshape)).
  Qed.

  Definition same_shape_zip
    (A B: Type) (t: T A) (u: T B)
      (Hshape: shape t = shape u):
      T (A * B) :=
    trav_make t (same_shape_zip_contents A B t u Hshape).

  Lemma same_shape_zip_fst
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    map fst (same_shape_zip A B t u Hshape) = t.
  Proof.
    unfold same_shape_zip.
    rewrite <- (trav_make_natural A (A * B) A t (@fst A B)
                 (same_shape_zip_contents A B t u Hshape)).
    rewrite same_shape_zip_contents_fst.
    rewrite trav_get_put.
    reflexivity.
  Qed.

  Lemma same_shape_zip_snd
    (A B: Type) (t: T A) (u: T B)
    (Hshape: shape t = shape u):
    map snd (same_shape_zip A B t u Hshape) = u.
  Proof.
    unfold same_shape_zip.
    rewrite <- (trav_make_natural A (A * B) B t (@snd A B)
                 (same_shape_zip_contents A B t u Hshape)).
    change u with (id u) at 2.
    rewrite id_spec.
    apply Vector_fun_sim_eq.
    - apply same_shape_implies_make.
      assumption.
    - apply same_shape_zip_contents_snd.
  Qed.

End misc.

(** * Lifting relations over Traversable functors *)
(******************************************************************************)
Section lifting_relations.

  Definition lift_relation {X} {A B:Type} `{Traverse X}
    (R: A -> B -> Prop): X A -> X B -> Prop :=
    traverse (G := subset) R.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{ToMap_inst: Map T}
    `{ToSubset_inst: ToSubset T}
    `{ToBatch_inst: ToBatch T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Lemma relation_spec1:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u <->
        (exists b: Vector (plength t) B,
            traverse (G := subset) R (trav_contents t) b /\
              trav_make t b = u).
  Proof.
    intros.
    unfold lift_relation.
    rewrite traverse_repr.
    compose near (trav_contents t).
    rewrite (traverse_commutative_idem
               (T' := Vector (plength t)) A B R).
    reflexivity.
  Qed.

  Lemma relation_implies_shape:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u -> shape t = shape u.
  Proof.
    introv Hrel.
    rewrite relation_spec1 in Hrel.
    destruct Hrel as [trav_contents_u [Hrel Hmake]].
    rewrite <- Hmake.
    change t with (id t) at 1.
    rewrite id_spec.
    unfold shape.
    rewrite <- trav_make_natural.
    rewrite <- trav_make_natural.
    fequal.
    clear.
    apply Vector_sim_eq.
    destruct (trav_contents t).
    destruct (trav_contents_u).
    cbn.
    unfold Vector_sim.
    cbn. clear trav_contents_u.
    generalize dependent x0.
    generalize dependent x.
    induction (plength t); intros x xlen y ylen; subst.
    - rewrite List.length_zero_iff_nil in xlen.
      rewrite List.length_zero_iff_nil in ylen.
      subst. reflexivity.
    - induction x.
      + cbn in xlen. inversion xlen.
      + destruct y.
        * inversion ylen.
        * cbn. fequal.
          apply IHn; auto.
  Qed.

  Lemma relation_to_zipped:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B),
      lift_relation R t u ->
        (exists zipped: T (A * B),
            map fst zipped = t /\
              map snd zipped = u /\
              Forall (uncurry R) zipped).
  Proof.
    introv Hrel.
    rewrite relation_spec1 in Hrel.
    destruct Hrel as [trav_contents_u [Hrel Hmake]].
    pose (zipped_contents:= Vector_zip_eq A B (plength t)
                             (trav_contents t)
                             (trav_contents_u)).
    exists (trav_make t zipped_contents).
    rewrite <- trav_make_natural.
    rewrite <- trav_make_natural.
    split.
    - unfold zipped_contents.
      rewrite Vector_zip_eq_fst.
      symmetry. apply id_spec.
    - split.
      + unfold zipped_contents.
        rewrite Vector_zip_eq_snd.
        assumption.
      + unfold zipped_contents.
        assert (
            Forall (uncurry R)
              (trav_make t
                 (Vector_zip_eq A B (plength t) (trav_contents t) trav_contents_u))
            =
              foldMap (M := Prop)
                (op := Monoid_op_and) (unit := Monoid_unit_true)
                (uncurry R)
              (trav_make t
                 (Vector_zip_eq A B (plength t)  (trav_contents t) trav_contents_u))).
        admit.
        rewrite H1.
        unfold foldMap.
        rewrite (traverse_trav_make (G := const Prop) A (A * B) False t (uncurry R)).
        unfold_ops @Map_const.
  Abort.


  Lemma relation_spec:
    forall (A B: Type) (R: A -> B -> Prop) (t: T A) (u: T B)
      (Heq: plength u = plength t),
      lift_relation R t u <->
        shape t = shape u /\
      lift_relation R (trav_contents t) (coerce Heq in trav_contents u).
  Proof.
    introv. split.
    -  introv Hrel.
       specialize (relation_implies_shape _ _ _ _ _ Hrel); intro.
       rewrite relation_spec1 in Hrel.
       destruct Hrel as [trav_contents_u [Htrav Hmake]].
       split.
       { auto. }
       { assert (cut: (coerce Heq in trav_contents u) = trav_contents_u).
         { apply Vector_sim_eq. subst.
           apply Vector_coerce_sim_l'.
           apply (trav_contents_make (t := t)).
         }
         rewrite cut.
         apply Htrav.
       }
    - intros [Hshape Hrel].
      rewrite relation_spec1.
      exists (coerce Heq in trav_contents u). split.
      + apply Hrel.
      + apply (same_shape_implies_make A B B t u) in Hshape.
        change u with (id u) at 3.
        rewrite id_spec.
        apply Hshape.
        apply Vector_coerce_sim_l.
  Qed.

  Lemma relation_natural1:
    forall (A B1 B2: Type) (R: B1 -> B2 -> Prop) (t: T A) (f: A -> B1),
      lift_relation R (map f t) = lift_relation (R ∘ map f) t.
  Proof.
    intros.
    unfold lift_relation.
    compose near t on left.
    rewrite (traverse_map (G2 := subset) R f).
    reflexivity.
  Qed.

  Lemma relation_natural2:
    forall (B1 A B2: Type) (R: B1 -> B2 -> Prop) (t: T B1) (u: T A) (f: A -> B2),
      lift_relation R t (map f u) = lift_relation (precompose f ∘ R) t u.
  Proof.
    intros.
    apply propositional_extensionality.
    rewrite relation_spec1.
    rewrite relation_spec1.
    split.
    - intros [trav_contents_map_u [H1 H2]].
      rewrite map_spec in H2.
      rewrite trav_make_natural in H2.
      try exists (trav_contents u).
  Abort.

  Lemma relation_respectful:
    forall (A B1 B2: Type) (R: B1 -> B2 -> Prop) (t: T A) (f: A -> B1) (g: A -> B2),
    (forall (a: A), a ∈ t -> R (f a) (g a)) -> lift_relation R (map f t) (map g t).
  Proof.
    introv hyp.
    rewrite relation_spec.
    split.
    rewrite shape_map.
    rewrite shape_map.
    reflexivity.
    unfold element_of in hyp.
    rewrite tosubset_spec in hyp.
    destruct (trav_contents t).
    subst.
  Abort.

End lifting_relations.
