From Tealeaves Require Export
  Examples.STLC.Syntax.

Import LN.Notations.
Import STLC.Syntax.Notations.

#[local] Notation "'P'" := pure.
#[local]  Notation "'BD'" := binddt.
#[local] Open Scope tealeaves_scope.

Section section.
  Context {E : Type} {T : Type -> Type} `{Mapdt E T}.

  Lemma Forall_ctx_to_foldMapd :
    forall {A t} (f: E * A -> Prop),
      Forall_ctx f t = foldMapd f t.
  Proof.
    reflexivity.
  Qed.
  Lemma foldMapd_to_Forall_ctx :
    forall {A t} (f: E * A -> Prop),
      foldMapd f t = Forall_ctx f t.
  Proof.
    reflexivity.
  Qed.

  Lemma exists_false_false
          `{DecoratedTraversableFunctor E T}:
    forall {A} (t: T A),
      foldMapd (op := Monoid_op_or) (unit := Monoid_unit_false)
        (const False) t = False.
  Proof.
    intros.
    rewrite foldMapd_through_toctxlist.
    unfold compose. induction (toctxlist t).
    - reflexivity.
    - cbn. rewrite IHe. do 2 unfold transparent tcs. propext;
                        intuition.
  Qed.

End section.

Lemma binddt_ret:
  forall {W : Type} {T G : Type -> Type}
    `{DecoratedTraversableMonad W T}
    `{Applicative G},
      forall (A B : Type) (f : W * A -> G (T B)) (a: A),
        binddt f (ret a) = f (Ƶ, a).
Proof.
  intros.
  compose near a.
  rewrite kdtm_binddt0.
  reflexivity.
Qed.
(*
Ltac simplify := simplify_with_simplify_binddt term ltac:(fun unit => cbn).
 *)

Ltac normalize_fns :=
  match goal with
  | |- context[?f ∘ id] =>
      change (f ∘ id) with f
  | |- context[(id ∘ ?f)] =>
      change (id ∘ f) with f
  end.

Ltac normalize_fns_in H :=
  match goal with
  | H: context[?f ∘ id] |- _ =>
      change (f ∘ id) with f in H
  | H: context[(id ∘ ?f)] |- _ =>
      change (id ∘ f) with f in H
  end.

Ltac normalize_id :=
  match goal with
  | |- context[id ?t] =>
      change (id t) with t
  end.

Ltac normalize_id_in :=
  match goal with
  | H: context[id ?t] |- _ =>
      change (id t) with t in H
  end.

Ltac push_preincr_into_fn :=
  match goal with
  | |- context[(?g ∘ ?f) ⦿ ?w] =>
      rewrite (preincr_assoc g f w)
  | |- context[extract ⦿ ?w] =>
      rewrite (extract_preincr w)
  end.

Ltac push_preincr_into_fn_in :=
  match goal with
  | H: context[(?g ∘ ?f) ⦿ ?w] |- _ =>
      rewrite (preincr_assoc g f w) in H
  | H: context[extract ⦿ ?w] |- _ =>
      rewrite (extract_preincr w) in H
  end.

Ltac simplify_post_binddt_ret :=
  match goal with
  | |- context[map (F := const ?X) ?f ∘ ?g] =>
      change (map (F := const ?X) ?f ∘ ?g) with g
  | |- context[map (F := const ?X) ?f] =>
      rewrite map_const_rw;
      try normalize_id
  | |- context[(?f ∘ extract) (?w, ?a)] =>
      change ((f ∘ extract) (w, a)) with (f a)
  | |- context[extract (?w, ?a)] =>
      change (extract (w, a)) with a
  | |- context[(?f ∘ ret (T := ?T) ?a)] =>
      change (f ∘ ret (T := T) a) with (f (ret a))
  end.

Ltac simplify_post_binddt_ret_in :=
  match goal with
  | H: context[map (F := const ?X) ?f ∘ ?g] |- _ =>
      change (map (F := const ?X) ?f ∘ ?g) with g in H
  | H: context[map (F := const ?X) ?f] |- _ =>
      rewrite map_const_rw in H;
      try normalize_id_in H
  | H: context[(?f ∘ extract) (?w, ?a)] |- _ =>
      change ((f ∘ extract) (w, a)) with (f a) in H
  | H: context[extract (?w, ?a)] |- _ =>
      change (extract (w, a)) with a in H
  | H: context[(?f ∘ ret (T := ?T) ?a)] |- _ =>
      change (f ∘ ret (T := T) a) with (f (ret a)) in H
  end.

Ltac simplify_binddt_ret :=
  match goal with
  | |- context[binddt (T := ?T) ?f (?rtn ?t)] =>
      change (rtn t) with (ret (T := T) t);
      rewrite binddt_ret;
      repeat simplify_post_binddt_ret
  end.

Ltac simplify_binddt_ret_in H :=
  match goal with
  | H: context[binddt (T := ?T) ?f (?rtn ?t)] |- _ =>
      change (rtn t) with (ret (T := T) t) in H;
      rewrite binddt_ret in H;
      repeat simplify_post_binddt_ret_in H
  end.

Ltac simplify_binddt_core :=
  match goal with
  | |- context[binddt (W := ?W) (T := ?T)
                (H := ?H) (H0 := ?H0) (H1 := ?H1)
                (U := ?U) (G := ?G) ?f ?t] =>
      let e := constr:(binddt (W := W) (T := T) (U := U) (G := G)
                         (H := H) (H0 := H0) (H1 := H1)
                         f t) in
      let e' := eval cbn in e in
        debug "simplify_binddt_core|change";
        progress (change e with e')
  end.

Ltac simplify_binddt_core_in :=
  match goal with
  | H: context[binddt (W := ?W) (T := ?T)
                (H := ?H) (H0 := ?H0) (H1 := ?H1)
                (U := ?U) (G := ?G) ?f ?t] |- _ =>
      let e := constr:(binddt (W := W) (T := T) (U := U) (G := G)
                         (H := H) (H0 := H0) (H1 := H1)
                         f t) in
      let e' := eval cbn in e in
        debug "simplify_binddt_core|change";
        progress (change e with e' in H)
  end.

Ltac simplify_binddt :=
   (simplify_binddt_ret
    (* || cbn; repeat push_preincr_into_fn *)
    || simplify_binddt_core;
    repeat push_preincr_into_fn).

Ltac simplify_binddt_in H :=
  (simplify_binddt_ret_in H
    || simplify_binddt_core_in H;
    repeat push_preincr_into_fn_in H).

Ltac simplify_mapdt :=
  match goal with
  | |- context[mapdt (T := ?T) ?f (ret ?t)] =>
      idtac "mapdt_ret should be called here"
  | |- context[mapdt (T := ?T)] =>
      rewrite (mapdt_to_binddt (T := T));
      simplify_binddt;
      repeat rewrite <- (mapdt_to_binddt (T := T))
  end.

Ltac simplify_mapdt_in :=
  match goal with
  | H: context[mapdt (T := ?T) ?f (ret ?t)] |- _ =>
      idtac "mapdt_ret should be called here"
  | H: context[mapdt (T := ?T)] |- _ =>
      rewrite (mapdt_to_binddt (T := T)) in H;
      simplify_binddt_in H;
      repeat rewrite <- (mapdt_to_binddt (T := T)) in H
  end.

Ltac simplify_bindt :=
  match goal with
  | |- context[bindt (T := ?T) ?f (ret ?t)] =>
      idtac "bindt_ret should be called here"
  | |- context[bindt (T := ?T)] =>
      rewrite (bindt_to_binddt (T := T));
      simplify_binddt;
      repeat rewrite <- (bindt_to_binddt (T := T))
  end.

Ltac simplify_bindd :=
  match goal with
  | |- context[bindd (T := ?T) ?f (ret ?t)] =>
      idtac "bindt_ret should be called here"
  | |- context[bindd (T := ?T)] =>
      rewrite (bindd_to_binddt (T := T));
      simplify_binddt;
      repeat rewrite <- (bindd_to_binddt (T := T));
      repeat simplify_applicative_I
  end.

Ltac simplify_bind :=
  match goal with
  | |- context[bind (T := ?T) ?f (ret ?t)] =>
      idtac "bind_ret should be called here"
  | |- context[bind (T := ?T)] =>
      rewrite (bind_to_bindd (T := T));
      simplify_bindd;
      repeat rewrite <- (bind_to_bindd (T := T))
  end.

Ltac simplify_traverse :=
  match goal with
  | |- context[traverse (T := ?T) ?f (ret ?t)] =>
      idtac "traverse_ret should be called here"
  | |- context[traverse (T := ?T) (G := ?G) ?f ?t] =>
      rewrite (traverse_to_bindt (T := T) (G := G) f);
      repeat simplify_bindt;
      repeat rewrite <- (traverse_to_bindt (T := T))
  end.

Ltac simplify_monoid_units_in H :=
  match goal with
  | H: context[Ƶ ● ?m] |- _ =>
      debug "monoid_id_r";
      rewrite (monoid_id_r m) in H
  | H: context[?m ● Ƶ] |- _ =>
      debug "monoid_id_l";
      rewrite (monoid_id_l m) in H
  end.

Ltac simplify_foldMapd_post :=
      repeat simplify_applicative_const;
      (* ^ above step creates some ((Ƶ ● m) ● n) *)
      repeat simplify_monoid_units.

Ltac simplify_foldMapd :=
  match goal with
  | |- context[foldMapd (T := ?T) (M := ?M) (op := ?op) (unit := ?unit)] =>
      rewrite foldMapd_to_mapdt1;
      simplify_mapdt;
      repeat rewrite <- foldMapd_to_mapdt1;
      simplify_foldMapd_post
  end.

Ltac simplify_foldMapd_post_in H :=
      repeat simplify_applicative_const_in H;
      repeat simplify_monoid_units_in H.

Ltac simplify_foldMapd_in :=
  match goal with
  | H: context[foldMapd (T := ?T) (M := ?M) (op := ?op) (unit := ?unit)] |- _ =>
      rewrite foldMapd_to_mapdt1 in H;
      simplify_mapdt_in H;
      repeat rewrite <- foldMapd_to_mapdt1 in H;
      simplify_foldMapd_post_in H
  end.

Ltac simplify_foldMap_post :=
  repeat simplify_applicative_const;
  repeat simplify_monoid_units;
  repeat change (const ?x ?y) with x.

Ltac simplify_foldMap :=
  match goal with
  | |- context[foldMap (T := ?T) (M := ?M) (op := ?op) (unit := ?unit)] =>
      rewrite foldMap_to_traverse1;
      simplify_traverse;
      repeat rewrite <- foldMap_to_traverse1;
      simplify_foldMap_post
  end.

Lemma monoid_conjunction_rw:
  forall (P1 P2: Prop),
    monoid_op (Monoid_op := Monoid_op_and) P1 P2 = (P1 /\ P2).
Proof.
  reflexivity.
Qed.

Ltac simplify_monoid_conjunction :=
  match goal with
  | |- context[monoid_op (Monoid_op := Monoid_op_and) ?P1 ?P2] =>
      rewrite monoid_conjunction_rw
  end.

Ltac simplify_monoid_conjunction_in H :=
  rewrite monoid_conjunction_rw in H.

Lemma monoid_append_rw:
  forall {A} (l1 l2: list A),
    monoid_op (Monoid_op := Monoid_op_list) l1 l2 = l1 ++ l2.
Proof.
  reflexivity.
Qed.

Lemma monoid_disjunction_rw:
  forall (P1 P2: Prop),
    monoid_op (Monoid_op := Monoid_op_or) P1 P2 = (P1 \/ P2).
Proof.
  reflexivity.
Qed.

Ltac simplify_monoid_disjunction :=
  match goal with
  | |- context[monoid_op (Monoid_op := Monoid_op_or) ?P1 ?P2] =>
      rewrite monoid_disjunction_rw
  end.

Ltac simplify_monoid_append :=
  rewrite monoid_append_rw.

Lemma monoid_subset_rw:
  forall {A} (l1 l2: subset A),
    monoid_op (Monoid_op := Monoid_op_subset) l1 l2 = l1 ∪ l2.
Proof.
  reflexivity.
Qed.

Ltac simplify_monoid_subset :=
  rewrite monoid_subset_rw.

Ltac simplify_tolist :=
  match goal with
  | |- context[tolist (F := ?T) ?t] =>
      rewrite (tolist_to_foldMap (T := T));
      simplify_foldMap;
      repeat rewrite <- (tolist_to_foldMap (T := T));
      repeat simplify_monoid_append
  end.

Ltac simplify_tosubset :=
  match goal with
  | |- context[tosubset (F := ?T) (A := ?A) ?t] =>
      rewrite (tosubset_to_foldMap (T := T) A);
      simplify_foldMap;
      repeat rewrite <- (tosubset_to_foldMap (T := T));
      repeat simplify_monoid_subset
  end;
  (* This should only be necessary after binddt (ret x)) *)
  try match goal with
  | |- context[ret (T := ?T) (Return := Return_subset) ?a] =>
      unfold_ops @Return_subset
    end.

Ltac simplify_toctxset :=
  match goal with
  | |- context[toctxset (F := ?T) ?t] =>
      rewrite (toctxset_to_foldMapd (T := T) t);
      simplify_foldMapd;
      repeat rewrite <- (toctxset_to_foldMapd (T := T));
      repeat simplify_monoid_subset
  end;
  (* This should only be necessary after binddt (ret x)) *)
  try match goal with
  | |- context[ret (T := ?T) (Return := Return_ctxset) ?a] =>
      unfold_ops @Return_ctxset
    end.

Ltac simplify_element_of :=
  match goal with
  | |- context[element_of (F := ?T) (A := ?A) ?t] =>
      rewrite (element_of_to_foldMap (T := T) A t);
      simplify_foldMap;
      repeat rewrite <- (element_of_to_foldMap (T := T));
      repeat simplify_monoid_disjunction
  end.

Lemma simplify_singleton_ctx_S_preincr: forall {A} (a: A),
  forall n, {{(S n, a)}} ⦿ 1 = {{(n, a)}}.
Proof.
  intros. ext [depth i]. cbv.
  propext; do 2 rewrite pair_equal_spec; intuition.
Qed.

Lemma simplify_singleton_ctx_0_preincr: forall {A} (a: A),
    {{(0, a)}} ⦿ 1 = const False.
Proof.
  intros. ext [depth i]. cbv.
  propext; rewrite pair_equal_spec; intuition.
Qed.

Lemma simplify_singleton_ctx_preincr: forall {A} (a: A) n,
    n > 1 ->
    {{(n, a)}} ⦿ 1 = {{(n - 1, a)}}.
Proof.
  intros. ext [depth i].
  unfold preincr, incr, compose.
  simpl_subset. propext;
    do 2 rewrite pair_equal_spec;
    unfold_ops @Monoid_op_plus;
    intuition.
Qed.

Ltac simplify_singleton_ctx_under_binder :=
  match goal with
  | |- context[{{?p}} ⦿ 1] =>
      rewrite simplify_singleton_ctx_S_preincr
  | |- context[{{(0, ?l)}} ⦿ 1] =>
      rewrite simplify_singleton_ctx_0_preincr
  end.

Ltac simplify_element_ctx_of :=
  match goal with
  | |- context[element_ctx_of (T := ?T) (A := ?A) ?p] =>
      rewrite (element_ctx_of_to_foldMapd (T := T) A p);
      simplify_foldMapd;
      try simplify_singleton_ctx_under_binder;
      repeat rewrite <- (element_ctx_of_to_foldMapd (T := T));
      repeat simplify_monoid_disjunction
  end;
  (* This should only be necessary after binddt (ret x)) *)
  simpl_subset;
  try rewrite pair_equal_spec.

Ltac simplify_Forall_ctx :=
  rewrite Forall_ctx_to_foldMapd;
  simplify_foldMapd;
  repeat rewrite <- Forall_ctx_to_foldMapd;
  repeat simplify_monoid_conjunction.

Ltac simplify_Forall_ctx_in H :=
  rewrite Forall_ctx_to_foldMapd in H;
  simplify_foldMapd_in H;
  repeat rewrite <- Forall_ctx_to_foldMapd in H;
  repeat simplify_monoid_conjunction_in H.

Ltac simplify_lc_loc_under_binder :=
  match goal with
  | |- context[lc_loc ?n ⦿ 1] =>
      rewrite lc_loc_S
  | |- context[lc_loc ?n ⦿ ?m] =>
      rewrite lc_loc_preincr
  end.

Ltac simplify_lc_loc_leaf :=
  match goal with
  | |- context[lc_loc ?n (?w, Fr ?x)] =>
      rewrite lc_loc_Fr
  | |- context[lc_loc 0 (0, Bd ?b)] =>
      rewrite lc_loc_00Bd
  | |- context[lc_loc 0 (?w, Bd ?b)] =>
      rewrite lc_loc_0Bd
  | |- context[lc_loc ?n (?w, Bd ?b)] =>
      rewrite lc_loc_nBd
  end.

Ltac simplify_arithmetic :=
  match goal with
  | |- context[(?x + 0)%nat] =>
      replace (x + 0)%nat with x by lia
  | |- context[(0 + ?x)%nat] =>
      replace (0 + x)%nat with x by lia
  end.

Ltac simplify_LC :=
  repeat change (LC ?t) with (LCn 0 t);
  rewrite LCn_spec;
  simplify_Forall_ctx;
  repeat simplify_lc_loc_under_binder;
  ( unfold_ops @Monoid_op_plus @Monoid_unit_zero;
    try simplify_lc_loc_leaf;
    repeat simplify_arithmetic);
  (* ^ This should really only apply at (ret) *)
  repeat rewrite <- LCn_spec;
  repeat change (LCn 0 ?t) with (LC t).


Ltac simplify_LC_in H :=
  repeat change (LC ?t) with (LCn 0 t) in H;
  rewrite LCn_spec in H;
  simplify_Forall_ctx_in H;
  repeat rewrite <- LCn_spec in H;
  repeat change (LCn 0 ?t) with (LC t) in H.


Ltac simplify_free_loc :=
  match goal with
  | |- context[free_loc ?v] =>
      let e := constr:(free_loc v)in
      let e' := eval cbn in e in
        change e with e' in *
  end.

Ltac simplify_free :=
  unfold free;
  simplify_foldMap;
  (* ^^ this exposes ● with lists *)
  repeat simplify_monoid_append;
  repeat change (foldMap free_loc ?t) with (free t);
  repeat simplify_free_loc.

Ltac simplify_FV :=
  unfold FV;
  simplify_free;
  autorewrite with tea_rw_atoms;
  repeat match goal with
    | |- context[atoms ○ free (T := ?T)] =>
        change (atoms ○ free (T := T))
        with (FV (T := T))
    | |- context[atoms (free (T := ?T) ?t)] =>
        change (atoms (free (T := T) t))
        with (FV (T := T) t)
    end.

Ltac simplify_open :=
  unfold open;
  simplify_bindd;
  repeat match goal with
  | |- context[bindd (open_loc ?u) ?t] =>
      try change (bindd (open_loc u) t) with (open u t)
    end.

Ltac simplify_subst :=
  unfold subst;
  simplify_bind;
  repeat match goal with
  | |- context[bind (subst_loc ?x ?u) ?t] =>
      try change (bind (subst_loc x u) t) with (subst x u t)
  end.

Ltac simplify_derived_operations :=
  match goal with
  | |- context[tolist ?t] =>
      debug "";
      simplify_tolist
  | |- context[element_ctx_of ?x ?t] =>
      debug "";
      simplify_element_ctx_of
  | |- context[toctxset ?t] =>
      debug "";
      simplify_toctxset
  | |- context[element_of ?x ?t] =>
      debug "";
      simplify_element_of
  | |- context[tosubset ?t] =>
      debug "";
      simplify_tosubset
  end.

Ltac simplify_LN :=
  match goal with
  | |- context[LCn ?t] =>
      debug "";
      simplify_LC
  | |- context[LC ?t] =>
      debug "";
      simplify_LC
  | |- context[free ?t] =>
      debug "";
      simplify_free
  | |- context[FV ?t] =>
      debug "";
      simplify_FV
  | |- context[open ?t] =>
      debug "";
      simplify_open
  | |- context[subst ?x ?u ?t] =>
      debug "";
      simplify_subst
  end.

Ltac simplify :=
  repeat simplify_LN;
  repeat simplify_derived_operations;
  simpl_list.

(** ** Rewriting lemmas for <<LC>> *)
(******************************************************************************)
Theorem term_lcn11 : forall (n : nat) (m : nat),
    LCn m (tvar (Bd n)) <-> n < m.
Proof.
  intros. simplify_LC. reflexivity.
Qed.

Theorem term_lcn12 : forall (x : atom) (m : nat),
    LCn m (tvar (Fr x)) <-> True.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lcn2 : forall (X : typ) (t : term LN) (m : nat),
    LCn m (lam X t) <-> LCn (S m) t.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lcn3 : forall (t1 t2 : term LN) (m : nat),
    LCn m (⟨t1⟩(t2)) <->
      LCn m t1 /\ LCn m t2.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lc11 : forall (n : nat),
    LC (tvar (Bd n)) <-> False.
Proof.
  intros. simplify_LN. lia.
Qed.

Theorem term_lc12 : forall (x : atom),
    LC (tvar (Fr x)) <-> True.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lc2 : forall (X : typ) (t : term LN),
    LC (lam X t) <-> LCn 1 t.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

Theorem term_lc3 : forall (t1 t2 : term LN),
    LC (⟨t1⟩ (t2)) <-> LC t1 /\ LC t2.
Proof.
  intros. simplify_LN. reflexivity.
Qed.

(** ** Rewriting lemmas for <<tolist>>, <<toset>>, <<∈>> *)
(******************************************************************************)
Section term_container_rewrite.

  Variable
    (A : Type).

  Lemma tolist_tvar_rw1: forall (x: A),
      tolist (tvar x) = [x].
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma tolist_term_rw2: forall (X: typ) (t: term A),
      tolist (lam X t) = tolist t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma tolist_term_rw3: forall (t1 t2: term A),
      tolist (app t1 t2) = tolist t1 ++ tolist t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.
  Lemma toset_tvar_rw1: forall (x: A),
      tosubset (tvar x) = {{x}}.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma toset_term_rw2: forall (X: typ) (t: term A),
      tosubset (lam X t) = tosubset t.
  Proof.
    intros. simplify_tosubset. reflexivity.
  Qed.

  Lemma toset_term_rw3: forall (t1 t2: term A),
      tosubset (app t1 t2) = tosubset t1 ∪ tosubset t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_rw1: forall (x y: A),
      x ∈ tvar y <-> x = y.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_rw2: forall (y: A) (X: typ) (t: term A),
      y ∈ (lam X t) <-> y ∈ t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Lemma in_term_3: forall (t1 t2: term A) (y: A),
      y ∈ (app t1 t2) <-> y ∈ t1 \/ y ∈ t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

End term_container_rewrite.

(** ** Rewriting lemmas for <<free>>, <<freeset>> *)
(******************************************************************************)
Section term_free_rewrite.

  Variable (A : Type).

  Definition term_free11 : forall (b : nat),
      free (tvar (Bd b)) = [].
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_in_free11 : forall (b : nat) (x : atom),
      x ∈ free (tvar (Bd b)) <-> False.
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_free12 : forall (y : atom),
      free (tvar (Fr y)) = [y].
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_in_free12 : forall (y : atom) (x : atom),
      x ∈ free (tvar (Fr y)) <-> x = y.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_free2 : forall (t : term LN) (X : typ),
      free (lam X t) = free t.
  Proof.
    intros. simplify_LN. reflexivity.
  Qed.

  Definition term_in_free2 : forall (x : atom) (t : term LN) (X : typ),
      x ∈ free (lam X t) <-> x ∈ free t.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_free3 : forall (x : atom) (t1 t2 : term LN),
      free (app t1 t2) = free t1 ++ free t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_in_free3 : forall (x : atom) (t1 t2 : term LN),
      x ∈ free (app t1 t2) <-> x ∈ free t1 \/ x ∈ free t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

  Definition term_in_FV11 : forall (b : nat) (x : atom),
      x `in` FV (tvar (Bd b)) <-> False.
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Definition term_in_FV12 : forall (y : atom) (x : atom),
      AtomSet.In x (FV (tvar (Fr y))) <-> x = y.
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Lemma term_in_FV2 : forall (x : atom) (t : term LN) (X : typ),
      AtomSet.In x (FV (lam X t)) <-> AtomSet.In x (FV t).
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Lemma term_in_FV3 : forall (x : atom) (t1 t2 : term LN),
      AtomSet.In x (FV (app t1 t2)) <->
        AtomSet.In x (FV t1) \/ AtomSet.In x (FV t2).
  Proof.
    intros. simplify_FV. reflexivity.
  Qed.

  Open Scope set_scope.

  Lemma term_FV11 : forall (b : nat) (x : atom),
      FV (tvar (Bd b)) [=] ∅.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

  Lemma term_FV12 : forall (y : atom),
      FV (tvar (Fr y)) [=] {{ y }}.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

  Lemma term_FV2 : forall (t : term LN) (X : typ),
      FV (lam X t) [=] FV t.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

  Lemma term_FV3 : forall (t1 t2 : term LN),
      FV (app t1 t2) [=] FV t1 ∪ FV t2.
  Proof.
    intros. simplify_FV. fsetdec.
  Qed.

End term_free_rewrite.

(** ** Rewriting lemmas for <<foldMapd>> *)
(******************************************************************************)
Section term_foldMapd_rewrite.

  Context {A M : Type} (f : nat * A -> M) `{Monoid M}.

  Lemma term_foldMapd1 : forall (a : A),
      foldMapd f (tvar a) = f (Ƶ, a).
  Proof.
    intros. simplify_foldMapd. reflexivity.
  Qed.

  Lemma term_foldMapd2 : forall X (t : term A),
      foldMapd f (λ X t) = foldMapd (f ⦿ 1) t.
  Proof.
    intros. simplify_foldMapd. reflexivity.
  Qed.

  Lemma term_foldMapd3 : forall (t1 t2 : term A),
      foldMapd f (⟨t1⟩ (t2)) = foldMapd f t1 ● foldMapd f t2.
  Proof.
    intros. simplify_foldMapd. reflexivity.
  Qed.

End term_foldMapd_rewrite.

(** ** Rewriting lemmas for <<∈d>> *)
(******************************************************************************)
Section term_ind_rewrite.

  Lemma term_ind1 : forall (l1 l2 : LN) (n : nat),
      (n, l1) ∈d (tvar l2) <-> n = Ƶ /\ l1 = l2.
  Proof.
    intros. simplify_element_ctx_of. reflexivity.
  Qed.

  Ltac print_goal := match goal with
  | |- ?g => idtac g (* prints goal *)
  end.


  Lemma term_ind2 : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d t = (S n, l) ∈d (λ X t).
  Proof.
    intros. simplify_element_ctx_of. reflexivity.
  Qed.

  Lemma term_ind2_nZ : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) -> n <> 0.
  Proof.
    introv.
    destruct n.
    - simplify_element_ctx_of.
      rewrite exists_false_false.
      easy.
    - simplify_element_ctx_of.
      easy.
  Qed.

  Lemma term_ind3 : forall (t1 t2 : term LN) (n : nat) (l : LN),
      (n, l) ∈d (⟨t1⟩ (t2)) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    intros. simplify. reflexivity.
  Qed.

End term_ind_rewrite.

(** ** Rewriting lemmas for <<open>> *)
(******************************************************************************)
Lemma open_term_rw2: forall (t1 t2: term LN) u,
    open u (app t1 t2) = app (open u t1) (open u t2).
Proof.
  intros. simplify_open. reflexivity.
Qed.

Lemma open_term_rw3: forall τ (t: term LN) u,
    open u (λ τ t) = λ τ (bindd (open_loc u ⦿ 1) t).
Proof.
  intros. simplify_open. reflexivity.
Qed.

(** ** Rewriting lemmas for <<subst>> *)
(******************************************************************************)
Lemma subst_term_rw2: forall (t1 t2: term LN) x u,
    subst x u (app t1 t2) =
      app (subst x u t1) (subst x u t2).
Proof.
  intros. simplify_subst. reflexivity.
Qed.

Lemma subst_term_rw3: forall τ (t: term LN) x u,
    subst x u (λ τ t) =
      λ τ (subst x u t).
Proof.
  intros. simplify_subst. reflexivity.
Qed.
