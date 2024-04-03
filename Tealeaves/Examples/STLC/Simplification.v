From Tealeaves Require Export
  Examples.STLC.Syntax.

Import STLC.Syntax.Notations.
#[local] Notation "'P'" := pure.
#[local]  Notation "'BD'" := binddt.

Definition DEBUG : bool := false.

Tactic Notation "debug" string(x) :=
  let debug := eval compute in DEBUG in
  (match debug with
  | true => idtac x
  | false => idtac
   | _ => idtac "debug pattern match failed with ";
         idtac x
   end).

(*|
========================================
Simplification automation
========================================
|*)


(*
Ltac binddt_term_1 :=
  change ((BD ?f) (tvar ?x)) with (f (0, x)).

Ltac binddt_term_2 :=
  change ((BD ?f) ((λ) ?τ ?body)) with
    (P ((λ) τ) <⋆> BD (f ⦿ 1) body).

Ltac binddt_term_3 :=
  change ((BD ?f) (app ?t1 ?t2)) with
    (P (@app _) <⋆> BD f t1 <⋆> BD f t2).
 *)

Section rw.

  Context
    {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
      {v1 v2 : Type}.

  Implicit Type (f: nat * v1 -> G (term v2)).

  Definition binddt_term_rw1: forall x f,
      binddt f (tvar x) = f (0, x) := ltac:(reflexivity).

  Definition binddt_term_rw2: forall τ body f,
      binddt f (@lam _ τ body) =
        (P ((λ) τ) <⋆> BD (f ⦿ 1) body)
    := ltac:(reflexivity).

  Definition binddt_term_rw3: forall t1 t2 f,
      binddt f (@app _ t1 t2) =
        (P (@app _) <⋆> BD f t1 <⋆> BD f t2)
    := ltac:(reflexivity).

End rw.

Ltac step_binddt_term :=
  match goal with
  | |- context[BD ?f (tvar ?y)] =>
      debug "step_BD_tvar";
      rewrite binddt_term_rw1
  | |- context[((BD ?f) ((λ) ?τ ?body))] =>
      debug "step_BD_lam";
      rewrite binddt_term_rw2
  | |- context[((BD ?f) (app ?t1 ?t2))] =>
      debug "step_BD_app";
      rewrite binddt_term_rw3
  end.

Ltac tolist_to_binddt :=
  rewrite tolist_to_traverse1, traverse_to_binddt.

Ltac element_of_to_binddt :=
  rewrite element_of_to_foldMap, foldMap_to_traverse1, traverse_to_binddt.

Ltac in_to_binddt :=
  rewrite in_to_foldMap, foldMap_to_traverse1, traverse_to_binddt.

Ltac ind_to_binddt :=
  rewrite ind_to_foldMapd, foldMapd_to_mapdt1, mapdt_to_binddt.

Lemma pure_const_rw: forall {A} {a:A} {M} {unit:Monoid_unit M},
    pure (F := const M) (Pure := @Pure_const _ unit) a = Ƶ.
  reflexivity.
Qed.

Lemma ap_const_rw: forall {M} `{Monoid_op M} {A B} (x: const M (A -> B)) (y: const M A),
    ap (const M) x y = (x ● y).
  reflexivity.
Qed.

Lemma map_const_rw: forall A B (f: A -> B) X,
    map (F := const X) f = @id X.
Proof.
  reflexivity.
Qed.

Lemma free_loc_Bd: forall b,
    free_loc (Bd b) = [].
Proof.
  reflexivity.
Qed.

Lemma free_loc_Fr: forall x,
    free_loc (Fr x) = [x].
Proof.
  reflexivity.
Qed.

Lemma free_to_foldMap: forall t,
    free t = foldMap free_loc t.
Proof.
  reflexivity.
Qed.

Ltac rewrite_ops_to_binddt :=
  match goal with
  | |- context[?x ∈ ?t] =>
      debug "in_to_binddt";
      in_to_binddt
  | |- context[(?n, ?l) ∈d ?t] =>
      debug "ind_to_binddt";
      ind_to_binddt
  | |- context[tolist ?t] =>
      debug "tolist_to_binddt";
      tolist_to_binddt
  | |- context[element_of ?t] =>
      debug "element_of_to_binddt";
      element_of_to_binddt
  | |- context[foldMap ?t] =>
      debug "foldMap_to_binddt";
      rewrite foldMap_to_traverse1, traverse_to_binddt
  | |- context[foldMapd ?t] =>
      debug "foldMap_to_binddt";
      rewrite foldMapd_to_mapdt1, mapdt_to_binddt
  | |- context[Forall_ctx ?P] =>
      debug "Forall_to_foldMapd";
      unfold Forall_ctx
  end.

Ltac simplify_monoid_units :=
  match goal with
  | |- context[Ƶ ● ?m] =>
      debug "monoid_id_r";
      rewrite (monoid_id_r m)
  | |- context[?m ● Ƶ] =>
      debug "monoid_id_l";
      rewrite (monoid_id_l m)
  end.

Ltac simplify_const_functor :=
  match goal with
  | |- context [pure (F := const ?W) ?x] =>
      debug "pure_const";
      rewrite pure_const_rw
  | |- context[(ap (const ?W) ?x ?y)] =>
      debug "ap_const";
      rewrite ap_const_rw
  | |- context[map (F := const ?X) ?f] =>
      debug "map_const";
      rewrite map_const_rw

  end.

Ltac simplify_I_functor :=
  match goal with
  | |- context[pure (F := fun A => A) ?x] =>
      debug "pure_I";
      change (pure (F := fun A => A) x) with x
  | |- context[ap (fun A => A) ?x ?y] =>
      debug "ap_I";
      change (ap (fun A => A) x y) with (x y)
  end.

Ltac simplify_extract :=
  match goal with
  | |- context[(?f ∘ extract) ⦿ ?w] =>
      debug "extract_preincr2";
      rewrite extract_preincr2
  | |- context[(?f ∘ extract) (?w, ?a)] =>
      debug "extract_pair";
      change ((f ∘ extract) (w, a)) with
      ((f ∘ (extract ∘ pair w)) a);
      rewrite extract_pair
  end.

Ltac simplify_fn_composition :=
  match goal with
  | |- context [id ∘ ?f] =>
      debug "id ∘ f";
      change (id ∘ f) with f
  | |- context [?f ∘ id] =>
      debug "f ∘ id";
      change (f ∘ id) with f
  end.

Ltac simplify_distribute_list_ops :=
  match goal with
  | |- context[?f (monoid_op (Monoid_op := Monoid_op_list) ?l1 ?l2)] =>
      unfold_ops @Monoid_op_list;
      progress (autorewrite with tea_list)
  | |- context[?f (monoid_op (Monoid_op := Monoid_op_subset) ?l1 ?l2)] =>
      unfold_ops @Monoid_op_subset;
      progress (autorewrite with tea_set)
  end.

Ltac simplify_locally_nameless_top_level :=
  match goal with
  | |- context[free ?t] =>
      debug "free_to_foldMap";
      rewrite free_to_foldMap
  | |- context[freeset ?t] =>
      debug "unfold_freeset";
      unfold freeset;
      rewrite free_to_foldMap
  | |- context[locally_closed] =>
      idtac "locally_closed_spec";
      rewrite locally_closed_spec
  | |- context[locally_closed_gap] =>
      idtac "locally_closed_gap_spec";
      rewrite locally_closed_gap_spec
  | |- context[is_bound_or_free] =>
      debug "simplify_bound_or_free";
      simplify_is_bound_or_free
  end.

Ltac simplify_locally_nameless_leaves :=
  match goal with
  | |- context[free_loc (Fr ?x)] =>
      rewrite free_loc_Fr
  | |- context[free_loc (Bd ?b)] =>
      rewrite free_loc_Bd
  | |- context[?x ∈ [?y]] =>
      rewrite in_list_one
  | |- context[Forall_ctx ?P] =>
      unfold Forall_ctx
  | |- context[is_bound_or_free] =>
      simplify_is_bound_or_free
  end.

Ltac simplify_misc :=
  match goal with
  | |- context[(?a, ?b) = (?c, ?d)] =>
      (* This form occurs when reasoning about ∈d at <<ret>> *)
      rewrite pair_equal_spec
  end.

Ltac simplify2 :=
  first [ step_binddt_term
        | simplify_locally_nameless_top_level
        | simplify_locally_nameless_leaves
        | rewrite_ops_to_binddt
        | simplify_const_functor
        | simplify_monoid_units
        (* ^ monoid_units should be after const_functor,
           before distribute_list_ops *)
        | simplify_I_functor
        | simplify_fn_composition
        | simplify_extract
        | simplify_distribute_list_ops
        | simplify_misc
    ].

Ltac handle_atoms :=
  match goal with
  | |- context[atoms] =>
      progress (autorewrite with tea_rw_atoms)
  | |- context[atoms (?l1 ● ?l2)] =>
      unfold_ops @Monoid_op_list;
      progress (autorewrite with tea_rw_atoms)
  end.

Ltac derive :=
  intros;
  repeat simplify2;
  try handle_atoms;
  (trivial || reflexivity || easy).

(* I don't entirely know why this is required. *)
#[local] Typeclasses Transparent Monoid_op.
#[local] Typeclasses Transparent Monoid_unit.

Lemma test_transparency:
  @Applicative (@const Type Type Prop)
    (@Map_const Prop)
    (@Pure_const Prop False)
    (@Mult_const Prop or).
Proof.
  typeclasses eauto.
Qed.

(** ** Rewriting lemmas for <<tolist>>, <<toset>>, <<∈>> *)
(******************************************************************************)
Section term_container_rewrite.

  Variable
    (A : Type).

  Definition tolist_tvar_rw1: forall (x: A),
      tolist (tvar x) = [x] :=
    ltac:(derive).

  Definition tolist_term_rw2: forall (X: typ) (t: term A),
      tolist (lam X t) = tolist t :=
    ltac:(derive).

  Definition tolist_term_rw3: forall (t1 t2: term A),
      tolist (app t1 t2) = tolist t1 ++ tolist t2 :=
    ltac:(derive).

  Open Scope tealeaves_scope.

  Definition toset_tvar_rw1: forall (x: A),
      element_of (tvar x) = {{x}}
    := ltac:(derive).

  Definition toset_term_rw2: forall (X: typ) (t: term A),
      element_of (lam X t) = element_of t
    := ltac:(derive).

  Definition toset_term_rw3: forall (t1 t2: term A),
      element_of (app t1 t2) = element_of t1 ∪ element_of t2
    := ltac:(derive).

  Lemma in_term_rw1: forall (x y: A),
      x ∈ tvar y <-> x = y.
  Proof.
    derive.
  Qed.

  Lemma in_term_rw2: forall (y: A) (X: typ) (t: term A),
    y ∈ (lam X t) <-> y ∈ t.
  Proof.
    derive.
  Qed.

  Lemma in_term_3: forall (t1 t2: term A) (y: A),
      y ∈ (app t1 t2) <-> y ∈ t1 \/ y ∈ t2.
  Proof.
    derive.
  Qed.

End term_container_rewrite.

(** ** Rewriting lemmas for <<free>>, <<freeset>> *)
(******************************************************************************)
Section term_free_rewrite.

  Variable (A : Type).

  Definition term_free11 : forall (b : nat),
      free (tvar (Bd b)) = []
    := ltac:(derive).

  Definition term_in_free11 : forall (b : nat) (x : atom),
      x ∈ free (tvar (Bd b)) <-> False
    := ltac:(derive).

  Definition term_free12 : forall (y : atom),
      free (tvar (Fr y)) = [y]
    := ltac:(derive).

  Definition term_in_free12 : forall (y : atom) (x : atom),
      x ∈ free (tvar (Fr y)) <-> x = y
    := ltac:(derive).

  Definition term_free2 : forall (t : term LN) (X : typ),
      free (lam X t) = free t
    := ltac:(derive).

  Definition term_in_free2 : forall (x : atom) (t : term LN) (X : typ),
      x ∈ free (lam X t) <-> x ∈ free t
    := ltac:(derive).

  Definition term_free3 : forall (x : atom) (t1 t2 : term LN),
      free (app t1 t2) = free t1 ++ free t2
    := ltac:(derive).

  Definition term_in_free3 : forall (x : atom) (t1 t2 : term LN),
      x ∈ free (app t1 t2) <-> x ∈ free t1 \/ x ∈ free t2
    := ltac:(derive).

  Definition term_in_freeset11 : forall (b : nat) (x : atom),
      AtomSet.In x (freeset (tvar (Bd b))) <-> False
    := ltac:(derive).

  Definition term_in_freeset12 : forall (y : atom) (x : atom),
      AtomSet.In x (freeset (tvar (Fr y))) <-> x = y.
  Proof.
    derive.
  Qed.

  Lemma term_in_freeset2 : forall (x : atom) (t : term LN) (X : typ),
      AtomSet.In x (freeset (lam X t)) <-> AtomSet.In x (freeset t).
  Proof.
    derive.
  Qed.

  Lemma term_in_freeset3 : forall (x : atom) (t1 t2 : term LN),
      AtomSet.In x (freeset (app t1 t2)) <->
        AtomSet.In x (freeset t1) \/ AtomSet.In x (freeset t2).
  Proof.
    derive.
  Qed.

  Open Scope set_scope.

  Lemma term_freeset11 : forall (b : nat) (x : atom),
      freeset (tvar (Bd b)) [=] ∅.
  Proof.
    intros. fsetdec.
  Qed.

  Lemma term_freeset12 : forall (y : atom),
      freeset (tvar (Fr y)) [=] {{ y }}.
  Proof.
    derive.
  Qed.

  Lemma term_freeset2 : forall (t : term LN) (X : typ),
      freeset (lam X t) [=] freeset t.
  Proof.
    derive.
  Qed.

  Lemma term_freeset3 : forall (t1 t2 : term LN),
      freeset (app t1 t2) [=] freeset t1 ∪ freeset t2.
  Proof.
    derive.
  Qed.

End term_free_rewrite.

(** ** Rewriting lemmas for <<foldMapd>> *)
(******************************************************************************)
Section term_foldMapd_rewrite.

  Context {A M : Type} (f : nat * A -> M) `{Monoid M}.

  Lemma term_foldMapd1 : forall (a : A),
      foldMapd f (tvar a) = f (Ƶ, a).
  Proof.
    derive.
  Qed.

  Lemma term_foldMapd2 : forall X (t : term A),
      foldMapd f (λ X t) = foldMapd (f ⦿ 1) t.
  Proof.
    derive.
  Qed.

  Lemma term_foldMapd3 : forall (t1 t2 : term A),
      foldMapd f ([t1]@[t2]) = foldMapd f t1 ● foldMapd f t2.
  Proof.
    derive.
  Qed.

End term_foldMapd_rewrite.

(** ** Rewriting lemmas for <<∈d>> *)
(******************************************************************************)
Section term_ind_rewrite.

  Lemma term_ind1 : forall (l1 l2 : LN) (n : nat),
      (n, l1) ∈d (tvar l2) <-> n = Ƶ /\ l1 = l2.
  Proof.
    derive.
  Qed.

  Lemma eq_pair_preincr: forall (n: nat) {A} (a: A),
      eq (n, a) = eq (S n, a) ⦿ 1.
  Proof.
    intros.
    ext [n' a'].
    unfold preincr, compose, incr.
    apply propositional_extensionality.
    rewrite pair_equal_spec.
    rewrite pair_equal_spec.
    intuition.
  Qed.

  Lemma term_ind2 : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d t = (S n, l) ∈d (λ X t).
  Proof.
    intros.
    do 2 rewrite ind_to_foldMapd.
    repeat simplify2.
    rewrite eq_pair_preincr.
    reflexivity.
  Qed.

  Lemma term_ind2_nZ : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) -> (n <> 0).
  Proof.
    introv.
    rewrite ind_to_foldMapd.
    repeat simplify2.
    assert (Hgt: 1 > 0) by lia; generalize dependent Hgt.
    generalize 1 as m.
    induction t; intros m Hgt.
    - simplify2.
      unfold preincr, compose, incr; cbn.
      rewrite pair_equal_spec.
      change (?m ● ?x) with (m + x)%nat. lia.
    - repeat simplify2.
      rewrite preincr_preincr.
      intro hyp.
      eapply IHt.
      2: eauto.
      change (?m ● ?x) with (m + x)%nat.
      lia.
    - repeat simplify2.
      intros [hyp|hyp]; eauto.
  Qed.

  Lemma term_ind2_nZ2: forall t n l,
      (@binddt nat term term Binddt_STLC (@const Type Type Prop)
        (@Map_const Prop) (@Pure_const Prop False) (@Mult_const Prop or) LN False
        (eq (n, l) ⦿ 1) t) -> n <> 0.
  Proof.
    introv.
    assert (Hgt: 1 > 0) by lia; generalize dependent Hgt.
    generalize 1 as m.
    induction t; intros m Hgt.
    - simplify2.
      unfold preincr, compose, incr; cbn.
      rewrite pair_equal_spec.
      change (?m ● ?x) with (m + x)%nat.
      lia.
    - repeat simplify2.
      rewrite preincr_preincr.
      intro hyp.
      eapply IHt.
      2: eauto.
      change (?m ● ?x) with (m + x)%nat.
      lia.
    - repeat simplify2.
      intros [hyp|hyp]; eauto.
  Qed.

  (*
  Lemma term_ind2_alt : forall (t : term LN) (l : LN) (n : nat) (X : typ),
      (n, l) ∈d (λ X t) = ((n - 1, l) ∈d t /\ n <> 0).
  Proof.
    intros.
    propext.
    - intro.
      specialize (term_ind2_nZ2 t l H).
      intro. destruct n.
      + false.
      + replace (S n - 1) with n by lia.
        apply term_ind2 in H.
    do 2 rewrite ind_to_foldMapd.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
                  .

    - intro. destruct H as [H H'].
      destruct n.
      + false.
      + rewrite <- eq_pair_preincr.
        replace (S n - 1) with n in H by lia.
        assumption.
  Qed.
  *)

  Lemma term_ind3 : forall (t1 t2 : term LN) (n : nat) (l : LN),
      (n, l) ∈d ([t1]@[t2]) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    derive.
  Qed.

End term_ind_rewrite.

(** ** Rewriting lemmas for <<subst>> *)
(******************************************************************************)

(** ** Rewriting lemmas for <<locally_closed>> *)
(******************************************************************************)
Theorem term_lc_gap11 : forall (n : nat) (m : nat),
    locally_closed_gap m (tvar (Bd n)) <-> n < m.
Proof.
  derive.
Qed.

Theorem term_lc_gap12 : forall (x : atom) (m : nat),
    locally_closed_gap m (tvar (Fr x)) <-> True.
Proof.
  derive.
Qed.

Theorem term_lc_gap2 : forall (X : typ) (t : term LN) (m : nat),
    locally_closed_gap m (lam X t) <-> locally_closed_gap (S m) t.
Proof.
  derive.
Qed.

Theorem term_lc_gap3 : forall (t1 t2 : term LN) (m : nat),
    locally_closed_gap m ([t1]@[t2]) <->
      locally_closed_gap m t1 /\ locally_closed_gap m t2.
Proof.
  derive.
Qed.

Theorem term_lc11 : forall (n : nat),
    locally_closed (tvar (Bd n)) <-> False.
Proof.
  derive.
Qed.

Theorem term_lc12 : forall (x : atom),
    locally_closed (tvar (Fr x)) <-> True.
Proof.
  derive.
Qed.

Theorem term_lc2 : forall (X : typ) (t : term LN),
    locally_closed (lam X t) <-> locally_closed_gap 1 t.
Proof.
  derive.
Qed.

Theorem term_lc3 : forall (t1 t2 : term LN),
    locally_closed ([t1]@[t2]) <-> locally_closed t1 /\ locally_closed t2.
Proof.
  derive.
Qed.
