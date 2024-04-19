From Tealeaves Require Export
  Examples.Simplification.Support
  Theory.DecoratedTraversableMonad.

Import
  List.ListNotations
  Product.Notations
  Monoid.Notations
  ContainerFunctor.Notations
  Subset.Notations.

(** * Rewriting with binddt *)
(******************************************************************************)
Module ToBinddt.

  Ltac rewrite_core_ops_to_binddt :=
    match goal with
    | |- context[map ?f ?t] =>
        debug "map_to_binddt";
        progress (rewrite bind_to_binddt)
    (* mapd/bind/traverse *)
    | |- context[bind ?f ?t] =>
        debug "bind_to_binddt";
        progress (rewrite bind_to_binddt)
    | |- context[mapd ?f ?t] =>
        debug "mapd_to_binddt";
        progress (rewrite mapd_to_binddt)
    | |- context[traverse ?f ?t] =>
        debug "traverse_to_binddt";
        progress (rewrite traverse_to_binddt)
    (* mapdt/bindd/bindt *)
    | |- context[mapdt ?f ?t] =>
        debug "mapdt_to_binddt";
        progress (rewrite mapdt_to_binddt)
    | |- context[bindd ?f ?t] =>
        debug "bindd_to_binddt";
        progress (rewrite bindd_to_binddt)
    | |- context[bindt ?f ?t] =>
        debug "bindt_to_binddt";
        progress (rewrite bindt_to_binddt)
    end.

  Ltac rewrite_binddt_to_core_ops :=
    match goal with
    | |- context[binddt (G := fun A => A) (ret ∘ ?f ∘ extract)] =>
        debug "binddt_to_map";
        progress (rewrite <- map_to_binddt)
    | |- context[binddt (G := fun A => A) (ret (T := ?T) (A := ?A) ∘ extract)] =>
        change (ret (T := T) (A := A)) with (ret (T := T) (A := A) ∘ id);
        debug "binddt_to_map";
        progress (rewrite <- map_to_binddt)
    | |- context[binddt (G := fun A => A) (?f ∘ extract)] =>
        debug "binddt_to_bind";
        progress (rewrite <- bind_to_binddt)
    | |- context[binddt (G := fun A => A) (ret ∘ ?f)] =>
        debug "binddt_to_mapd";
        progress (rewrite <- mapd_to_binddt)
    | |- context[binddt (G := fun A => A)] =>
        debug "binddt_to_bindd";
        progress (rewrite <- bindd_to_binddt)
    | |- context[binddt (G := ?G) (map (F := ?G) ret ∘ ?f ∘ extract)] =>
        debug "binddt_to_traverse";
        progress (rewrite <- traverse_to_binddt)
    | |- context[binddt (G := ?G) (map (F := ?G) ret ∘ ?f)] =>
        debug "binddt_to_mapdt";
        progress (rewrite <- mapdt_to_binddt)
    | |- context[binddt (G := ?G) (?f ∘ extract)] =>
        debug "binddt_to_bindt";
        progress (rewrite <- bindt_to_binddt)
    end.

  Ltac rewrite_derived_ops_to_binddt T :=
    match goal with
    (* tolist *)
    | |- context[tolist (F := T) ?t] =>
        debug "tolist_to_binddt";
        rewrite (tolist_to_binddt (T := T))
    (* elements *)
    | |- context[element_of (F := T) ?x ?t] =>
        debug "element_of_to_binddt";
        rewrite (element_of_to_binddt (T := T))
    | |- context[element_ctx_of (T := T) (?n, ?l) ?t] =>
        debug "element_ctx_of_to_binddt";
        rewrite (element_ctx_of_to_binddt (T := T))
    (* tosubset *)
    | |- context[tosubset (F := T) ?t] =>
        debug "tosubset_to_binddt";
        rewrite (tosubset_to_binddt (T := T))
    | |- context[toctxset (F := T) ?t] =>
        debug "toctxset_to_binddt";
        rewrite (toctxset_to_binddt (T := T))
    (* foldMap *)
    | |- context[foldMap (T := T) ?t] =>
        debug "foldMap_to_binddt";
        rewrite foldMap_to_traverse1, traverse_to_binddt
    | |- context[foldMapd (T := T) ?t] =>
        debug "foldMap_to_binddt";
        rewrite (foldMapd_to_mapdt1 (T := T)),
          (mapdt_to_binddt (T := T))
    (* quantifiers *)
    | |- context[Forall_ctx (T := T)  ?P] =>
        debug "Forall_to_foldMapd";
        unfold Forall_ctx
    end.

End ToBinddt.

(** * Rewriting support lemmas *)
(******************************************************************************)
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

(*
Ltac simplify_binddt :=
   (simplify_binddt_ret
    (* || cbn; repeat push_preincr_into_fn *)
    || simplify_binddt_core;
    repeat push_preincr_into_fn).
 *)

(* simplify binddt but handle ret case with DTM law *)
Ltac simplify_binddt :=
   (simplify_binddt_ret
    || simplify_binddt_core;
    repeat push_preincr_into_fn).

(* simplify binddt and don't handle ret case differently
 (use during proof of DTM laws) *)
Ltac simplify_binddt_raw :=
  (simplify_binddt_core; repeat push_preincr_into_fn).

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
