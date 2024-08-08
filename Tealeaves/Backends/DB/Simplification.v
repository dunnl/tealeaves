From Tealeaves Require Export
  Backends.DB.DB
  Simplification.Support
  Simplification.Binddt
  Simplification.Tests.Support.

#[local] Generalizable Variables T U.

Import DB.Notations.

(** * Extra lemmas *)
(******************************************************************************)
Section db_simplification_lemmas.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Mapd_T_inst : Mapd nat T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Mapdt_T_inst : Mapdt nat T}
      `{Bindd_T_inst : Bindd nat T T}
      `{Bindt_T_inst : Bindt T T}
      `{Binddt_T_inst : Binddt nat T T}
      `{! Compat_Map_Binddt nat T T}
      `{! Compat_Mapd_Binddt nat T T}
      `{! Compat_Traverse_Binddt nat T T}
      `{! Compat_Bind_Binddt nat T T}
      `{! Compat_Mapdt_Binddt nat T T}
      `{! Compat_Bindd_Binddt nat T T}
      `{! Compat_Bindt_Binddt nat T T}
      `{Monad_inst : ! DecoratedTraversableMonad nat T}.

  Context
    `{Map_U_inst : Map U}
      `{Mapd_U_inst : Mapd nat U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Mapdt_U_inst : Mapdt nat U}
      `{Bindd_U_inst : Bindd nat T U}
      `{Bindt_U_inst : Bindt T U}
      `{Binddt_U_inst : Binddt nat T U}
      `{! Compat_Map_Binddt nat T U}
      `{! Compat_Mapd_Binddt nat T U}
      `{! Compat_Traverse_Binddt nat T U}
      `{! Compat_Bind_Binddt nat T U}
      `{! Compat_Mapdt_Binddt nat T U}
      `{! Compat_Bindd_Binddt nat T U}
      `{! Compat_Bindt_Binddt nat T U}
      `{Module_inst : ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.

  Lemma subst_id_Applied: forall t,
      subst (@ret T _ nat) t = t.
  Proof.
    now rewrite subst_id.
  Qed.

  (* used for simpl_db *)
  Lemma subst_compose_ret_assoc {X: Type}: forall (f: T nat -> X) σ,
    (f ∘ subst σ) ∘ ret = f ∘ σ.
  Proof.
    intros.
    change_left (f ∘ (subst σ ∘ ret)).
    rewrite subst_compose_ret.
    reflexivity.
  Qed.

  (* Autosubst: subst_compR *)
  Lemma subst_subst_R {X}: forall (f: U nat -> X) (σ2 σ1: nat -> T nat),
      (f ∘ subst σ2) ∘ subst σ1 = f ∘ subst (T := T) (subst σ2 ∘ σ1).
  Proof.
    intros.
    reassociate -> on left.
    rewrite subst_subst.
    reflexivity.
  Qed.

  (* Autosubst: subst_compI *)
  Lemma subst_subst_applied: forall (σ2 σ1: nat -> T nat) (t: U nat),
      subst σ2 (subst σ1 t) = subst (T := T) (subst σ2 ∘ σ1) t.
  Proof.
    intros.
    compose near t on left.
    rewrite subst_subst.
    reflexivity.
  Qed.

End db_simplification_lemmas.

(** * Unfolding up *)
(******************************************************************************)

Ltac unfold_up :=
  rewrite ?up__sub_unfold;
  (* up__sub σ = ret 0 ⋅ (subst (ret ∘ (+1)) ∘ σ). *)
  unfold up__ren.

(** * Simplifying renaming via unfolding *)
(******************************************************************************)
Lemma local__ren_zero_comp_alt {X Y Z: Type} {f: nat * X -> Y} {g: Y -> Z} {n}:
  (g ∘ f) (0, n) = g (f (0, n)).
  reflexivity.
Qed.

Lemma local__ren_zero_comp {X:Type} {f: nat -> X} {ρ n}:
    (f ∘ local__ren ρ) (0, n) = f (ρ n).
Proof.
  unfold compose.
  intros.
  rewrite local__ren_zero.
  conclude.
Qed.

Ltac rw_local__ren :=
  rewrite ?local__ren_zero, ?local__ren_zero_comp, ?local__ren_zero_comp_alt,
    ?local__sub_zero.

Ltac rw_db_local :=
  unfold_ops @Monoid_op_plus @Monoid_unit_zero;
  repeat rw_local__ren;
  normalize_all_ret.

Lemma rename_to_mapd {T} `{Mapd nat T}: forall (ρ: nat -> nat),
    rename ρ = mapd (local__ren ρ).
Proof.
  reflexivity.
Qed.

Ltac simplify_rename :=
  rewrite ?rename_to_mapd;
  simplify_mapd;
  rewrite ?local__ren_preincr_1;
  rewrite <- ?rename_to_mapd;
  rw_db_local.

(** * Simplifying substitution via unfolding *)
(******************************************************************************)
Ltac tealeaves_unfold :=
  rewrite ?rename_to_subst.

Lemma subst_to_bindd {T U} `{Return T} `{Mapd nat T} `{Bindd nat T U}: forall (σ: nat -> T nat),
    subst (T := T) (U := U) σ = bindd (local__sub σ).
Proof.
  reflexivity.
Qed.

(* Simplify by unfolding *)
Ltac simplify_subst :=
  rewrite ?subst_to_bindd;
  simplify_bindd;
  rewrite ?local__sub_preincr_1;
  rewrite <- ?subst_to_bindd;
  rw_db_local.

(** * Simplifying substitution a la Autosubst *)
(******************************************************************************)
Ltac simplify_subst_id :=
  rewrite
    ?subst_id_Applied,
    ?subst_id.


Ltac simplify_subst_ret :=
  rewrite
    ?subst_ret,
    ?subst_compose_ret,
    ?subst_compose_ret_assoc.

Ltac simplify_subst_subst :=
  rewrite
    ?subst_subst_applied,
    ?subst_subst_R,
    ?subst_subst.

Ltac normalize_rename_to_subst :=
  rewrite ?rename_to_subst.

Ltac normalize_rename_to_subst_in_all :=
  rewrite ?rename_to_subst in *.

(* unfold some operations to reduce the number that must be considered *)
Ltac simplify_db_unfold_phase :=
  unfold_up;
  normalize_rename_to_subst.

Ltac simplify_db_end_phase :=
  idtac.

Ltac simplify_db_core_phase :=
  simplify_subst_id;
  simplify_subst_ret;
  simplify_subst_subst;
  try simplify_subst;
  rewrite ?cons_compose.

Ltac simplify_db :=
  simplify_db_unfold_phase;
  repeat (progress simplify_db_core_phase);
  simplify_db_end_phase.

Ltac simplify_like_autosubst_core :=
  progress
    rewrite
    ?subst_compose_ret,
    ?subst_id,
    ?subst_subst,
    ?subst_compose_ret_assoc,
    ?subst_subst_applied,
    ?subst_ret,
    ?subst_id_Applied.

Ltac normalize_functions :=
  ltac_trace "normalize_functions";
  match goal with
  | |- context[?f ∘ id] =>
      change (f ∘ id) with f
  | |- context[(id ∘ ?f)] =>
      change (id ∘ f) with f
  | |- context[(?f ∘ (?g ∘ ?h))] =>
      change (f ∘ (g ∘ h)) with (f ∘ g ∘ h)
  end.

Lemma cons_compose_S {X}: forall (x: X) (σ: nat -> X) (n: nat),
    (x ⋅ σ) ∘ (+ (S n)) = σ ∘ (+n).
Proof.
  reflexivity.
Qed.

Ltac simplify_cons :=
  match goal with
  | |- context[(?x ⋅ ?σ) ∘ (+ (S ?n))] =>
     rewrite (cons_compose_S x σ n)
  | |- context[?x ⋅ (?σ ∘ (+ (S ?n)))] =>
      change x with (σ n);
      rewrite (cons_eta σ n)
  | _ => progress (rewrite ?cons_compose, ?lift_eta)
  end.

Ltac factor_out_ret :=
  repeat match goal with
    | |- context[((ret (T := ?T) (A := ?A) ∘ ?f) ∘ ?g)]=>
        change ((ret (T := T) (A := A) ∘ f) ∘ g)
        with (ret (T := T) (A := A) ∘ (f ∘ g))
    end;
  rewrite <- ?cons_compose.

Ltac simplify_db_like_autosubst :=
  repeat (progress simplify_subst); (* in place of cbn *)
  simplify_db_unfold_phase;
  repeat (first
            [ simplify_like_autosubst_core
            | simplify_cons
            | simplify_lift
            | normalize_functions
    ]);
  factor_out_ret;
  simplify_db_end_phase.

