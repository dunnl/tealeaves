From Tealeaves Require Export
  Backends.DB.DB
  Simplification.Support
  Simplification.Binddt
  Simplification.Tests.Support.

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


Ltac simplify_db :=
  rewrite
    ?subst_compose_ret_assoc,
    ?subst_compose_ret,
    ?subst_ret,
    ?subst_id.

