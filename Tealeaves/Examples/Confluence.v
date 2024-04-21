From Tealeaves Require Export
  Backends.DB.DB
  Examples.Simplification.

About open.

Import DB.Notations.

#[local] Set Implicit Arguments.

Inductive term (V : Type) :=
| tvar : V -> term V
| lam  : term V -> term V
| app  : term V -> term V -> term V.

Module Notations.
  Notation "'λ'" := (lam) (at level 45).
  Notation "⟨ t ⟩ ( u )" := (app t u) (at level 80, t at level 40, u at level 40).
End Notations.

Fixpoint binddt_term (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (term v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar v    => f (0, v)
  | lam body  => pure (@lam v2) <⋆> binddt_term (f ⦿ 1) body
  | app t1 t2 => pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance Return_STLC: Return term := tvar.
#[export] Instance Binddt_STLC: Binddt nat term term := @binddt_term.
#[export] Instance DTM_STLC: DecoratedTraversableMonad nat term.
Proof.
  derive_dtm.
Qed.

#[export] Instance Map_STLC: Map term
  := Map_Binddt nat term term.
#[export] Instance Mapd_STLC: Mapd nat term
  := Mapd_Binddt nat term term.
#[export] Instance Traverse_STLC: Traverse term
  := Traverse_Binddt nat term term.
#[export] Instance Mapdt_STLC: Mapdt nat term
  := Mapdt_Binddt nat term term.
#[export] Instance Bind_STLC: Bind term term
  := Bind_Binddt nat term term.
#[export] Instance Bindd_STLC: Bindd nat term term
  := Bindd_Binddt nat term term.
#[export] Instance Bindt_STLC: Bindt term term
  := Bindt_Binddt nat term term.
#[export] Instance ToSubset_STLC: ToSubset term
  := ToSubset_Traverse.
#[export] Instance ToBatch_STLC: ToBatch term
  := ToBatch_Traverse.

Import Notations.


Print subst.
About local__sub.
Ltac refold_subst :=
  repeat match goal with
  | |- context[bindd (local__sub ?σ) ?t] =>
      repeat progress (change (bind (local__sub σ) t) with (subst σ t))
    end.

Ltac fold_rename :=
  repeat rewrite rename_to_subst.

Ltac simplify_subst_loc :=
  rewrite ?local__sub_preincr.
  (*
  rewrite ?subst_loc_neq, ?subst_loc_b,
    ?subst_loc_fr_neq by auto.
   *)

Ltac simplify_subst :=
  debug "simplify_db_subst|start";
  unfold subst;
  autounfold with tea_ret_coercions;
  simplify_bindd;
  fold_rename;
  debug "simplify_db_subst|local";
  simplify_subst_loc;
  refold_subst;
  debug "simplify_db_subst|end".

Section test_notations.
  Check λ (tvar 0).
  Check ⟨λ (tvar 0) ⟩(λ (tvar 1)).

  Variable (σ: nat -> term nat).

  Check DB.subst (T := term) σ (⟨λ (tvar 0) ⟩(λ (tvar 1))).
  Eval cbn in subst (T := term) σ (⟨λ (tvar 0) ⟩(λ (tvar 1))).

  Goal subst σ (⟨λ (tvar 0) ⟩(λ (tvar 1))) = tvar 0.
    unfold subst.
    simplify_bindd.
    fold_rename.
    rewrite bindd_to_binddt.
    cbn.
    simplify_binddt_core.

    simplify_subst.
End test_notations.
