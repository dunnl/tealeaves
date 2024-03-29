From Tealeaves Require Import
  Backends.DB.DB
  Theory.DecoratedTraversableMonad.

From Autosubst Require Import
  Autosubst.

Export Kleisli.DecoratedTraversableMonad.Notations. (* ∈d *)
Import Monoid.Notations. (* Ƶ and ● *)
Import Misc.Subset.Notations. (* ∪ *)
Export Applicative.Notations. (* <⋆> *)
Export List.ListNotations. (* [] :: *)
Export LN.AtomSet.Notations.
Export LN.AssocList.Notations. (* one, ~ *)
Export Product.Notations. (* × *)
Export ContainerFunctor.Notations. (* ∈ *)
Export DecoratedContainerFunctor.Notations. (* ∈d *)

Set Implicit Arguments.

(** ** Autosubst *)
(******************************************************************************)
Section Autosubst.

  Inductive term (var : Type) : Type :=
  | tvar (x : var)
  | app (s t : term var)
  | lam (s : {bind (term var)}).

  #[export] Instance Ids_term : Ids (term var). derive. Defined.
  #[export] Instance Rename_term : Rename (term var). derive. Defined.
  #[export] Instance Subst_term : Subst (term var). derive. Defined.

End Autosubst.

Fixpoint binddt_term (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (term v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar v => f (0, v)
  | lam body => pure (@lam _) <⋆> binddt_term (preincr f 1) body
  | app t1 t2 => pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance Return_Term: Return term := tvar.
#[export] Instance Binddt_Term: Binddt nat term term := @binddt_term.

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

#[export] Instance DTMFull_Term:
  DecoratedTraversableMonadFull nat term.
Admitted.

Implicit Types (ρ: nat -> nat) (σ: nat -> term nat).

Ltac lia' :=
  repeat
  match goal with
  | |- context[(?ix + 0)%nat] =>
      replace (ix + 0)%nat with ix by lia
  | |- context[(?ix - 0)%nat] =>
      replace (ix - 0)%nat with ix by lia
  | |- context[(?ix - ?m + ?m)%nat] => (* applies if ix > m in context *)
      replace (ix - m + m)%nat with ix by lia
  end;
  try solve lia.

Lemma upren_spec: forall ρ,
    upren ρ = scoot_ren 1 ρ.
Proof.
  intros.
  ext ix.
  destruct ix.
  - unfold scoot_ren. bound_induction.
  - cbn.
    replace (ix - 0) with ix by lia.
    lia.
Qed.

Lemma Autosubst_rename_spec: forall (ρ: nat -> nat),
    rename ρ =
      DB.rename ρ.
Proof.
  intros. ext t.
  generalize dependent ρ.
  unfold DB.rename.
  induction t; intro ρ.
  - cbn; unfold compose.
    unfold rename_loc.
    now rewrite scoot_ren_zero.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - cbn.
    fequal.
    change ((?f ∘ ?g) ⦿ ?n) with
      (f ∘ (g ⦿ n)).
    rewrite <- mapd_to_binddt.
    rewrite rename_loc_preincr.
    rewrite IHt.
    rewrite upren_spec.
    reflexivity.
Qed.

Import Coq.Init.Nat. (* Nat notations *)

Lemma up_spec: forall (σ: nat -> term nat),
    up σ = scoot 1 σ.
Proof.
  intros σ. ext n.
  unfold up.
  rewrite Autosubst_rename_spec.
  unfold funcomp, scons, scoot, bound_in.
  change (ids 0) with (ret 0).
  remember (n <? 1) as b.
  symmetry in Heqb.
  destruct b.
  - destruct n. easy. false.
  - destruct n. easy.
    cbn. lia'. unfold DB.rename.
    fequal. ext [depth ix].
    cbn. unfold scoot_ren.
    + bound_induction.
      cbn. lia'.
      destruct depth. lia.
      cbn in *.
      rewrite Hbound. lia.
      destruct depth.
      lia. cbn in Hbound.
      rewrite Hbound.
      reflexivity.
Qed.

Lemma Tealeaves_Matches_Autosubst:
  forall (t : term nat) (σ : nat -> term nat),
    DB.open σ t = subst σ t.
Proof.
  intros. generalize dependent σ. induction t; intros σ.
  - cbn. lia'.
    rewrite DB.lift_zero.
    rewrite dfun_mapd1.
    reflexivity.
  - cbn. fequal; eauto.
  - cbn. fequal.
    rewrite <- IHt.
    unfold open.
    rewrite open_loc_preincr.
    rewrite up_spec.
    reflexivity.
Qed.
