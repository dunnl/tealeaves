From Tealeaves.Backends.DB Require Import
  DB.

Import PeanoNat.Nat.
Import Coq.Init.Nat.
Open Scope nat_scope.

#[local] Generalizable Variables W T U.

(** * Operations with policy *)
(******************************************************************************)
Definition map_with_policy `{Mapd nat T}
  (policy : (nat -> nat) -> (nat -> nat)) (ρ : nat -> nat): T nat -> T nat :=
  mapd (fun '(depth, ix) => iterate depth policy ρ ix).

Definition bind_with_policy `{Bindd nat T U}
  (policy : (nat -> T nat) -> (nat -> T nat)) (σ : nat -> T nat): U nat -> U nat :=
  bindd (fun '(depth, ix) => iterate depth policy σ ix).

(* Given a depth and local substitution σ,
       adjust σ to account for the depth
       - σ should be a top-level map, e.g.
         σ 0 is the replacement for the first free variable
         σ 1 is the replacement for the second free variable
         ...
 *)

Section alt_presentation.

  Context
    `{ret_inst : Return T}
      `{Mapd_T_inst : Mapd nat T}
      `{Mapd_U_inst : Mapd nat U}
      `{Bindd_U_inst : Bindd nat T U}
      `{ToCtxset_U_inst : ToCtxset nat U}.

  Definition cons {X : Type} : X -> (nat -> X) -> (nat -> X)  :=
    fun new sub n => match n with
                  | O => new
                  | S n' => sub n'
                  end.

  Definition uparrow: nat -> nat := S.

  (* adjust a renaming to go under one binder *)
  Definition up__ren (ρ: nat -> nat): nat -> nat :=
    cons 0 (S ∘ ρ).

  Definition rename_alt: forall (ρ : nat -> nat), T nat -> T nat :=
    map_with_policy up__ren.

  (* adjust a substitution to go under one binder *)
  Definition up__sub (σ: nat -> T nat): nat -> T nat :=
    cons (ret 0) (rename_alt S ∘ σ).

  Definition subst_alt (σ : nat -> T nat): U nat -> U nat :=
    bind_with_policy (T := T) (U := U) up__sub σ.

End alt_presentation.

#[local] Notation "↑" := uparrow.
#[local] Notation "'⇑'" := up__sub.
#[local] Notation "'⇑__ren'" := up__ren.
#[local] Notation "f ';' g" := (kc1 g f) (at level 30).
#[local] Infix "⋅" := (cons) (at level 10).

(** ** Properties of cons *)
(******************************************************************************)
Lemma cons_rw0 {A}: forall `(x: A) σ, (x ⋅ σ) 0 = x.
Proof.
  reflexivity.
Qed.

Lemma cons_rw1 {A}: forall `(x: A) (n: nat) σ, (x ⋅ σ) (S n) = σ n.
Proof.
  reflexivity.
Qed.

Lemma cons_sub_id {X}: forall (σ: nat -> X),
    (σ 0) ⋅ (σ ∘ S) = σ.
Proof.
  intros.
  ext ix.
  destruct ix.
  - rewrite cons_rw0.
    reflexivity.
  - rewrite cons_rw1.
    reflexivity.
Qed.

Lemma scons_sub_id {X}: forall (σ: nat -> T nat),
    (x ⋅ σ) ∘ rename S = σ.
Proof.
  intros.
  ext ix.
  destruct ix.
  - rewrite scons_rw0.
    reflexivity.
  - rewrite scons_rw1.
    reflexivity.
Qed.

(** ** Relating <<up__ren>> to <<liftRenaming>> *)
(******************************************************************************)
Lemma lift__ren_1:
  lift__ren 1 = up__ren.
Proof.
  intros. ext ρ ix.
  unfold lift__ren.
  unfold up__ren.
  bound_induction.
  - cbn. destruct ix.
    + false.
    + cbn. unfold compose.
      rewrite add_1_r.
      do 2 fequal. lia.
  - apply bound_in_1 in Hbound.
    subst. reflexivity.
Qed.

Lemma liftRenaming_policy_repr: forall depth,
    lift__ren depth = iterate depth up__ren.
Proof.
  intros. induction depth.
  - ext ρ ix. cbn.
    rewrite add_0_r.
    fequal; lia.
  - ext ρ ix.
    rewrite iterate_rw1'.
    rewrite lift__ren_S.
    rewrite IHdepth.
    rewrite lift__ren_1.
    reflexivity.
Qed.

Corollary local__ren_policy_repr: forall ρ depth ix,
    local__ren ρ (depth, ix) = iterate depth up__ren ρ ix.
Proof.
  intros. cbn.
  rewrite liftRenaming_policy_repr.
  reflexivity.
Qed.

Section equiv.

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
      `{Monad_inst : ! DecoratedTraversableMonad nat T}
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
                        (unit := Monoid_unit_zero) }.

  Lemma rename_policy_repr (ρ : nat -> nat):
    rename (T := T) ρ = rename_alt ρ.
  Proof.
    unfold rename, rename_alt.
    unfold map_with_policy.
    fequal. ext [depth ix].
    apply local__ren_policy_repr.
  Qed.

  Lemma up_spec:
    lift__sub 1 = up__sub.
  Proof.
    ext σ ix.
    unfold up__sub.
    unfold lift__sub.
    bound_induction.
    - apply bound_in_ge_iff in Hbound.
      assert (Hgt1: exists ix', ix = S ix').
      { destruct ix. false; lia. eauto. }
      destruct Hgt1 as [ix' Heq]; subst.
      rewrite cons_rw1; unfold compose at 1.
      replace (S ix' - 1) with ix' by lia.
      rewrite <- rename_policy_repr.
      fequal. ext n. lia.
    - apply bound_in_1 in Hbound.
      now subst.
  Qed.

  Lemma local__sub_policy_repr: forall depth ix σ,
      local__sub σ (depth, ix) = iterate depth up__sub σ ix.
  Proof.
    intros.
    unfold local__sub.
    rewrite lift__sub_iter.
    fequal.
    apply up_spec.
  Qed.

  Lemma subst_policy_repr (σ : nat -> T nat):
    subst σ = subst_alt σ.
  Proof.
    unfold subst, subst_alt.
    unfold bind_with_policy.
    fequal.
    ext [depth ix].
    rewrite local__sub_policy_repr.
    reflexivity.
  Qed.

End equiv.

From Autosubst Require Autosubst.

Module DTM_Autosubst_Instances.

  Import Autosubst.

  Section DTM_to_Autosubst.

    Context
      `{DecoratedTraversableMonadFull
          (op := Monoid_op_plus) (unit := Monoid_unit_zero) nat T}.

    #[export] Instance Ids_DTM: Ids (T var) :=
      @ret T _ var.
    #[export] Instance Rename_DTM: Rename (T var) :=
      @DB2.rename_alt T _.
    #[export] Instance Subst_DTM : Subst (T var) :=
      @DB2.subst_alt T _ _ _ _.
    #[export] Instance SubstLemmas_term: SubstLemmas (T var).
    Proof.
      constructor.
      - intros.
        unfold_ops @Rename_DTM @Subst_DTM.
        rewrite <- rename_policy_repr.
        rewrite <- subst_policy_repr.
        rewrite (rename_to_subst xi).
        reflexivity.
      - intros.
        unfold_ops @Ids_DTM @Subst_DTM.
        rewrite <- subst_policy_repr.
        rewrite DB.subst_id.
        reflexivity.
      - intros.
        unfold_ops @Ids_DTM @Subst_DTM.
        rewrite <- subst_policy_repr.
        rewrite subst_ret.
        reflexivity.
      - intros.
        unfold_ops @Subst_DTM.
        compose near s on left.
        do 2 rewrite <- subst_policy_repr.
        rewrite subst_subst.
        unfold scomp, funcomp, subst.
        do 2 rewrite <- subst_policy_repr.
        reflexivity.
    Qed.

  End DTM_to_Autosubst.

  Lemma cons_eq {X:Type}:
    @cons X = scons.
  Proof.
    reflexivity.
  Qed.

  Lemma upren_eq {X:Type}:
    up__ren = upren.
  Proof.
    reflexivity.
  Qed.

  Lemma up_eq `{Return T} `{Mapd nat T} {X:Type}:
    up__sub (T := T) = up.
  Proof.
    ext σ ix.
    unfold up.
    destruct ix.
    - asimpl. reflexivity.
    - asimpl. reflexivity.
  Qed.

End DTM_Autosubst_Instances.


Section DTM_to_Autosubst_rw_lemmas.

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
      `{Monad_inst : ! DecoratedTraversableMonad nat T}
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
                        (unit := Monoid_unit_zero) }.



  Declare Scope subst_scope.
  Delimit Scope subst_scope with subst.
  Open Scope subst_scope.

  Definition ren {A B} (f: A -> B) := ret (T := T) ∘ f.
  (*
  Reserved Notation "sigma >> tau" (at level 56, left associativity).
  Notation "f >>> g" := (funcomp f g)
                          (at level 56, left associativity) : subst_scope.
   *)

  (* plus with different simplification behaviour *)
  Definition lift (x y : nat) : nat := plus x y.
  Arguments lift x y/.
  Notation "( + x )" := (lift x) (format "( + x )").

  Notation "s .: sigma" :=
    (cons s sigma)
      (at level 55, sigma at level 56, right associativity) : subst_scope.

  Lemma rename_substX xi :
    rename (T := T) xi = subst (T := T) (U := T) (ren xi).
  Proof.
    rewrite rename_to_subst.
    reflexivity.
  Qed.

  Lemma upX σ : up__sub σ =  ret 0 .: (subst (ren (+1)) ∘ σ).
  Proof.
    unfold up__sub.
    rewrite <- rename_policy_repr.
    rewrite rename_substX.
    reflexivity.
  Qed.

  Lemma id_scompX σ : subst σ ∘ ret = σ.
  Proof.
    unfold compose.
    ext n.
    rewrite subst_ret.
    reflexivity.
  Qed.

  Lemma id_scompR {A:Type} σ (f : _ -> A) :
    (f ∘ subst σ) ∘ ret = f ∘ σ.
  Proof.
    ext d. unfold compose.
    compose near d.
    rewrite id_scompX.
    reflexivity.
  Qed.

  Lemma subst_idX : subst ret = id.
  Proof.
    rewrite subst_id.
    reflexivity.
  Qed.

  Lemma subst_compI σ tau s :
    s.[σ].[tau] = s.[σ >>> subst tau].
  Proof. apply subst_comp. Qed.

  Lemma subst_compX σ tau :
    subst σ >>> subst tau = subst (σ >>> subst tau).
  Proof. f_ext. apply subst_comp. Qed.

  Lemma subst_compR {A} σ tau (f : _ -> A) :
    subst σ >>> (subst tau >>> f) = subst (σ >>> subst tau) >>> f.
  Proof. now rewrite <- subst_compX. Qed.

  Lemma fold_ren_cons (x : var) (xi : var -> var) :
    ids x .: ren xi = ren (x .: xi).
  Proof. unfold ren. now rewrite scons_comp. Qed.


  Lemma upE σ : up σ = ids 0 .: σ >> ren (+1).
  Proof. apply upX. Qed.

  (* unfold upn *)

  Lemma upnSX n σ :
    upn (S n) σ = ids 0 .: upn n σ >>> subst (ren (+1)).
  Proof.
    unfold iterate; now rewrite upX.
  Qed.

  Lemma upnSE n σ :
    upn (S n) σ = ids 0 .: upn n σ >> ren (+1).
  Proof.
    now rewrite upnSX.
  Qed.

  Lemma upn0 σ : upn 0 σ = σ.
  Proof. reflexivity. Qed.

  (* fold up *)

  Lemma fold_up k σ :
    ids k .: σ >> ren (+S k) = up σ >> ren (+k).
  Proof.
    unfold scomp, ren. rewrite upX; fsimpl; rewrite id_subst, subst_compX; simpl; fsimpl.
    unfold ren. fsimpl. rewrite id_scompX. now fsimpl.
  Qed.

  Lemma fold_up0 σ :
    σ >> ren (+0) = σ.
  Proof.
    unfold scomp, ren. fsimpl. now rewrite subst_idX.
  Qed.

  (* combine up *)

  Lemma fold_up_up σ : up (up σ) = upn 2 σ.
  Proof. reflexivity. Qed.

  Lemma fold_up_upn n σ : up (upn n σ) = upn (S n) σ.
  Proof. reflexivity. Qed.

  Lemma fold_upn_up n σ : upn n (up σ) = upn (S n) σ.
  Proof. now rewrite iterate_Sr. Qed.

End LemmasForSubst.

(*
(** Derived substitution lemmas for heterogeneous substitutions. *)

Section LemmasForHSubst.

Context {inner outer : Type}.

Context {Ids_inner : Ids inner} {Rename_inner : Rename inner}
  {Subst_inner : Subst inner} {SubstLemmas_inner : SubstLemmas inner}.

Context {Ids_outer : Ids outer} {Rename_outer : Rename outer}
  {Subst_outer : Subst outer} {SubstLemmas_outer : SubstLemmas outer}.

Context {HSubst_inner_outer : HSubst inner outer}.
Context {HSubstLemmas_inner_outer : HSubstLemmas inner outer}.
Context {SubstHSubstComp_inner_outer : SubstHSubstComp inner outer}.

Lemma id_hsubstX (σ : var -> inner) : ids >>> hsubst σ = ids.
Proof. f_ext. apply id_hsubst. Qed.

Lemma id_hsubstR {A} (f : _ -> A) (σ : var -> inner) :
  ids >>> (hsubst σ >>> f) = ids >>> f.
Proof. now rewrite <- compA, id_hsubstX. Qed.

Lemma hsubst_idX : hsubst ids = id.
Proof. f_ext. exact hsubst_id. Qed.

Lemma hsubst_compI σ tau s :
  s.|[σ].|[tau] = s.|[σ >>> subst tau].
Proof. apply hsubst_comp. Qed.

Lemma hsubst_compX σ tau :
  hsubst σ >>> hsubst tau = hsubst (σ >>> subst tau).
Proof. f_ext. apply hsubst_comp. Qed.

Lemma hsubst_compR {A} σ tau (f : _ -> A) :
  hsubst σ >>> (hsubst tau >>> f) = hsubst (σ >>> subst tau) >>> f.
Proof. now rewrite <- hsubst_compX. Qed.

Lemma scomp_hcompI σ theta s :
  s.[σ].|[theta] = s.|[theta].[σ >>> hsubst theta].
Proof. apply subst_hsubst_comp. Qed.

Lemma scomp_hcompX σ theta :
  subst σ >>> hsubst theta = hsubst theta >>> subst (σ >>>hsubst theta).
Proof. f_ext. apply subst_hsubst_comp. Qed.

Lemma scomp_hcompR {A} σ theta (f : _ -> A) :
  subst σ >>> (hsubst theta >>> f) =
  hsubst theta >>> (subst (σ >>> hsubst theta) >>> f).
Proof. now rewrite <- compA, scomp_hcompX. Qed.

End LemmasForHSubst.
*)

(** Normalize the goal state. *)

Ltac autosubst_typeclass_normalize :=
  mmap_typeclass_normalize;
  repeat match goal with
  | [|- context[ids ?x]] =>
    let s := constr:(ids x) in progress change (ids x) with s
  | [|- context[ren ?xi]] =>
    let s := constr:(ren xi) in progress change (ren xi) with s
  | [|- context[rename ?xi]] =>
    let s := constr:(rename xi) in progress change (rename xi) with s
  | [|- context[subst ?σ]] =>
    let s := constr:(subst σ) in progress change (subst σ) with s
  | [|- context[hsubst ?σ]] =>
    let s := constr:(hsubst σ) in progress change (hsubst σ) with s
  end.

Ltac autosubst_typeclass_normalizeH H :=
  mmap_typeclass_normalizeH H;
  repeat match typeof H with
  | context[ids ?x] =>
    let s := constr:(ids x) in progress change (ids x) with s in H
  | context[ren ?xi] =>
    let s := constr:(ren xi) in progress change (ren xi) with s in H
  | context[rename ?xi] =>
    let s := constr:(rename xi) in progress change (rename xi) with s in H
  | context[subst ?σ] =>
    let s := constr:(subst σ) in progress change (subst σ) with s in H
  | context[hsubst ?σ] =>
    let s := constr:(hsubst σ) in progress change (hsubst σ) with s in H
  end.

Ltac autosubst_unfold_up :=
  rewrite ?upX, ?upnSX;
  repeat match goal with
  | [|- context[upn 0 ?σ]] => change (upn 0 σ) with σ
  end.

Ltac autosubst_unfold_upH H :=
  rewrite ?upX, ?upnSX in H;
  repeat match typeof H with
  | context[upn 0 ?σ] => change (upn 0 σ) with σ
  end.

Ltac autosubst_unfold :=
  autosubst_typeclass_normalize; autosubst_unfold_up;
  rewrite ?rename_substX; unfold ren, scomp, hcomp, upren.

Ltac autosubst_unfoldH H :=
  autosubst_typeclass_normalizeH H; autosubst_unfold_upH H;
  rewrite ?rename_substX in H; unfold ren, scomp, hcomp, upren in H.

(** Simplify results. *)

Ltac fold_ren :=
  repeat match goal with
    | [|- context[?xi >>> (@ids ?T _)]] =>
         change (xi >>> (@ids T _)) with (@ren T _ xi)
    | [|- context[?xi >>> (@ids ?T _ >>> ?g)]] =>
         change (xi >>> (@ids T _ >>> g)) with (@ren T _ xi >>> g)
    | [|- context[?xi >>> @ren ?T _ ?zeta]] =>
         change (xi >>> @ren T _ zeta) with (@ren T _ (xi >>> zeta))
    | [|- context[?xi >>> (@ren ?T _ ?zeta >>> ?g)]] =>
         change (xi >>> (@ren T _ zeta >>> g)) with
                (@ren T _ (xi >>> zeta) >>> g)
    | [|- context [ids ?x .: ?σ]] =>
      first[
          rewrite fold_ren_cons
        | replace (ids x .: ids) with (ren (x .: id))
          by (symmetry; apply fold_ren_cons)
        ]
  end.

Ltac fold_renH H :=
  repeat match typeof H with
    | context[?xi >>> (@ids ?T _)] =>
         change (xi >>> (@ids T _)) with (@ren T _ xi) in H
    | context[?xi >>> (@ids ?T _ >>> ?g)] =>
         change (xi >>> (@ids T _ >>> g)) with (@ren T _ xi >>> g) in H
    | context[?xi >>> @ren ?T _ ?zeta] =>
         change (xi >>> @ren T _ zeta) with (@ren T _ (xi >>> zeta)) in H
    | context[?xi >>> (@ren ?T _ ?zeta >>> ?g)] =>
         change (xi >>> (@ren T _ zeta >>> g)) with
                (@ren T _ (xi >>> zeta) >>> g) in H
    | context [ids ?x .: ?σ] =>
      first[
          rewrite fold_ren_cons in H
        | replace (ids x .: ids) with (ren (x .: id)) in H
          by (symmetry; apply fold_ren_cons)
        ]
  end.

Ltac fold_comp :=
  repeat match goal with
    | [|- context[?f >>> (?g >>> ?h)]] =>
        change (f >>> (g >>> h)) with ((f >>> g) >>> h)
    | [|- context[?σ >>> subst ?tau]] =>
        change (σ >>> subst tau) with (σ >> tau)
    | [|- context[?σ >>> hsubst ?tau]] =>
        change (σ >>> hsubst tau) with (σ >>| tau)
  end.

Ltac fold_compH H :=
  repeat match typeof H with
    | context[?f >>> (?g >>> ?h)] =>
        change (f >>> (g >>> h)) with ((f >>> g) >>> h) in H
    | context[?σ >>> subst ?tau] =>
        change (σ >>> subst tau) with (σ >> tau) in H
    | context[?σ >>> hsubst ?tau] =>
        change (σ >>> hsubst tau) with (σ >>| tau) in H
  end.

Ltac fold_up := rewrite ?fold_up, ?fold_up0;
  repeat match goal with
    | [|- context[up (up ?σ)]] =>
      change (up (up σ)) with (upn 2 σ)
    | [|- context[up (upn ?n ?σ)]] =>
      change (up (upn n σ)) with (upn (S n) σ)
    | _ => rewrite fold_upn_up
  end;
  repeat open_fold (upren _).

Ltac fold_upH H := rewrite ?fold_up, ?fold_up0 in H;
  repeat match typeof H with
    | context[up (up ?σ)] =>
      change (up (up σ)) with (upn 2 σ) in H
    | context[up (upn ?n ?σ)] =>
      change (up (upn n σ)) with (upn (S n) σ) in H
    | _ => rewrite fold_upn_up in H
  end;
  repeat open_fold (upren _) in H.

(** Solve & Simplify goals involving substitutions. *)

Ltac autosubst :=
  cbn; trivial; autosubst_unfold; solve [repeat first
  [ solve [trivial]
  | progress (
      cbn; unfold _bind, ren, scomp, hcomp; fsimpl; autosubst_unfold_up;
      autorewrite with autosubst;
      rewrite ?id_scompX, ?id_scompR, ?subst_idX, ?subst_compX,
              ?subst_compR, ?id_subst, ?subst_id, ?subst_compI,
              ?id_hsubstX, ?id_hsubstR, ?hsubst_idX, ?scomp_hcompX,
              ?scomp_hcompR, ?hsubst_compX, ?hsubst_compR,
              ?hsubst_id, ?id_hsubst, ?hsubst_compI, ?scomp_hcompI
    )
  | match goal with [|- context[(_ .: _) ?x]] =>
      match goal with [y : _ |- _ ] => unify y x; destruct x; simpl @scons end
    end
  | fold_id]].

Ltac asimpl :=
  autorewrite with autosubst;
  cbn; autosubst_unfold; repeat first
  [ progress (
      cbn; unfold _bind, ren, scomp, hcomp; fsimpl; autosubst_unfold_up;
      autorewrite with autosubst;
      rewrite ?id_scompX, ?id_scompR, ?subst_idX, ?subst_compX,
              ?subst_compR, ?id_subst, ?subst_id, ?subst_compI,
              ?id_hsubstX, ?id_hsubstR, ?hsubst_idX, ?scomp_hcompX,
              ?scomp_hcompR, ?hsubst_compX, ?hsubst_compR,
              ?hsubst_id, ?id_hsubst, ?hsubst_compI, ?scomp_hcompI
    )
  | fold_id];
  fold_ren; fold_comp; fold_up.

Ltac asimplH H :=
  autorewrite with autosubst in H;
  cbn in H; autosubst_unfoldH H; repeat first
  [ progress (
      cbn in H; unfold _bind, ren, scomp, hcomp in H; fsimpl in H;
      autosubst_unfold_upH H; autorewrite with autosubst in H;
      rewrite ?id_scompX, ?id_scompR, ?subst_idX, ?subst_compX,
              ?subst_compR, ?id_subst, ?subst_id, ?subst_compI,
              ?id_hsubstX, ?id_hsubstR, ?hsubst_idX, ?scomp_hcompX,
              ?scomp_hcompR, ?hsubst_compX, ?hsubst_compR,
              ?hsubst_id, ?id_hsubst, ?hsubst_compI, ?scomp_hcompI in H
    )
  | fold_id in H];
  fold_renH H; fold_compH H; fold_upH H.

Tactic Notation "asimpl" "in" ident(H) := asimplH H.
Tactic Notation "asimpl" "in" "*" := (in_all asimplH); asimpl.
*)


End DTM_to_Autosubst_rw_lemmas.

