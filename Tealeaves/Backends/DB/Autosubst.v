From Tealeaves Require Import Backends.DB.DB Backends.DB.Simplification.
From Autosubst Require Autosubst.

#[local] Generalizable Variables W T U.

Module Autosubst_Shim.

  Import Autosubst.

  Section DTM_to_Autosubst.

    Context
      `{DecoratedTraversableMonadFull
          (op := Monoid_op_plus) (unit := Monoid_unit_zero) nat T}.

    #[export] Instance Ids_DTM: Ids (T nat) :=
      @ret T _ nat.
    #[export] Instance Rename_DTM: Rename (T nat) :=
      @DB.rename T _.
    #[export] Instance Subst_DTM : Subst (T nat) :=
      @DB.subst T _ _ _ _.

    Print SubstLemmas.

    Lemma rename_subst_DTM:
      forall (xi : nat -> nat) (s : T nat), rename xi s = s.[ren xi].
    Proof.
      intros.
      unfold_ops @Rename_DTM @Subst_DTM.
      tealeaves_unfold.
      reflexivity.
    Qed.

    Lemma subst_id_DTM:
      forall s : T nat, s.[ids] = s.
    Proof.
      intros.
      unfold_ops @Ids_DTM @Subst_DTM.
      simplify_db.
      reflexivity.
    Qed.

    Lemma id_subst_DTM: forall (sigma : nat -> T nat) (x : nat),
        (ids x).[sigma] = sigma x.
    Proof.
      intros.
      unfold_ops @Ids_DTM @Subst_DTM.
      simplify_db.
      conclude.
    Qed.

    Lemma subst_comp_DTM:
      forall (sigma tau : nat -> T nat) (s : T nat),
        s.[sigma].[tau] = s.[scomp sigma tau].
    Proof.
      intros.
      unfold_ops @Subst_DTM.
      compose near s on left.
      rewrite subst_subst.
      reflexivity.
    Qed.

    #[export] Instance SubstLemmas_term: SubstLemmas (T nat) :=
      {| rename_subst := rename_subst_DTM;
        subst_id := subst_id_DTM;
        id_subst := id_subst_DTM;
        subst_comp := subst_comp_DTM;
      |}.

  End DTM_to_Autosubst.

  Lemma cons_eq {X:Type}:
    @DB.scons X = Autosubst_Basics.scons.
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
    unfold up, up__sub.
    rewrite cons_eq.
    rewrite <- rename_policy_repr.
    reflexivity.
  Qed.

End Autosubst_Shim.

(*
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

  Lemma fold_ren_cons (x : nat) (xi : nat -> nat) :
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

Lemma id_hsubstX (σ : nat -> inner) : ids >>> hsubst σ = ids.
Proof. f_ext. apply id_hsubst. Qed.

Lemma id_hsubstR {A} (f : _ -> A) (σ : nat -> inner) :
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
