From Tealeaves Require Import
     Functors.List.

From Multisorted Require Import
     Classes.DTM
     Theory.DTMContainer
     Theory.DTMSchedule.

Import Tealeaves.Classes.Monoid.Notations.
Import Tealeaves.Theory.Product.Notations.
Import Tealeaves.Classes.Applicative.Notations.
Import Multisorted.Classes.DTM.Notations.
Require List.
Import List.ListNotations.

Open Scope list_scope.
Open Scope tealeaves_scope.
Open Scope tealeaves_multi_scope.

(** * The index [K] *)
(******************************************************************************)
Inductive K2 : Type := KType | KTerm.

Instance Keq : EqDec K2 eq.
Proof.
  change (forall x y : K2, {x = y} + {x <> y}).
  decide equality.
Defined.

Instance I2 : Index := {| K := K2 |}.

(** * System F syntax and typeclass instances *)
(******************************************************************************)
Parameter base_typ : Type.

Section syntax.

  Context
    {V : Type}.

  Inductive typ : Type :=
  | ty_c : base_typ -> typ
  | ty_v : V -> typ
  | ty_C : typ -> typ
  | ty_ar : typ -> typ -> typ
  | ty_univ : typ -> typ.

  Inductive term : Type :=
  | tm_var : V -> term
  | tm_abs : typ -> term -> term
  | tm_app : term -> term -> term
  | tm_tab : term -> term
  | tm_tap : term -> typ -> term.

End syntax.

(** Clear the implicit arguments to the type constructors. This keeps <<V>>
    implicit for the constructors. *)
Arguments typ V : clear implicits.
Arguments term V : clear implicits.

Definition SystemF (k : K)  (v : Type) : Type :=
  match k with
  | KType => typ v
  | KTerm => term v
  end.

(*
(** * Testing the syntax *)
(******************************************************************************)
Module examples.

  Context
    (x y z : atom)
    (c1 c2 c3 : base_typ).

  (** ** Raw abstract syntax *)
  (** tm_abstract syntax trees without notations or coercions *)
  Module raw.

    (** *** Constants and variables *)
    Example typ_1 : typ leaf := ty_v (Fr x).
    Example typ_2 : typ leaf := ty_v (Fr y).
    Example typ_3 : typ leaf := ty_v (Fr z).
    Example typ_4 : typ leaf := ty_v (B 0).
    Example typ_5 : typ leaf := ty_v (B 1).
    Example typ_6 : typ leaf := ty_v (B 2).
    Example typ_7 : typ leaf := ty_c c1.
    Example typ_8 : typ leaf := ty_c c2.

    (** *** Simple types *)
    Example typ_9  : typ leaf := ty_ar (ty_v (Fr x))
                                       (ty_v (Fr x)).
    Example typ_10 : typ leaf := ty_ar (ty_v (Fr x))
                                       (ty_v (Fr y)).
    Example typ_11 : typ leaf := ty_ar (ty_v (Fr x))
                                       (ty_v (B 1)).
    Example typ_12 : typ leaf := ty_ar (ty_v (B 1))
                                       (ty_c c1).
    Example typ_13 : typ leaf := ty_ar (ty_ar (ty_v (B 0))
                                              (ty_v (Fr x)))
                                       (ty_v (B 1)).
    Example typ_14 : typ leaf := ty_ar (ty_c c2)
                                       (ty_ar (ty_v (Fr x))
                                              (ty_v (B 1))).
    Example typ_15 : typ leaf := ty_ar (ty_ar (ty_v (B 2))
                                              (ty_c c1))
                                       (ty_ar (ty_v (Fr y))
                                              (ty_v (Fr x))).
    Example typ_16 : typ leaf := ty_ar (ty_ar (ty_v (B 2))
                                              (ty_v (B 1)))
                                       (ty_ar (ty_v (Fr y))
                                              (ty_v (Fr x))).

    (** *** Universal types *)
    Example typ_17 : typ leaf := ty_univ (ty_ar (ty_v (B 0))
                                                (ty_v (B 0))).
    Example typ_18 : typ leaf := ty_univ (ty_ar (ty_ar (ty_v (B 2))
                                                       (ty_v (B 1)))
                                                (ty_ar (ty_v (Fr y))
                                                       (ty_v (Fr x)))).
  End raw.


  Definition ty_c_ : base_typ -> typ leaf := @ty_c leaf.
  Definition ty_v_ : leaf -> typ leaf := @ty_v leaf.
  Coercion ty_c_ : base_typ >-> typ.
  Coercion ty_v_ : leaf >-> typ.
  Coercion Fr : atom >-> leaf.
  Coercion B : nat >-> leaf.

  (* ⟹ at 50+1 to avoid assoc. conflict *)
  Notation "A ⟹ B" := (ty_ar A B) (at level 51, right associativity).
  Notation "∀ τ" := (ty_univ τ) (at level 60).

  (** ** Pretyy tm_abstract syntax for types *)
  Module pretty.

    (** *** Constants and variables *)
    Example typ_1 : typ leaf := x.
    Example typ_2 : typ leaf := y.
    Example typ_3 : typ leaf := Fr z.

    Goal (x : typ leaf) = ty_v (Fr x). reflexivity. Qed.
    Goal (x : typ leaf) = Fr x. reflexivity. Qed.

    Example typ_4 : typ leaf := 0.
    Example typ_5 : typ leaf := B 1.
    Example typ_6 : typ leaf := 2.
    Example typ_7 : typ leaf := c1.
    Example typ_8 : typ leaf := c2.

    Goal (0 : typ leaf) = ty_v (B 0). reflexivity. Qed.
    Goal (0 : typ leaf) = B 0. reflexivity. Qed.
    Goal (c1 : typ leaf) = ty_c c1. reflexivity. Qed.

    (** *** Simple types *)
    Example typ_9  : typ leaf := x ⟹ x.
    Example typ_10 : typ leaf := x ⟹ y.

    Goal ((x ⟹ x : typ leaf) = Fr x ⟹ Fr x). reflexivity. Qed.
    Goal ((x ⟹ 1 : typ leaf) = Fr x ⟹ B 1). reflexivity. Qed.

    Example typ_11 : typ leaf := x ⟹ 1.
    Example typ_12 : typ leaf := x ⟹ c1.
    Example typ_13 : typ leaf := (x ⟹ 0) ⟹ 1.
    Example typ_14 : typ leaf := c2 ⟹ (x ⟹ 1).

    Goal c2 ⟹ x ⟹ 1 = c2 ⟹ (x ⟹ 1). reflexivity. Qed.

    Example typ_15 : typ leaf := (2 ⟹ c1) ⟹ (y ⟹ x).
    Example typ_16 : typ leaf := (2 ⟹ 1) ⟹ (y ⟹ x).

    (** *** Universal types *)
    Example typ_17 : typ leaf := ∀ (0 ⟹ 0).
    Goal ∀ (0 ⟹ 0) = ∀ 0 ⟹ 0. reflexivity. Qed.

    Example typ_18 : typ leaf := ∀ (2 ⟹ 1) ⟹ (y ⟹ x).
    Goal ∀ (2 ⟹ 1) ⟹ (y ⟹ x) = ∀ ((2 ⟹ 1) ⟹ (y ⟹ x)). reflexivity. Qed.

    Example typ_19 : typ leaf := (∀ 2 ⟹ 1) ⟹ (y ⟹ x).
    Example typ_20 : typ leaf := (2 ⟹ 1) ⟹ ∀ y ⟹ x.

  End pretty.

  (** ** Demo of opening operation *)
  Goal open typ KType (Fr x) (B 0) = Fr x. reflexivity. Qed.
  Goal open typ KType (Fr x) (B 1) = B 0. reflexivity. Qed.
  Goal open typ KType (Fr x) (Fr x) = Fr x. reflexivity. Qed.
  Goal open typ KType (Fr x) (Fr y) = Fr y. reflexivity. Qed.
  Goal open typ KType (Fr y) (Fr x) = Fr x. reflexivity. Qed.
  Goal open typ KType (Fr y) (Fr y) = Fr y. reflexivity. Qed.
  Goal open typ KType (Fr x) (∀ B 0) = (∀ (B 0)). reflexivity. Qed.
  Goal open typ KType (Fr x) (∀ B 1) = (∀ (Fr x)). reflexivity. Qed.
  Goal open typ KType (Fr x) (∀ (B 1 ⟹ B 0)) = (∀ Fr x ⟹ B 0). reflexivity. Qed.
  Goal open typ KType (Fr x) (∀ B 1 ⟹ B 2) = (∀ Fr x ⟹ B 1). reflexivity. Qed.

  Example term_1 : term leaf := tm_var (Fr x).
  Example term_2 : term leaf := tm_var (B 0).
  Example term_3 : term leaf := tm_app term_1 term_2.
  Example term_4 : term leaf := tm_app term_3 term_3.
  (** Identity function on type [c1]. *)
  Example term_5 : term leaf := tm_abs (ty_c c1) (tm_var (B 0)).
  Example term_6 : term leaf := tm_app term_5 term_3.
  (** Polymorphic identity function. *)
  Example term_7 : term leaf := tm_tab (tm_abs (ty_v (B 0))(tm_var (B 0))).
  Example term_8 : term leaf := tm_tap (tm_tab (tm_abs (ty_v (B 0))(tm_var (B 0))))
                                       (ty_c c1).

  Notation "'λ' X ⋅ body" := (tm_abs X body) (at level 45).
  Notation "[ t1 ] [ t2 ]" := (tm_app t1 t2) (at level 40).
  Notation "'Λ' body" := (tm_tab body) (at level 45).
  Notation "[ t1 ] @ [ t2 ]" := (tm_tap t1 t2) (at level 40).

  Definition tm_var_ : leaf -> term leaf := @tm_var leaf.
  Coercion tm_var_ : leaf >-> term.

  Check (Λ λ (B 0) ⋅ (B 0)).

End examples.
*)

(** ** <<binddt>> operations *)
(******************************************************************************)
Section operations.

  Context
    (F : Type -> Type)
    `{Applicative F}.

  Fixpoint bind_type {A B : Type} (f : forall k, list K2 * A -> F (SystemF k B)) (t : typ A) : F (typ B) :=
    match t with
    | ty_c t => pure F (ty_c t)
    | ty_v a => f KType (nil, a)
    | ty_C t => pure F ty_C <⋆> bind_type f t
    | ty_ar t1 t2 => pure F (ty_ar) <⋆> (bind_type f t1) <⋆> (bind_type f t2)
    | ty_univ body => pure F (ty_univ) <⋆> (bind_type (fun k => f k ∘ incr [KType]) body)
    end.

  Fixpoint bind_term {A B} (f  : forall k, list K2 * A -> F (SystemF k B)) (t : term A) : F (term B) :=
    match t with
    | tm_var a => f KTerm (nil, a)
    | tm_abs ty body =>
      pure F (tm_abs)
           <⋆> bind_type (fun k => f k ∘ incr [KTerm]) ty
           <⋆> bind_term (fun k => f k ∘ incr [KTerm]) body
    | tm_app t1 t2 => pure F tm_app <⋆> bind_term f t1 <⋆> bind_term f t2
    | tm_tab body => pure F tm_tab <⋆> (bind_term (fun k => f k ∘ incr [KType]) body)
    | tm_tap t1 ty => pure F tm_tap <⋆> bind_term f t1 <⋆> bind_type f ty
    end.

End operations.

Instance: MReturn SystemF :=
  fun A k => match k with
          | KType => ty_v
          | KTerm => tm_var
          end.

Instance MBind_type : MBind (list K2) SystemF typ := @bind_type.
Instance MBind_term : MBind (list K2) SystemF term := @bind_term.
Instance MBind_SystemF : forall k, MBind (list K2) SystemF (SystemF k) :=
  ltac:(intros [|]; typeclasses eauto).

Section DTM_instance_lemmas.

  Context
    (W : Type)
    (S : Type -> Type)
    (T : K -> Type -> Type)
    `{! MReturn T}
    `{! MBind W T S}
    `{! forall k, MBind W T (T k)}
    {mn_op : Monoid_op W}
    {mn_unit : Monoid_unit W}.

  Lemma mbinddt_inst_law1_case1 : forall (A : Type) (t : S A) (w : W),
      (mbinddt S (fun A => A) (fun k => mret T k ∘ extract (W ×)) t = t) ->
      (mbinddt S (fun A => A) (fun k => mret T k ∘ extract (W ×) ∘ incr w) t = t).
  Proof.
    introv IH. rewrite <- IH at 2.
    fequal. ext k [w' a]. easy.
  Qed.

  Lemma mbinddt_inst_law1_case12 : forall (A : Type) (w : W),
      mbinddt S (fun A => A) (fun k => mret T k ∘ extract (W ×)) (A := A) =
      mbinddt S (fun A => A) (fun k => mret T k ∘ extract (W ×) ∘ incr w).
  Proof.
    introv. fequal. now ext k [w' a].
  Qed.

  Context
    `{Applicative G}
    `{Applicative F}
    `{! Monoid W}
    {A B C : Type}
    (g : forall k, W * B -> G (T k C))
    (f : forall k, W * A -> F (T k B)).

  (* for Var case *)
  Lemma mbinddt_inst_law2_case2 : forall (a : A) (k : K),
    fmap F (mbinddt (T k) G g) (f k (Ƶ, a)) =
    fmap F (mbinddt (T k) G (fun k => g k ∘ const (incr Ƶ) k)) (f k (Ƶ, a)).
  Proof.
    intros. repeat fequal. ext k' [w b].
    unfold compose. cbn. now simpl_monoid.
  Qed.

  Lemma compose_dtm_incr : forall (w : W),
      (fun k => (g ⋆dtm f) k ∘ incr w) =
      ((fun k => g k ∘ incr w) ⋆dtm (fun k => f k ∘ incr w)).
  Proof.
    intros. ext k [w' a].
    cbn. do 2 fequal.
    ext j [w'' b].
    unfold compose. cbn. fequal.
    now rewrite monoid_assoc.
  Qed.

End DTM_instance_lemmas.

Lemma mbinddt_mret_typ : forall (A : Type),
    mbinddt typ (fun A => A) (fun k => mret SystemF k ∘ extract (list K2 ×)) = @id (typ A).
Proof.
  intros. ext t. unfold id. induction t.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. fequal.
    + apply IHt.
  - cbn. fequal.
    + apply IHt1.
    + apply IHt2.
  - cbn. fequal.
    + rewrite <- mbinddt_inst_law1_case12.
      apply IHt.
Qed.

Lemma mbinddt_mret_term : forall (A : Type),
    mbinddt term (fun A => A) (fun k => mret SystemF k ∘ extract (list K2 ×)) = @id (term A).
Proof.
  intros. ext t. unfold id. induction t.
  - easy.
  - cbn. fequal.
    + change (bind_type ?F ?f) with (mbinddt typ F f).
      rewrite <- mbinddt_inst_law1_case12.
      now rewrite mbinddt_mret_typ.
    + rewrite <- mbinddt_inst_law1_case12.
      apply IHt.
  - cbn. fequal.
    + apply IHt1.
    + apply IHt2.
  - cbn. fequal.
    rewrite <- mbinddt_inst_law1_case12.
    apply IHt.
  - cbn. fequal.
    + apply IHt.
    + now rewrite mbinddt_mret_typ.
Qed.

Lemma mbinddt_mbinddt_typ_generalized :
  forall (A : Type)
    (F : Type -> Type)
    (G : Type -> Type)
    `{Applicative F}
    `{Applicative G}
    `(g : forall k, list K2 * B -> G (SystemF k C))
    `(f : forall k, list K2 * A -> F (SystemF k B)),
    fmap F (mbinddt typ G g) ∘ mbinddt typ F f =
    mbinddt typ (F ∘ G) (g ⋆dtm f).
Proof.
  intros. ext t. generalize dependent f. generalize dependent g.
  unfold compose at 1. induction t; intros g f.
  - cbn.
    rewrite (app_pure_natural F).
    reflexivity.
  - cbn.
    change (MBind_type ?G H3 H4 H5 ?A ?B) with (mbinddt typ G (A := A) (B := B)).
    change [] with (Ƶ : list K2).
    change typ with (SystemF KType).
    rewrite <- (mbinddt_inst_law2_case2 (list K2) SystemF (H := MBind_SystemF )).
    reflexivity.
  - cbn.
    rewrite <- IHt.
    rewrite (ap_compose3 G F).
    rewrite <- (ap7 (G := F)).
    compose near (pure (F ∘ G) (ty_C (V := C))).
    rewrite (fun_fmap_fmap F).
    unfold_ops @Pure_compose.
    rewrite (app_pure_natural F).
    rewrite ap6.
    rewrite (app_pure_natural F).
    reflexivity.
  - cbn.
    rewrite <- IHt1.
    rewrite <- IHt2.
    do 2 rewrite (ap_compose3 G F).
    rewrite <- (ap7 (G := F)).
    rewrite <- (ap7 (G := F)).
    do 2 rewrite ap6.
    do 2 rewrite ap6.
    do 3 (compose near (pure (F ∘ G) (ty_ar (V := C)));
          rewrite (fun_fmap_fmap F)).
    unfold_ops @Pure_compose.
    rewrite (app_pure_natural F).
    rewrite (app_pure_natural F).
    reflexivity.
  - cbn. setoid_rewrite compose_dtm_incr.
    2:{ typeclasses eauto. }
    rewrite <- IHt.
    rewrite (ap_compose3 G F).
    rewrite <- (ap7 (G := F)).
    compose near (pure (F ∘ G) (ty_univ (V := C))).
    rewrite (fun_fmap_fmap F).
    unfold_ops @Pure_compose.
    rewrite (app_pure_natural F).
    rewrite ap6.
    rewrite (app_pure_natural F).
    reflexivity.
Qed.

Lemma mbinddt_mbinddt_term :
  forall (A : Type)
    (F : Type -> Type)
    (G : Type -> Type)
    `{Applicative F}
    `{Applicative G}
    `(g : forall k, list K2 * B -> G (SystemF k C))
    `(f : forall k, list K2 * A -> F (SystemF k B)),
    fmap F (mbinddt term G g) ∘ mbinddt term F f =
    mbinddt term (F ∘ G) (g ⋆dtm f).
Proof.
Admitted.

(*
Instance: DTPreModule (list K2) typ SystemF :=
  {| dtp_mbinddt_mret := @mbinddt_mret_typ;
     dtp_mbinddt_mbinddt := @mbinddt_mbindt_typ;
  |}.

Instance: DTPreModule (list K2) term SystemF :=
  {| dtp_mbinddt_mret := @mbinddt_mret_term;
     dtp_mbinddt_mbinddt := @mbinddt_mbindt_typ;
  |}.
*)

(** *** Rewriting operations in <<typ>> *)
Section rw_tomlist_type.

  Context
    (A : Type).

  Lemma rw_tomlist_type1 : forall c, tomlist (A:=A) typ (ty_c c) = [].
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_type2 : forall (a : A), tomlist typ (ty_v a) = [(KType, a)].
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_type3 : forall (body : typ A), tomlist typ (ty_univ body) = tomlist typ body.
  Proof. idtac. Admitted.

  Lemma rw_tomlist_type4 : forall (t1 t2 : typ A), tomlist typ (ty_ar t1 t2) = tomlist typ t1 ++ tomlist typ t2.
  Proof. intros. cbn. unfold_ops @Monoid_op_list. now simpl_list. Qed.

End rw_tomlist_type.

Create HintDb sysf_rw.
Hint Rewrite @rw_tomlist_type1 @rw_tomlist_type2
     @rw_tomlist_type3 @rw_tomlist_type4 : sysf_rw.

Section rw_toklist_KTerm_type.

  Context
    (A : Type).

  Lemma rw_toklist_KTerm_type1 : forall c, toklist (A:=A) typ KTerm (ty_c c) = [].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_type2 : forall (a : A), toklist typ KTerm (ty_v a) = [].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_type3 : forall (body : typ A), toklist typ KTerm (ty_univ body) = toklist typ KTerm body.
  Proof. rewrite tomlistd. Qed.

  Lemma rw_toklist_KTerm_type4 : forall (t1 t2 : typ A), toklist typ KTerm (ty_ar t1 t2) = toklist typ KTerm t1 ++ toklist typ KTerm t2.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_toklist_KTerm_type.

Hint Rewrite @rw_toklist_KTerm_type1 @rw_toklist_KTerm_type2
     @rw_toklist_KTerm_type3 @rw_toklist_KTerm_type4 : sysf_rw.

Section rw_toklist_KType_type.

  Context
    (A : Type).

  Lemma rw_toklist_KType_type1 : forall c, toklist (A:=A) typ KType (ty_c c) = [].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_type2 : forall (a : A), toklist typ KType (ty_v a) = [a].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_type3 : forall (body : typ A), toklist typ KType (ty_univ body) = toklist typ KType body.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_type4 : forall (t1 t2 : typ A), toklist typ KType (ty_ar t1 t2) = toklist typ KType t1 ++ toklist typ KType t2.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_toklist_KType_type.

Hint Rewrite @rw_toklist_KType_type1 @rw_toklist_KType_type2
     @rw_toklist_KType_type3 @rw_toklist_KType_type4 : sysf_rw.

Section rw_in_KType_type.

  Context
    (A : Type).

  Lemma rw_in_KType_type1 : forall (c : base_typ) (a : A), (KType, a) ∈m ty_c c <-> False.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder.
  Qed.

  Lemma rw_in_KType_type2 : forall (a1 a2 : A), (KType, a2) ∈m ty_v a1 <-> a1 = a2.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder.
  Qed.

  Lemma rw_in_KType_type3 : forall t1 t2 (a : A), (KType, a) ∈m (ty_ar t1 t2) <-> (KType, a) ∈m t1 \/ (KType, a) ∈m t2.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder.
  Qed.

  Lemma rw_in_KType_type4 : forall (t : typ A) (a : A), (KType, a) ∈m ty_univ t <-> (KType, a) ∈m t.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder.
  Qed.

End rw_in_KType_type.

Hint Rewrite @rw_in_KType_type1 @rw_in_KType_type2
     @rw_in_KType_type3 @rw_in_KType_type4 : sysf_rw.

(* This seems necessary to prevent <<autorewrite>> from
   simplifying too far and unifying with unintended lemmas. *)
Set Keyed Unification.

Section rw_in_KTerm_type.

  Context
    (A : Type).

  Lemma rw_in_KTerm_type1 : forall (c : base_typ) (a : A), (KTerm, a) ∈m ty_c c <-> False.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder.
  Qed.

  Lemma rw_in_KTerm_type2 : forall (a1 a2 : A), (KTerm, a2) ∈m ty_v a1 <-> False.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder (try discriminate).
  Qed.

  Lemma rw_in_KTerm_type3 : forall t1 t2 (a : A), (KTerm, a) ∈m (ty_ar t1 t2) <-> (KTerm, a) ∈m t1 \/ (KTerm, a) ∈m t2.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder.
  Qed.

  Lemma rw_in_KTerm_type4 : forall (t : typ A) (a : A), (KTerm, a) ∈m ty_univ t <-> (KTerm, a) ∈m t.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder.
  Qed.

End rw_in_KTerm_type.

Hint Rewrite @rw_in_KTerm_type1 @rw_in_KTerm_type2
     @rw_in_KTerm_type3 @rw_in_KTerm_type4 : sysf_rw.

Section rw_free_KType_type.

  Lemma rw_free_KType_type11 : forall (x : atom), free typ KType (ty_v (Fr x)) = [x].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type12 : forall (n : nat), free typ KType (ty_v (B n)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type2 : forall (c : base_typ), free typ KType (ty_c c) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type3 : forall t1 t2, free typ KType (ty_ar t1 t2) = free typ KType t1 ++ free typ KType t2.
  Proof.
    intros. unfold free. autorewrite with sysf_rw tea_list.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type4 : forall t, free typ KType (ty_univ t) = free typ KType t.
  Proof.
    intros. unfold free. autorewrite with sysf_rw tea_list.
    reflexivity.
  Qed.

End rw_free_KType_type.

Hint Rewrite rw_free_KType_type11 rw_free_KType_type12 rw_free_KType_type2
     rw_free_KType_type3 rw_free_KType_type4 : sysf_rw.

Section rw_free_KTerm_type.

  Lemma rw_free_KTerm_type11 : forall (x : atom), free typ KTerm (ty_v (Fr x)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type12 : forall (n : nat), free typ KTerm (ty_v (B n)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type2 : forall (c : base_typ), free typ KTerm (ty_c c) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type3 : forall t1 t2, free typ KTerm (ty_ar t1 t2) = free typ KTerm t1 ++ free typ KTerm t2.
  Proof.
    intros. unfold free. autorewrite with sysf_rw tea_list.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type4 : forall t, free typ KTerm (ty_univ t) = free typ KTerm t.
  Proof.
    intros. unfold free. autorewrite with sysf_rw tea_list.
    reflexivity.
  Qed.

End rw_free_KTerm_type.

Hint Rewrite rw_free_KTerm_type11 rw_free_KTerm_type12 rw_free_KTerm_type2
     rw_free_KTerm_type3 rw_free_KTerm_type4 : sysf_rw.

Section rw_freeset_KType_type.

  Lemma rw_freeset_KType_type11 : forall (x : atom), freeset typ KType (ty_v (Fr x)) [=] {{ x }}.
  Proof.
    unfold freeset. intros. autorewrite with sysf_rw tea_rw_atoms. fsetdec.
  Qed.

  Lemma rw_freeset_KType_type12 : forall (n : nat), freeset typ KType (ty_v (B n)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KType_type2 : forall (c : base_typ), freeset typ KType (ty_c c) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KType_type3 : forall t1 t2, freeset typ KType (ty_ar t1 t2) [=] freeset typ KType t1 ∪ freeset typ KType t2.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KType_type4 : forall t, freeset typ KType (ty_univ t) [=] freeset typ KType t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_freeset_KType_type.

Hint Rewrite rw_freeset_KType_type11 rw_freeset_KType_type12 rw_freeset_KType_type2
     rw_freeset_KType_type3 rw_freeset_KType_type4 : sysf_rw.

Section rw_freeset_KTerm_type.

  Lemma rw_freeset_KTerm_type11 : forall (x : atom), freeset typ KTerm (ty_v (Fr x)) [=] ∅.
  Proof.
    unfold freeset. intros. autorewrite with sysf_rw tea_rw_atoms. fsetdec.
  Qed.

  Lemma rw_freeset_KTerm_type12 : forall (n : nat), freeset typ KTerm (ty_v (B n)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type2 : forall (c : base_typ), freeset typ KTerm (ty_c c) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type3 : forall t1 t2, freeset typ KTerm (ty_ar t1 t2) [=] freeset typ KTerm t1 ∪ freeset typ KTerm t2.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type4 : forall t, freeset typ KTerm (ty_univ t) [=] freeset typ KTerm t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_freeset_KTerm_type.

Hint Rewrite rw_freeset_KTerm_type11 rw_freeset_KTerm_type12 rw_freeset_KTerm_type2
     rw_freeset_KTerm_type3 rw_freeset_KTerm_type4 : sysf_rw.

(** *** Rewriting operations in <<term>> *)
Section rw_tomlist_term.

  Context
    (A : Type).

  Lemma rw_tomlist_term1 : forall (a : A), tomlist term (tm_var a) = [(KTerm, a)].
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_term2 : forall (ty : typ A) (body : term A), tomlist term (tm_abs ty body) = tomlist typ ty ++ tomlist term body.
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_term3 : forall (t1 t2 : term A), tomlist term (tm_app t1 t2) = tomlist term t1 ++ tomlist term t2.
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_term4 : forall (body : term A), tomlist term (tm_tab body) = tomlist term body.
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_term5 : forall (tm : term A) (ty : typ A), tomlist term (tm_tap tm ty) = tomlist term tm ++ tomlist typ ty.
  Proof. reflexivity. Qed.

End rw_tomlist_term.

Create HintDb sysf_rw.
Hint Rewrite @rw_tomlist_term1 @rw_tomlist_term2
     @rw_tomlist_term3 @rw_tomlist_term4 @rw_tomlist_term5 : sysf_rw.

Section rw_toklist_KType_term.

  Context
    (A : Type).

  Lemma rw_toklist_KType_term1 : forall (a : A), toklist term KType (tm_var a) = [].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_term2 : forall (ty : typ A) (body : term A), toklist term KType (tm_abs ty body) = toklist typ KType ty ++ toklist term KType body.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_toklist_KType_term3 : forall (t1 t2 : term A), toklist term KType (tm_app t1 t2) = toklist term KType t1 ++ toklist term KType t2.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_toklist_KType_term4 : forall (body : term A), toklist term KType (tm_tab body) = toklist term KType body.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_term5 : forall (tm : term A) (ty : typ A), toklist term KType (tm_tap tm ty) = toklist term KType tm ++ toklist typ KType ty.
  Proof.  intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_toklist_KType_term.

Create HintDb sysf_rw.
Hint Rewrite @rw_toklist_KType_term1 @rw_toklist_KType_term2
     @rw_toklist_KType_term3 @rw_toklist_KType_term4 @rw_toklist_KType_term5 : sysf_rw.

Section rw_toklist_KTerm_term.

  Context
    (A : Type).

  Lemma rw_toklist_KTerm_term1 : forall (a : A), toklist term KTerm (tm_var a) = [ a ].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_term2 : forall (ty : typ A) (body : term A), toklist term KTerm (tm_abs ty body) = toklist typ KTerm ty ++ toklist term KTerm body.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_toklist_KTerm_term3 : forall (t1 t2 : term A), toklist term KTerm (tm_app t1 t2) = toklist term KTerm t1 ++ toklist term KTerm t2.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_toklist_KTerm_term4 : forall (body : term A), toklist term KTerm (tm_tab body) = toklist term KTerm body.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_term5 : forall (tm : term A) (ty : typ A), toklist term KTerm (tm_tap tm ty) = toklist term KTerm tm ++ toklist typ KTerm ty.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_toklist_KTerm_term.

Hint Rewrite @rw_toklist_KTerm_term1 @rw_toklist_KTerm_term2
     @rw_toklist_KTerm_term3 @rw_toklist_KTerm_term4 @rw_toklist_KTerm_term5 : sysf_rw.

Section rw_in_KType_term.

  Context
    (A : Type).

  Lemma rw_in_KType_term1 : forall (a1 a2 : A), (KType, a2) ∈m tm_var a1 <-> False.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. firstorder discriminate.
  Qed.

  Lemma rw_in_KType_term2 : forall (T : typ A) (t : term A) (a : A), (KType, a) ∈m tm_abs T t <-> (KType, a) ∈m T \/ (KType, a) ∈m t.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_in_KType_term3 : forall t1 t2 (a : A), (KType, a) ∈m (tm_app t1 t2) <-> (KType, a) ∈m t1 \/ (KType, a) ∈m t2.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_in_KType_term4 : forall (t : term A) (a : A), (KType, a) ∈m tm_tab t <-> (KType, a) ∈m t.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_in_KType_term5 : forall t T (a : A), (KType, a) ∈m (tm_tap t T) <-> (KType, a) ∈m t \/ (KType, a) ∈m T.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

End rw_in_KType_term.

Hint Rewrite @rw_in_KType_term1 @rw_in_KType_term2 @rw_in_KType_term3
     @rw_in_KType_term4 @rw_in_KType_term5 : sysf_rw.

Section rw_in_KTerm_term.

  Context
    (A : Type).

  Lemma rw_in_KTerm_term1 : forall (a1 a2 : A), (KTerm, a2) ∈m tm_var a1 <-> a1 = a2.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    autorewrite with sysf_rw tea_list. intuition.
  Qed.

  Lemma rw_in_KTerm_term2 : forall (T : typ A) (t : term A) (a : A), (KTerm, a) ∈m tm_abs T t <-> (KTerm, a) ∈m T \/ (KTerm, a) ∈m t.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_in_KTerm_term3 : forall t1 t2 (a : A), (KTerm, a) ∈m (tm_app t1 t2) <-> (KTerm, a) ∈m t1 \/ (KTerm, a) ∈m t2.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_in_KTerm_term4 : forall (t : term A) (a : A), (KTerm, a) ∈m tm_tab t <-> (KTerm, a) ∈m t.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_in_KTerm_term5 : forall t T (a : A), (KTerm, a) ∈m (tm_tap t T) <-> (KTerm, a) ∈m t \/ (KTerm, a) ∈m T.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

End rw_in_KTerm_term.

Hint Rewrite @rw_in_KTerm_term1 @rw_in_KTerm_term2 @rw_in_KTerm_term3
     @rw_in_KTerm_term4 @rw_in_KTerm_term5 : sysf_rw.

Section rw_free_KType_term.

  Lemma rw_free_KType_term11 : forall n : nat, free term KType (tm_var (B n)) = [].
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KType_term12 : forall x : atom, free term KType (tm_var (Fr x)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_term2 : forall τ t, free term KType (tm_abs τ t) = free typ KType τ ++ free term KType t.
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KType_term3 : forall t1 t2, free term KType (tm_app t1 t2) = free term KType t1 ++ free term KType t2.
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KType_term4 : forall t, free term KType (tm_tab t) = free term KType t.
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KType_term5 : forall t τ, free term KType (tm_tap t τ) = free term KType t ++ free typ KType τ.
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

End rw_free_KType_term.

Hint Rewrite rw_free_KType_term11 rw_free_KType_term12 rw_free_KType_term2
     rw_free_KType_term3 rw_free_KType_term4 rw_free_KType_term5 : sysf_rw.

Section rw_free_KTerm_term.

  Lemma rw_free_KTerm_term11 : forall n : nat, free term KTerm (tm_var (B n)) = [].
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KTerm_term12 : forall x : atom, free term KTerm (tm_var (Fr x)) = [x].
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KTerm_term2 : forall τ t, free term KTerm (tm_abs τ t) = free typ KTerm τ ++ free term KTerm t.
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KTerm_term3 : forall t1 t2, free term KTerm (tm_app t1 t2) = free term KTerm t1 ++ free term KTerm t2.
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KTerm_term4 : forall t, free term KTerm (tm_tab t) = free term KTerm t.
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KTerm_term5 : forall t τ, free term KTerm (tm_tap t τ) = free term KTerm t ++ free typ KTerm τ.
  Proof.
    intros. unfold free.
    now autorewrite with sysf_rw tea_list.
  Qed.

End rw_free_KTerm_term.

Hint Rewrite rw_free_KTerm_term11 rw_free_KTerm_term12 rw_free_KTerm_term2
     rw_free_KTerm_term3 rw_free_KTerm_term4 rw_free_KTerm_term5 : sysf_rw.

Section rw_freeset_KType_term.

  Lemma rw_freeset_KType_term11 : forall n : nat, freeset term KType (tm_var (B n)) [=] ∅.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KType_term12 : forall x : atom, freeset term KType (tm_var (Fr x)) [=] ∅.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KType_term2 : forall τ t, freeset term KType (tm_abs τ t) [=] freeset typ KType τ ∪ freeset term KType t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KType_term3 : forall t1 t2, freeset term KType (tm_app t1 t2) [=] freeset term KType t1 ∪ freeset term KType t2.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KType_term4 : forall t, freeset term KType (tm_tab t) [=] freeset term KType t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KType_term5 : forall t τ, freeset term KType (tm_tap t τ) [=] freeset term KType t ∪ freeset typ KType τ.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_freeset_KType_term.

Hint Rewrite rw_freeset_KType_term11 rw_freeset_KType_term12 rw_freeset_KType_term2
     rw_freeset_KType_term3 rw_freeset_KType_term4 rw_freeset_KType_term5 : sysf_rw.

Section rw_freeset_KTerm_term.

  Lemma rw_freeset_KTerm_term11 : forall n : nat, freeset term KTerm (tm_var (B n)) [=] ∅.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_term12 : forall x : atom, freeset term KTerm (tm_var (Fr x)) [=] {{ x }}.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_term2 : forall τ t, freeset term KTerm (tm_abs τ t) [=] freeset typ KTerm τ ∪ freeset term KTerm t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_term3 : forall t1 t2, freeset term KTerm (tm_app t1 t2) [=] freeset term KTerm t1 ∪ freeset term KTerm t2.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_term4 : forall t, freeset term KTerm (tm_tab t) [=] freeset term KTerm t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_term5 : forall t τ, freeset term KTerm (tm_tap t τ) [=] freeset term KTerm t ∪ freeset typ KTerm τ.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_freeset_KTerm_term.

Hint Rewrite rw_freeset_KTerm_term11 rw_freeset_KTerm_term12 rw_freeset_KTerm_term2
     rw_freeset_KTerm_term3 rw_freeset_KTerm_term4 rw_freeset_KTerm_term5 : sysf_rw.
