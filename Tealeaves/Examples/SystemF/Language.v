From Tealeaves Require Import
     Functors.List
     LN.Leaf LN.Atom LN.AtomSet LN.AssocList
     LN.Multisorted.Operations
     Classes.Kleisli.Decorated.Monad. (* prepromote *)

From Tealeaves.Multisorted Require Import
     Classes.DTM
     Theory.DTMContainer
     Theory.DTMSchedule.

Import AtomSet.Notations.
Import Tealeaves.Classes.Monoid.Notations.
Import Tealeaves.Data.Product.Notations.
Import Tealeaves.Classes.Algebraic.Applicative.Notations.
Import Multisorted.Classes.DTM.Notations.
Import List.ListNotations.

Open Scope set_scope.
Open Scope list_scope.
Open Scope tealeaves_scope.
Open Scope tealeaves_multi_scope.

#[local] Generalizable Variables F G A B C ϕ.

(** * The index [K] *)
(******************************************************************************)
Inductive K2 : Type := KType | KTerm.

#[export] Instance Keq : EqDec K2 eq.
Proof.
  change (forall x y : K2, {x = y} + {x <> y}).
  decide equality.
Defined.

#[export] Instance I2 : Index := {| K := K2 |}.

(** * System F syntax and typeclass instances *)
(******************************************************************************)
Parameter base_typ : Type.

Section syntax.

  Context
    {V : Type}.

  Inductive typ : Type :=
  | ty_c : base_typ -> typ
  | ty_v : V -> typ
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

Definition SystemF (k : K) (v : Type) : Type :=
  match k with
  | KType => typ v
  | KTerm => term v
  end.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Declare Scope SystemF_scope.

  (** *** Notations for type expressions *)
  Notation "A ⟹ B" := (ty_ar A B) (at level 51, right associativity) : SystemF_scope.
  Notation "∀ τ" := (ty_univ τ) (at level 60) : SystemF_scope.

  (** *** Notations for term expressions *)
  Notation "'λ' X ⋅ body" := (tm_abs X body) (at level 45) : SystemF_scope.
  Notation "t1 @ t2" := (tm_app t1 t2) (at level 40) : SystemF_scope.
  Notation "'Λ' body" := (tm_tab body) (at level 45) : SystemF_scope.
  Notation "t1 @@ t2" := (tm_tap t1 t2) (at level 40) : SystemF_scope.

  (** *** Coercions from variables to leaves *)
  Coercion Fr : atom >-> leaf.
  Coercion Bd : nat >-> leaf.

  (** *** Coercions from leaves to term expressions *)
  Definition tm_var_ : leaf -> term leaf := @tm_var leaf.
  Coercion tm_var_ : leaf >-> term.

  (** *** Coercions from leaves to type expressions *)
  Definition c_base_type: base_typ -> typ leaf := @ty_c leaf.
  Definition c_leaf_type : leaf -> typ leaf := @ty_v leaf.
  Coercion c_base_type : base_typ >-> typ.
  Coercion c_leaf_type : leaf >-> typ.

End Notations.

Import Notations.

(** ** Example expressions *)
(******************************************************************************)
Module examples.

  Context
    (x y z : atom)
    (c1 c2 c3 : base_typ).

  (** *** Raw abstract syntax *)
  (** Abstract syntax trees without notations or coercions *)
  (******************************************************************************)

  (** *** Constants and variables *)
  Example typ_1 : typ leaf := ty_v (Fr x).
  Example typ_2 : typ leaf := ty_v (Fr y).
  Example typ_3 : typ leaf := ty_v (Fr z).
  Example typ_4 : typ leaf := ty_v (Bd 0).
  Example typ_5 : typ leaf := ty_v (Bd 1).
  Example typ_6 : typ leaf := ty_v (Bd 2).
  Example typ_7 : typ leaf := ty_c c1.
  Example typ_8 : typ leaf := ty_c c2.

  (** *** Simple types *)
  Example typ_9  : typ leaf := ty_ar (ty_v (Fr x))
                                     (ty_v (Fr x)).
  Example typ_10 : typ leaf := ty_ar (ty_v (Fr x))
                                     (ty_v (Fr y)).
  Example typ_11 : typ leaf := ty_ar (ty_v (Fr x))
                                     (ty_v (Bd 1)).
  Example typ_12 : typ leaf := ty_ar (ty_v (Bd 1))
                                     (ty_c c1).
  Example typ_13 : typ leaf := ty_ar (ty_ar (ty_v (Bd 0))
                                            (ty_v (Fr x)))
                                     (ty_v (Bd 1)).
  Example typ_14 : typ leaf := ty_ar (ty_c c2)
                                     (ty_ar (ty_v (Fr x))
                                            (ty_v (Bd 1))).
  Example typ_15 : typ leaf := ty_ar (ty_ar (ty_v (Bd 2))
                                            (ty_c c1))
                                     (ty_ar (ty_v (Fr y))
                                            (ty_v (Fr x))).
  Example typ_16 : typ leaf := ty_ar (ty_ar (ty_v (Bd 2))
                                            (ty_v (Bd 1)))
                                     (ty_ar (ty_v (Fr y))
                                            (ty_v (Fr x))).

  (** *** Universal types *)
  Example typ_17 : typ leaf := ty_univ (ty_ar (ty_v (Bd 0))
                                              (ty_v (Bd 0))).
  Example typ_18 : typ leaf := ty_univ (ty_ar (ty_ar (ty_v (Bd 2))
                                                     (ty_v (Bd 1)))
                                              (ty_ar (ty_v (Fr y))
                                                     (ty_v (Fr x)))).

  (** *** Printy printed syntax *)
  (******************************************************************************)
  Module pretty.

    #[local] Open Scope SystemF_scope.

    Compute (0 : typ leaf).
    Compute (x : typ leaf).
    Compute (c1 : typ leaf).

    (** Constants and variables *)
    Example typ_1 : typ leaf := x.
    Example typ_2 : typ leaf := y.
    Example typ_3 : typ leaf := Fr z.
    Example typ_4 : typ leaf := 0.
    Example typ_5 : typ leaf := Bd 1.
    Example typ_6 : typ leaf := 2.
    Example typ_7 : typ leaf := c1.
    Example typ_8 : typ leaf := c2.

    (** Simple types *)
    Example typ_9  : typ leaf := x ⟹ x.
    Example typ_10 : typ leaf := x ⟹ y.

    Goal ((x ⟹ x : typ leaf) = Fr x ⟹ Fr x). reflexivity. Qed.
    Goal ((x ⟹ 1 : typ leaf) = Fr x ⟹ Bd 1). reflexivity. Qed.

    Example typ_11 : typ leaf := x ⟹ 1.
    Example typ_12 : typ leaf := x ⟹ c1.
    Example typ_13 : typ leaf := (x ⟹ 0) ⟹ 1.
    Example typ_14 : typ leaf := c2 ⟹ (x ⟹ 1).

    Goal c2 ⟹ x ⟹ 1 = c2 ⟹ (x ⟹ 1). reflexivity. Qed.

    Example typ_15 : typ leaf := (2 ⟹ c1) ⟹ (y ⟹ x).
    Example typ_16 : typ leaf := (2 ⟹ 1) ⟹ (y ⟹ x).

    (** Universal types *)
    Example typ_17 : typ leaf := ∀ (0 ⟹ 0).
    Goal ∀ (0 ⟹ 0) = ∀ 0 ⟹ 0. reflexivity. Qed.

    Example typ_18 : typ leaf := ∀ (2 ⟹ 1) ⟹ (y ⟹ x).
    Goal ∀ (2 ⟹ 1) ⟹ (y ⟹ x) = ∀ ((2 ⟹ 1) ⟹ (y ⟹ x)). reflexivity. Qed.

    Example typ_19 : typ leaf := (∀ 2 ⟹ 1) ⟹ (y ⟹ x).
    Example typ_20 : typ leaf := (2 ⟹ 1) ⟹ ∀ y ⟹ x.

  End pretty.

  Example term_1 : term leaf := tm_var (Fr x).
  Example term_2 : term leaf := tm_var (Bd 0).
  Example term_3 : term leaf := tm_app term_1 term_2.
  Example term_4 : term leaf := tm_app term_3 term_3.

  (** Identity function on type [c1]. *)
  Example term_5 : term leaf := tm_abs (ty_c c1) (tm_var (Bd 0)).
  Example term_6 : term leaf := tm_app term_5 term_3.

  (** Polymorphic identity function. *)
  Example term_7 : term leaf := tm_tab (tm_abs (ty_v (Bd 0))(tm_var (Bd 0))).

  (** Instantiate identity at <<c1>> *)
  Example term_8 : term leaf := tm_tap term_7 c1.

  #[local] Open Scope SystemF_scope.

  Example term_9 : term leaf := (Λ λ 0 ⋅ 0).

End examples.

(** ** <<binddt>> operations *)
(******************************************************************************)
Section operations.

  Context
    (F : Type -> Type)
    `{Applicative F}
    {A B : Type}.

  Fixpoint bind_type (f : forall (k : K), list K2 * A -> F (SystemF k B)) (t : typ A) : F (typ B) :=
    match t with
    | ty_c t =>
      pure F (ty_c t)
    | ty_v a =>
      f KType (nil, a)
    | ty_ar t1 t2 =>
      pure F (ty_ar) <⋆> (bind_type f t1) <⋆> (bind_type f t2)
    | ty_univ body =>
      pure F (ty_univ) <⋆> (bind_type (fun k => prepromote [KType] (f k)) body)
    end.

  Fixpoint bind_term (f : forall (k : K), list K2 * A -> F (SystemF k B)) (t : term A) : F (term B) :=
    match t with
    | tm_var a =>
      f KTerm (nil, a)
    | tm_abs ty body =>
      pure F (tm_abs)
           <⋆> bind_type (fun k => f k) ty
           <⋆> bind_term (fun k => f k ∘ incr [KTerm]) body
    | tm_app t1 t2 =>
      pure F tm_app <⋆> bind_term f t1 <⋆> bind_term f t2
    | tm_tab body =>
      pure F tm_tab <⋆> (bind_term (fun k => f k ∘ incr [KType]) body)
    | tm_tap t1 ty =>
      pure F tm_tap <⋆> bind_term f t1 <⋆> bind_type f ty
    end.

End operations.

#[export] Instance MReturn_SystemF : MReturn SystemF :=
  fun A k => match k with
          | KType => ty_v
          | KTerm => tm_var
          end.

#[export] Instance MBind_type : MBind (list K2) SystemF typ := @bind_type.
#[export] Instance MBind_term : MBind (list K2) SystemF term := @bind_term.
#[export] Instance MBind_SystemF : forall k, MBind (list K2) SystemF (SystemF k) :=
  ltac:(intros [|]; typeclasses eauto).

(** ** Example computations *)
(******************************************************************************)
Section example_computations.

  Open Scope SystemF_scope.

  Context
    (x y z : atom)
    (c1 c2 c3 : base_typ).

  (** ** Demo of opening operation *)
  Goal open (T := SystemF) typ KType (Fr x) (Bd 0) = Fr x. reflexivity. Qed.
  Goal open typ KType (Fr x) (Bd 1) = Bd 0. reflexivity. Qed.
  Goal open typ KType (Fr x) (Fr x) = Fr x. reflexivity. Qed.
  Goal open typ KType (Fr x) (Fr y) = Fr y. reflexivity. Qed.
  Goal open typ KType (Fr y) (Fr x) = Fr x. reflexivity. Qed.
  Goal open typ KType (Fr y) (Fr y) = Fr y. reflexivity. Qed.
  Goal open typ KType (Fr x) (∀ Bd 0) = (∀ (Bd 0)). reflexivity. Qed.
  Goal open typ KType (Fr x) (∀ Bd 1) = (∀ (Fr x)). reflexivity. Qed.
  Goal open typ KType (Fr x) (∀ (Bd 1 ⟹ Bd 0)) = (∀ Fr x ⟹ Bd 0). reflexivity. Qed.
  Goal open typ KType (Fr x) (∀ Bd 1 ⟹ Bd 2) = (∀ Fr x ⟹ Bd 1). reflexivity. Qed.

End example_computations.

(** * Proofs of the DTM axioms *)
(******************************************************************************)

(** ** Helper lemmas for proving DTM axioms *)
(******************************************************************************)
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

Arguments compose_dtm_incr {W}%type_scope {T}%function_scope {H}%function_scope {mn_op mn_unit}
  {G}%function_scope {H0 H1 H2} {F}%function_scope {H4 H5 H6 Monoid0} {A B C}%type_scope (_
  _)%function_scope _.

(** ** <<mbinddt_mret>> *)
(******************************************************************************)
Lemma mbinddt_mret_typ : forall (A : Type),
    mbinddt typ (fun A => A) (fun k => mret SystemF k ∘ extract (list K2 ×)) = @id (typ A).
Proof.
  intros. ext t. unfold id. induction t.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - cbn. fequal.
    + apply IHt1.
    + apply IHt2.
  - cbn. fequal.
    unfold prepromote.
    rewrite <- mbinddt_inst_law1_case12.
    apply IHt.
Qed.

Lemma mbinddt_mret_term : forall (A : Type),
    mbinddt term (fun A => A) (fun k => mret SystemF k ∘ extract (list K2 ×)) = @id (term A).
Proof.
  intros. ext t. unfold id. induction t.
  - easy.
  - cbn. fequal.
    + change (bind_type ?F ?f) with (mbinddt typ F f).
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

(** ** <<mbinddt_mbinddt>> *)
(******************************************************************************)
Lemma mbinddt_mbinddt_typ :
  forall (F : Type -> Type)
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
  forall (F : Type -> Type)
    (G : Type -> Type)
    `{Applicative F}
    `{Applicative G}
    `(g : forall k, list K2 * B -> G (SystemF k C))
    `(f : forall k, list K2 * A -> F (SystemF k B)),
    fmap F (mbinddt term G g) ∘ mbinddt term F f =
    mbinddt term (F ∘ G) (g ⋆dtm f).
Proof.
  intros. ext t. generalize dependent f. generalize dependent g.
  unfold compose at 1. induction t; intros g f.
  - cbn.
    change (MBind_term ?G H3 H4 H5 ?A ?B) with (mbinddt term G (A := A) (B := B)).
    fequal. fequal. now ext k [w a].
  - cbn.
    change (bind_type ?F ?f) with (mbinddt typ F f).
    setoid_rewrite compose_dtm_incr.
    rewrite <- IHt.
    rewrite <- (mbinddt_mbinddt_typ F G).
    unfold compose at 6.
    do 2 rewrite (ap_compose3 G F).
    unfold compose.
    do 2 rewrite <- (ap7 (G := F)).
    unfold_ops @Pure_compose.
    rewrite (app_pure_natural F).
    do 4 rewrite ap6.
    compose near ((pure F (ap G (pure G (@tm_abs C))))).
    rewrite (fun_fmap_fmap F).
    do 3 rewrite (app_pure_natural F).
    reflexivity.
  - cbn.
    rewrite <- IHt1.
    rewrite <- IHt2.
    do 2 rewrite (ap_compose3 G F).
    do 2 rewrite <- (ap7 (G := F)).
    do 4 rewrite ap6.
    compose near (pure (F ∘ G) (@tm_app C)).
    rewrite (fun_fmap_fmap F).
    compose near (pure (F ∘ G) (@tm_app C)).
    rewrite (fun_fmap_fmap F).
    compose near (pure (F ∘ G) (@tm_app C)).
    rewrite (fun_fmap_fmap F).
    unfold_ops @Pure_compose.
    do 2 rewrite (app_pure_natural F).
    reflexivity.
  - cbn.
    setoid_rewrite compose_dtm_incr.
    rewrite <- IHt.
    rewrite (ap_compose3 G F).
    rewrite <- (ap7 (G := F)).
    rewrite ap6.
    unfold_ops @Pure_compose.
    do 3 rewrite (app_pure_natural F).
    reflexivity.
  - cbn.
    rewrite <- IHt.
    rewrite <- (mbinddt_mbinddt_typ F G).
    unfold compose at 4.
    do 2 rewrite (ap_compose3 G F).
    repeat rewrite <- (ap7 (G := F)).
    change (bind_type ?F ?f) with (mbinddt typ F f).
    do 4 rewrite ap6.
    compose near (pure (F ∘ G) (@tm_tap C)).
    rewrite (fun_fmap_fmap F).
    compose near (pure (F ∘ G) (@tm_tap C)).
    rewrite (fun_fmap_fmap F).
    compose near (pure (F ∘ G) (@tm_tap C)).
    rewrite (fun_fmap_fmap F).
    unfold_ops @Pure_compose.
    rewrite (app_pure_natural F).
    rewrite (app_pure_natural F).
    reflexivity.
Qed.

(** ** <<mbinddt_morphism>> *)
(******************************************************************************)

#[local] Set Keyed Unification.

Lemma mbinddt_morphism_typ :
  forall (F : Type -> Type)
    (G : Type -> Type)
    `{ApplicativeMorphism F G ϕ}
    `(f : forall k, list K2 * A -> F (SystemF k B)),
    ϕ (typ B) ∘ mbinddt typ F f =
    mbinddt typ G (fun k => ϕ (SystemF k B) ∘ f k).
Proof.
  intros. ext t. generalize dependent f. unfold compose. induction t; intro f.
  - cbn. rewrite (appmor_pure F G). reflexivity.
  - reflexivity.
  - cbn.
    rewrite <- IHt1. clear IHt1.
    rewrite <- IHt2. clear IHt2.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite (appmor_pure F G).
    reflexivity.
  - cbn.
    rewrite <- IHt. clear IHt.
    rewrite ap_morphism_1.
    rewrite (appmor_pure F G).
    reflexivity.
Qed.

Lemma mbinddt_morphism_term :
  forall (F : Type -> Type)
    (G : Type -> Type)
    `{ApplicativeMorphism F G ϕ}
    `(f : forall k, list K2 * A -> F (SystemF k B)),
    ϕ (term B) ∘ mbinddt term F f =
    mbinddt term G (fun k => ϕ (SystemF k B) ∘ f k).
Proof.
  intros. ext t. generalize dependent f. unfold compose. induction t; intro f.
  - reflexivity.
  - cbn.
    rewrite <- IHt. clear IHt.
    do 2 rewrite ap_morphism_1.
    rewrite (appmor_pure F G).
    change (bind_type ?F ?f) with (mbinddt typ F f).
    compose near t on left.
    rewrite (mbinddt_morphism_typ F G).
    reflexivity.
  - cbn.
    rewrite <- IHt1. clear IHt1.
    rewrite <- IHt2. clear IHt2.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite (appmor_pure F G).
    reflexivity.
  - cbn.
    rewrite <- IHt. clear IHt.
    rewrite ap_morphism_1.
    rewrite (appmor_pure F G).
    reflexivity.
  - cbn.
    rewrite <- IHt. clear IHt.
    do 2 rewrite ap_morphism_1.
    rewrite (appmor_pure F G).
    change (bind_type ?F ?f) with (mbinddt typ F f).
    compose near t0 on left.
    rewrite (mbinddt_morphism_typ F G).
    reflexivity.
Qed.

#[local] Unset Keyed Unification.

(** ** <<mbinddt_comp_mret>> *)
(******************************************************************************)
Lemma mbinddt_comp_mret_typ :
  forall (F : Type -> Type)
    `{Applicative F}
    `(f : forall k, list K2 * A -> F (SystemF k B)),
    mbinddt typ F f ∘ mret SystemF KType = f KType ∘ pair nil.
Proof.
  reflexivity.
Qed.

Lemma mbinddt_comp_mret_term :
  forall (F : Type -> Type)
    `{Applicative F}
    `(f : forall k, list K2 * A -> F (SystemF k B)),
    mbinddt term F f ∘ mret SystemF KTerm = f KTerm ∘ pair nil.
Proof.
  reflexivity.
Qed.

Corollary mbinddt_comp_mret_F :
  forall k F `{Applicative F}
    `(f : forall k, (list K2) * A -> F (SystemF k B)),
    mbinddt (W := list K2) (T := SystemF) (SystemF k) F f ∘ mret SystemF k = (fun a => f k (Ƶ, a)).
Proof.
  intro k. destruct k.
  - apply mbinddt_comp_mret_typ.
  - apply mbinddt_comp_mret_term.
Qed.

(** ** <<DTPreModule>> instances *)
(******************************************************************************)
#[export] Instance DTP_typ: DTPreModule (list K2) typ SystemF :=
  {| dtp_mbinddt_mret := @mbinddt_mret_typ;
     dtp_mbinddt_mbinddt := @mbinddt_mbinddt_typ;
     dtp_mbinddt_morphism := @mbinddt_morphism_typ;
  |}.

#[export] Instance DTP_term: DTPreModule (list K2) term SystemF :=
  {| dtp_mbinddt_mret := @mbinddt_mret_term;
     dtp_mbinddt_mbinddt := @mbinddt_mbinddt_term;
     dtp_mbinddt_morphism := @mbinddt_morphism_term;
  |}.

#[export] Instance: forall k, DTPreModule (list K2) (SystemF k) SystemF :=
  fun k => match k with
        | KType => DTP_typ
        | KTerm => DTP_term
        end.

#[export] Instance: DTM (list K2) SystemF :=
  {| dtm_mbinddt_comp_mret := mbinddt_comp_mret_F;
  |}.

(** * System F type system and operational rules *)
(******************************************************************************)
Reserved Notation "Δ ; Γ ⊢ t : τ" (at level 90, t at level 99).

Import Tealeaves.Classes.Algebraic.Setlike.Functor.Notations.
Export LN.AtomSet.Notations.
Export LN.AssocList.Notations.

(** ** Contexts and well-formedness predicates *)
(******************************************************************************)

(** *** Context of type variables *)
Definition kind_ctx := alist unit.

(** *** Context of term variables *)
Definition type_ctx := alist (typ leaf).

(** *** Well-formedness for kinding contexts *)
(** A kinding context is well-formed when its keys, i.e. type
    variables, are unique. *)
Definition ok_kind_ctx : kind_ctx -> Prop := uniq.

(** *** Well-formedness of type expressions in a kinding context *)
(** A type is well-formed in a kinding context <<Δ>> when all of its
    type variables appear in Δ and the type is locally closed. *)
Definition ok_type : kind_ctx -> typ leaf -> Prop :=
  fun Δ τ => scoped typ KType τ (domset Δ) /\ locally_closed typ KType τ.

(** *** Well-formedness for typing contexts *)
(** A typing context <<Γ>> is well-formed in kinding context <<Δ>>
    when the keys of <<Γ>> (i.e. term variables) are unique, and each
    associated type is itself well-formed in context <<Δ>>. *)
Definition ok_type_ctx : kind_ctx -> type_ctx -> Prop :=
  fun Δ Γ => uniq Γ /\ forall τ, τ ∈ range Γ -> ok_type Δ τ.

(** *** Well-formedness of term expressions in context *)
(** A term <<t>> is well-formed in contexts <<Δ>> and <<Γ>> when its
    type variables are declared in <<Δ>>, its term variables are
    declared in <<Γ>>, and it is locally closed with respect to both
    kinds of variables. *)
Definition ok_term : kind_ctx -> type_ctx -> term leaf -> Prop :=
  fun Δ Γ t => scoped term KType t (domset Δ) /\
            scoped term KTerm t (domset Γ) /\
            locally_closed term KTerm t /\
            locally_closed term KType t.

(** ** Typing judgments *)
(******************************************************************************)
Implicit Types (Δ : kind_ctx) (Γ : type_ctx) (τ : typ leaf).

Inductive Judgment : kind_ctx -> type_ctx -> term leaf -> typ leaf -> Prop :=
| j_var :
    forall Δ Γ x τ,
      ok_kind_ctx Δ ->
      ok_type_ctx Δ Γ ->
      (x, τ) ∈ Γ ->
      (Δ ; Γ ⊢ tm_var (Fr x) : τ)
| j_abs :
    forall Δ Γ L t τ1 τ2,
      (forall x, ~ x ∈@ L  ->
            Δ ; Γ ++ x ~ τ1 ⊢ open term KTerm (tm_var (Fr x)) t : τ2) ->
      (Δ ; Γ ⊢ tm_abs τ1 t : ty_ar τ1 τ2)
| j_app :
    forall Δ Γ t1 t2 τ1 τ2,
      (Δ ; Γ ⊢ t1 : ty_ar τ1 τ2) ->
      (Δ ; Γ ⊢ t2 : τ1) ->
      (Δ ; Γ ⊢ tm_app t1 t2 : τ2)
| j_univ :
    forall Δ Γ L τ t,
      (forall x, ~ x ∈@ L ->
            Δ ++ x ~ tt ; Γ ⊢ open term KType (ty_v (Fr x)) t
                          : open typ KType (ty_v (Fr x)) τ) ->
      (Δ ; Γ ⊢ tm_tab t : ty_univ τ)
| j_inst :
    forall Δ Γ t τ1 τ2,
      ok_type Δ τ1 ->
      (Δ ; Γ ⊢ t : ty_univ τ2) ->
      (Δ ; Γ ⊢ tm_tap t τ1 : open typ KType τ1 τ2)
where "Δ ; Γ ⊢ t : τ" := (Judgment Δ Γ t τ).

(** ** Values and reduction rules *)
(******************************************************************************)
Inductive value : term leaf -> Prop :=
| val_abs : forall T t, value (tm_abs T t)
| val_tab : forall t, value (tm_tab t).

Inductive red : term leaf -> term leaf -> Prop :=
| red_app_l : forall t1 t1' t2,
    red t1 t1' ->
    red (tm_app t1 t2) (tm_app t1' t2)
| red_app_r : forall t1 t2 t2',
    value t1 ->
    red t2 t2' ->
    red (tm_app t1 t2) (tm_app t1 t2')
| red_abs : forall T t1 t2,
    value t2 ->
    red (tm_app (tm_abs T t1) t2) (open term KTerm t2 t1)
| red_tapl : forall t t' T,
    red t t' ->
    red (tm_tap t T) (tm_tap t' T)
| red_tab : forall T t,
    red (tm_tap (tm_tab t) T) (open term KType T t).

From Tealeaves Require Import
     LN.Multisorted.Theory.

Definition preservation := forall t t' τ,
    (nil ; nil ⊢ t : τ) ->
    red t t' ->
    (nil ; nil ⊢ t' : τ).

Definition progress := forall t τ,
    (nil ; nil ⊢ t : τ) ->
    value t \/ exists t', red t t'.

(*
(** ** Example: Typing the polymorphic identity *)
(******************************************************************************)
Example polymorphic_identity_function :
  (nil ; nil ⊢ (Λ λ 0 ⋅ 0) : (∀ 0 ⟹ 0)).
Proof.
  apply j_univ with (L := ∅). introv _.
  cbn. apply j_abs with (L := ∅).
  - introv _. apply j_var.
    + auto with sysf_ctx.
    + simpl_alist. apply ok_tmv_tm_one.
      unfold ok_type, scoped_env, scoped.
      autorewrite with sysf_rw tea_rw_dom.
      split; [fsetdec | apply lc_ty_ty_Fr].
    + simpl_alist. now autorewrite with tea_list.
Qed.
*)
