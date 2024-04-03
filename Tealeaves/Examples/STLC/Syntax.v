(*|
############################################################
Formalizing STLC with Tealeaves
############################################################
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Kleisli presentation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

This file gives a tutorial on proving the decorated traversable monad
laws the for the syntax of the simply-typed lambda calculus (STLC).

.. contents:: Table of Contents
   :depth: 2

============================
Imports and setup
============================

Since we are using the Kleisli typeclass hierarchy, we import modules under
the namespaces ``Classes.Kleisli`` and ``Theory.Kleisli.``
|*)
From Tealeaves Require Export
  Backends.LN
  Misc.NaturalNumbers
  Functors.List
  Theory.DecoratedTraversableMonad
  Examples.Debug.

Export Monoid.Notations. (* Ƶ and ● *)
Export Kleisli.DecoratedTraversableMonad.Notations. (* ∈d *)
Export Misc.Subset.Notations. (* ∪ *)
Export Applicative.Notations. (* <⋆> *)
Export List.ListNotations. (* [] :: *)
Export LN.Notations. (* operations *)
Export LN.AtomSet.Notations.
Export LN.AssocList.Notations. (* one, ~ *)
Export Product.Notations. (* × *)
Export ContainerFunctor.Notations. (* ∈ *)
Export DecoratedContainerFunctor.Notations. (* ∈d *)

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.

Open Scope set_scope.

(*|
========================================
Simplification support
========================================
|*)

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

(*
Lemma free_to_foldMap: forall t,
    free t = foldMap free_loc t.
Proof.
  reflexivity.
Qed.
*)

Lemma eq_pair_preincr: forall (n: nat) {A} (a: A),
    eq (S n, a) ⦿ 1 = eq (n, a).
Proof.
  intros.
  ext [n' a'].
  unfold preincr, compose, incr.
  apply propositional_extensionality.
  rewrite pair_equal_spec.
  rewrite pair_equal_spec.
  intuition.
Qed.

Ltac rewrite_core_ops_to_binddt :=
  match goal with
  | |- context[bind ?f ?t] =>
      debug "bind_to_binddt";
      progress (rewrite bind_to_binddt)
  | |- context[bindd ?f ?t] =>
      debug "bindd_to_binddt";
      progress (rewrite bindd_to_binddt)
  end.

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
  | |- context[(?f ⦿ Ƶ)] =>
      rewrite (preincr_zero f)
  | |- context[(?f ⦿ ?x)] =>
      let T := type of x in
      change x with (Ƶ:T);
      rewrite preincr_zero
  end.

Ltac simplify_fn_composition :=
  match goal with
  | |- context [id ∘ ?f] =>
      debug "id ∘ f";
      change (id ∘ f) with f
  | |- context [?f ∘ id] =>
      debug "f ∘ id";
      change (f ∘ id) with f
  | |- context [id ?x] =>
      debug "unfold_id";
      change (id x) with x
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
      unfold free
      (*
      rewrite free_to_foldMap
      *)
  | |- context[freeset ?t] =>
      debug "unfold_freeset";
      unfold freeset;
      unfold free
      (*
      rewrite free_to_foldMap
      *)
  | |- context[locally_closed] =>
      idtac "locally_closed_spec";
      rewrite locally_closed_spec
  | |- context[locally_closed_gap] =>
      idtac "locally_closed_gap_spec";
      rewrite locally_closed_gap_spec
  | |- context[is_bound_or_free] =>
      debug "simplify_bound_or_free";
      simplify_is_bound_or_free
  | |- context[subst] =>
      unfold subst
  | |- context[open] =>
      unfold open
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
  | |- context[eq (S ?n, ?a) ⦿ 1] =>
      rewrite eq_pair_preincr
  end.

(* I don't entirely know why this is required. *)
#[export] Typeclasses Transparent Monoid_op.
#[export] Typeclasses Transparent Monoid_unit.

Lemma test_transparency:
  @Applicative (@const Type Type Prop)
    (@Map_const Prop)
    (@Pure_const Prop False)
    (@Mult_const Prop or).
Proof.
  typeclasses eauto.
Qed.


(*|
========================================
Using Tealeaves with STLC
========================================
|*)

Parameter base_typ : Type.

Inductive typ :=
| base : base_typ -> typ
| arr : typ -> typ -> typ.

Coercion base : base_typ >-> typ.

Inductive term (v : Type) :=
| tvar : v -> term v
| lam : typ -> term v -> term v
| app : term v -> term v -> term v.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Module Notations.
  Notation "'λ'" := (lam) (at level 45).
  Notation "[ t1 ]@[ t2 ]" := (app t1 t2) (at level 80).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End Notations.

Import Notations.

Section test_notations.

  Context
    (β : Type)
    (x y z : atom)
    (b : β) (τ : typ).

  Check 1.
  Check (λ τ (tvar (Bd 1))).
  Check (λ τ (tvar (Fr x))).
  Check [λ τ (tvar (Bd 1))]@[tvar (Fr x)].
  Check [λ τ (tvar (Fr x))]@[tvar (Bd 0)].
  Check λ τ ([(tvar (Bd 1))]@[tvar (Fr x)]).
  Check λ τ ([(tvar (Fr x))]@[tvar (Bd 0)]).

End test_notations.

(*|
========================================
Definition of binddt
========================================
|*)
Fixpoint binddt_term (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (term v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar v => f (0, v)
  | lam τ body => pure (lam τ) <⋆> binddt_term (f ⦿ 1) body
  | app t1 t2 => pure (@app v2) <⋆> binddt_term f t1 <⋆> binddt_term f t2
  end.

#[export] Instance Return_STLC: Return term := tvar.
#[export] Instance Binddt_STLC: Binddt nat term term := @binddt_term.

(*|
========================================
Simplification automation
========================================
|*)

#[local] Notation "'P'" := pure.
#[local] Notation "'BD'" := binddt.

(*|
========================================
Simplification support
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

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Helper lemmas for proving the DTM laws
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

These definitional equalities help prove the composition law later.
|*)

Section rw.

  Context
    {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f: nat * v1 -> G (term v2)).

  Definition binddt_term_rw1: forall x,
      BD f (tvar x) = f (0, x) := ltac:(reflexivity).

  Definition binddt_term_rw2: forall τ body,
      binddt f (@lam _ τ body) =
        (P (λ τ) <⋆> BD (f ⦿ 1) body)
    := ltac:(reflexivity).

  Definition binddt_term_rw3: forall t1 t2,
      binddt f (@app _ t1 t2) =
        (P (@app v2) <⋆> BD f t1 <⋆> BD f t2)
    := ltac:(reflexivity).

  Lemma binddt_lam: forall τ,
    BD f ∘ (@lam v1 τ) =
      (precompose (BD (f ⦿ 1)) ∘ ap G ∘ P) (@lam v2 τ).
  Proof.
    reflexivity.
  Qed.

  Lemma binddt_app :
    compose (BD f) ∘ @app v1 =
      (compose (precompose (BD f) ∘ ap G) ∘ precompose (BD f) ∘ ap G ∘ P) (@app v2).
  Proof.
    reflexivity.
  Qed.

End rw.

Ltac simpl_binddt_term :=
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

Ltac simplify_pass1 :=
  first [ simplify_locally_nameless_top_level
        | rewrite_core_ops_to_binddt
        | rewrite_ops_to_binddt
        | simpl_binddt_term
    ].

Ltac simplify_pass2 :=
  first [ simplify_locally_nameless_leaves
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

Ltac dtm_law_pass :=
  match goal with
  | |- context[kc7 ?g ?f] =>
      unfold kc7
  end.

Ltac handle_atoms :=
  match goal with
  | |- context[atoms] =>
      progress (autorewrite with tea_rw_atoms)
  | |- context[atoms (?l1 ● ?l2)] =>
      unfold_ops @Monoid_op_list;
      progress (autorewrite with tea_rw_atoms)
  end.

Ltac introduce_induction :=
  let t := fresh "t" in
  ext t; induction t.

Ltac derive_dtm_law :=
  intros;
  try introduce_induction;
  repeat simpl_binddt_term;
  repeat simplify_pass2;
  fequal; (trivial || reflexivity).

(*|
========================================
An overview of the DTM axioms
========================================
|*)

Section laws.

  (* Generalize over (Coq) variables used for object-level variables
   and symbols for applicative homomorphisms. *)
  Generalizable Variables v ϕ.

  Ltac rewrite_with_bind_hyp :=
    match goal with
    | H : context[binddt] |- _ => rewrite H
    end.

  Ltac induction_on_term :=
    match goal with
    | t : term ?v |- _ => induction t
    end.

  Ltac dtm_setup :=
    intros; ext t; unfold id; induction_on_term; cbn.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Composition with unit (left unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The "composition with unit" law (or left unit law) establishes that
the atomic expression `ret term v`

1. consists just of variable `v`
2. inside an empty binding context

In this law, `ret (list β ×)` is the operation which lifts any `v`
into an empty binding context to get `([], v)`. A simpler way of
writing the left unit law is then

`binddt f (ret term v) = f ([], v)`

The proof of this rule ought to follow merely from the definitions of
`binddt` and `ret`.  In the course of proofs about `binddt f t` by
induction of the syntax of expression `t`, the left unit law acts as
a base case.

.. coq::
   :name: dtm1
|*)
  Ltac solve_dtm1 :=
    intros; now try ext var.

  Theorem dtm1_stlc:
    forall `{Applicative G} (A B : Type),
       forall f : nat * A -> G (term B),
         binddt f ∘ ret  = f ∘ ret (T := (nat ×)).
  Proof.
    reflexivity.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Identity law (right unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The identity law (or right unit law) establishes that applying the
substitution rule

`pure F ∘ ret term ∘ extract ((list β) ×)`

to each of the variables in expression `t` acts as the pure effect on
`t`. The substitution rule is the one which at each variable

1. throws away the binding context: `list β * v -> v`
2. coerces the variable into an atomic expression: `v -> term v`
3. and lifts the result into `F` with the `pure` effect: `term v -> F (term v)`

.. coq::
   :name: dtm2
|*)

  Theorem dtm2_stlc: forall A: Type,
      binddt (T := term) (U := term)
        (G := fun A => A) (ret (T := term) ∘ extract (W := (nat ×))) = @id (term A).
  Proof.
    derive_dtm_law.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~
Composition law
~~~~~~~~~~~~~~~~~~~~~~~~

The composition law states the following:

`map F (binddt g) ∘ binddt f = binddt (g ⋆ f)`

The right-hand side may be written more explicitly as

`binddt (fun '(w, x) => map F (binddt (F := G) (g ∘ incr w)) (f (w, x))))`

This law is an analogue of the ordinary monad composition law

`bind g ∘ bind f = bind (bind g ∘ f)`.

Both are loosely of the form

`bind g ∘ bind f = bind (g ∗ f)`

A close comparison shows the rules differ in two respects:

1. The call to `g` in `bind g` is replaced with a call to `(g ∘ incr
   w)` where `w` is the context seen by the function `f`.
2. The call to `binddt (g ∘ incr w)` is wrapped in `map F`. This is
   required to map over the applicative effect of type `F` generated
   by the application of `f`.

.. coq::
   :name: dtm3
|*)


  Ltac dtm3_lhs_step :=
  repeat rewrite map_ap;
  (* Distribute outer <<map>> into the constructor *)
  rewrite app_pure_natural.
  (* Fuse <<map f>> and the <<pure C>> into <<pure (f ∘ C)>> *)

  Ltac dtm3_rhs_kc7_preincr :=
    try match goal with
    | |- context[@preincr _ _ _ ((?G1 ∘ ?G2) ?x)] =>
        (* this step deals with composition blocking
           rewrite kc7_preincr *)
        change ((G1 ∘ G2) x) with (G1 (G2 x))
        end;
    repeat rewrite <- kc7_preincr.

  Ltac dtm3_rhs_invoke_IH :=
    repeat match goal with
      | IH: context[BD (_ ⋆7 _) ?t] |- _ =>
          dtm3_rhs_kc7_preincr;
          rewrite <- IH
      end.

  Ltac dtm3_rhs_applicative_compose :=
      match goal with
      | |- context[ap (?G1 ∘ ?G2)] =>
          (rewrite_strat innermost
             (terms (ap_compose2 G2 G1)));
          (repeat rewrite map_ap);
          (repeat rewrite app_pure_natural)
      end.

  Ltac dtm3_rhs_applicative_map :=
      rewrite <- ap_map;
      repeat rewrite map_ap;
      repeat rewrite app_pure_natural.

  Ltac dtm3_rhs_step :=
      dtm3_rhs_invoke_IH;
      unfold_ops @Pure_compose;
      repeat (dtm3_rhs_applicative_compose;
              dtm3_rhs_applicative_map).

  Theorem dtm3_stlc :
    forall `{Applicative G1} `{Applicative G2},
        forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
          map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
  Proof.
    intros. ext t.
    unfold compose at 1.
    generalize dependent g.
    generalize dependent f.
    induction t; intros f g.
    - repeat simpl_binddt_term.
      dtm_law_pass.
      simplify_pass2.
      reflexivity.
    - repeat simpl_binddt_term.
      dtm3_lhs_step.
      dtm3_rhs_step.
      reflexivity.
    - repeat simpl_binddt_term.
      dtm3_lhs_step.
      dtm3_rhs_step.
      reflexivity.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Applicative homomorphism law
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This law states that `binddt` is parametric with respect to
applicative functors in the sense that it commutes with their
homomorphisms. It is (probably?) a free theorem, so it is not actually
a restriction on implementations of `binddt` (cite Gibbons).


.. coq::
   :name: dtm4
|*)

  Theorem dtm4_stlc :
    forall (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Mult G1) (H3 : Pure G1) (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A), ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : nat * A -> G1 (term B)),
        ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
  Proof.
    intros. ext t.
    inversion H.
    generalize dependent f.
    unfold compose at 1.
    induction t; intro f. (* .unfold *)
    - reflexivity.
    - cbn.
      repeat rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHt.
      reflexivity.
    - cbn.
      repeat rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

  #[export] Instance DTMPre_STLC:
    DecoratedTraversableRightPreModule nat term term :=
    {| kdtm_binddt1 := dtm2_stlc;
      kdtm_binddt2 := @dtm3_stlc;
      kdtm_morph := @dtm4_stlc;
    |}.

  #[export] Instance DTM_STLC:
    DecoratedTraversableMonad nat term :=
    {| kdtm_binddt0 := @dtm1_stlc;
    |}.

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
  #[export] Instance Elements_STLC: Elements term
    := Elements_Traverse.

  #[export] Instance DTMFull_STLC:
    DecoratedTraversableMonadFull nat term
    := DecoratedTraversableMonadFull_DecoratedTraversableMonad nat term.

End laws.

Definition ctx := list (atom * typ).

Reserved Notation "Γ ⊢ t : S" (at level 90, t at level 99).

Inductive Judgment : ctx -> term LN -> typ -> Prop :=
| j_var :
    forall (Γ : ctx) (x : atom) (A : typ),
      uniq Γ ->
      (x, A) ∈ Γ ->
      Γ ⊢ tvar (Fr x) : A
| j_abs :
    forall (L : AtomSet.t) Γ (τ1 τ2 : typ) (t : term LN),
      (forall x : atom, ~ AtomSet.In x L -> Γ ++ x ~ τ1 ⊢ t '(tvar (Fr x)) : τ2) ->
      Γ ⊢ λ τ1 t : τ1 ⟹ τ2
| j_app :
    forall Γ (t1 t2 : term LN) (A B : typ),
      Γ ⊢ t1 : A ⟹ B ->
      Γ ⊢ t2 : A ->
      Γ ⊢ [t1]@[t2] : B
where "Γ ⊢ t : A" := (Judgment Γ t A).
