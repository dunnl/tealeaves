(*|
############################################################
Adding a letrec to untyped lambda calculus
############################################################

.. contents:: Table of Contents
   :depth: 2

============================
Imports and setup
============================

|*)
From Tealeaves Require Import
  Functors.List
  Backends.LN.Atom
  Classes.EqDec_eq
  Classes.Traversable.Functor
  Categories.TypeFamilies
  Functors.Writer
  Multisorted.Classes.DTM.

Import Setlike.Functor.Notations.
Import Traversable.Functor.ToKleisli.

Import Tealeaves.Classes.Monoid.Notations.
Import Tealeaves.Data.Product.Notations.
Import Tealeaves.Classes.Applicative.Notations.
Import Multisorted.Classes.DTM.Notations.
Import List.ListNotations.

#[local] Generalizable Variables F G A B C ϕ.

(*|
============================
Language definition
============================
|*)
#[export] Instance Unit_eq : EqDec unit eq.
Proof.
  change (forall x y : unit, {x = y} + {x <> y}).
  decide equality.
Defined.

#[export] Instance Unit : Index := {| K := unit |}.

Inductive term (v : Type) :=
| tvar : v -> term v
| app : term v -> term v -> term v
| lam : atom -> term v -> term v
| letin : atom -> term v -> term v -> term v.

Definition T (_ : unit) (v : Type) : Type := @term v.

(*|
========================================
Definition of `binddt` and `return`
========================================
|*)

#[export] Instance: MReturn T := fun A k => @tvar A.

Fixpoint binddt_term (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : forall k, list atom * v1 -> G (T k v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar _ v => f tt (nil, v)
  | app _ t1 t2 =>
      pure G (@app v2) <⋆> binddt_term G f t1 <⋆> binddt_term G f t2
  | lam _ name body =>
      pure G (@lam v2 name) <⋆> binddt_term G (fun k => f k ∘ incr [name]) body
  | letin _ name def body =>
      pure G (@letin v2 name) <⋆> binddt_term G f def <⋆> binddt_term G (fun k => f k ∘ incr [name]) body
  end.

#[export] Instance MBind_term : MBind (list atom) T term := @binddt_term.

#[export] Instance MBind_T : forall k, MBind (list atom) T (T k) :=
  ltac:(intros []; typeclasses eauto).

(*|
Helpers
|*)

Section helpers.

  Context
    `{Applicative F}
    `{Applicative G}
      {v1 v2 v3 : Type}
      (f : forall k, nat * v1 -> F (T k v2))
      (g : forall k, nat * v2 -> G (T k v3)).

End helpers.

(*|
========================================
The Kleisli axioms of DTMs
========================================
|*)

Section laws.

  Ltac rewrite_with_bind_hyp :=
    match goal with
    | H : context[mbinddt] |- _ => rewrite H
    end.

  Ltac induction_on_term :=
    match goal with
    | t : term ?v |- _ => induction t
    end.

  Ltac dtm_setup :=
    intros; ext t; unfold id; induction_on_term; cbn.

(*|
-----------------------------
Law 1
-----------------------------
|*)

  Lemma mbinddt_comp_mret_term :
    forall (F : Type -> Type)
      `{Applicative F}
      `(f : forall k, list atom * A -> F (T k B)),
      mbinddt term F f ∘ mret T tt = f tt ∘ pair nil.
  Proof.
    reflexivity.
  Qed.

  Corollary mbinddt_comp_mret_T :
    forall k F `{Applicative F}
      `(f : forall k, list atom * A -> F (T k B)),
      mbinddt (W := (list atom)) (T := T) (T k) F f ∘ mret T k = (fun a => f k (Ƶ, a)).
  Proof.
    intros []. apply mbinddt_comp_mret_term.
  Qed.

(*|
-----------------------------
Law 2
-----------------------------
|*)

  Generalizable Variable M.

  Lemma dtm2_helper : forall (x : atom) (A : Type),
      (fun k : unit => mret T k ∘ extract (A:=A) (prod (list atom)) ∘ incr [x]) =
        (fun k : unit => mret T k ∘ extract (prod (list atom))).
  Proof.
    intros. ext k. reassociate ->. now rewrite (extract_incr).
  Qed.

  Lemma mbinddt_mret_term : forall (A : Type),
      mbinddt term (fun A => A) (fun k => mret T k ∘ extract ((list atom) ×)) = @id (term A).
  Proof.
    intros. ext t. unfold id. induction t.
    - cbn. reflexivity.
    - cbn. fequal.
      + assumption.
      + assumption.
    - cbn. fequal.
      * rewrite dtm2_helper. auto.
    - cbn. fequal.
      * auto.
      * rewrite dtm2_helper. auto.
  Qed.

  Corollary mbinddt_mret_T :
    forall k A, mbinddt (T k) (fun A => A) (fun k => mret T k ∘ extract ((list atom) ×)) = @id (T k A).
  Proof.
    intros [] A. apply mbinddt_mret_term.
  Qed.

  Ltac solve_dtm2_case :=
    fequal; try rewrite dtm2_helper; auto.

  Lemma mbinddt_mret_term_automated : forall (A : Type),
      mbinddt term (fun A => A) (fun k => mret T k ∘ extract ((list atom) ×)) = @id (term A).
  Proof.
    dtm_setup; solve_dtm2_case.
  Qed.

(*|
-----------------------------
Law 3
-----------------------------
|*)

  (*
  Corollary ap6_simple {G} `{Applicative G} {A B C} : forall (g : B -> C) (f : A -> B) (a : G A) ,
      fmap G g (pure G f <⋆> a) = pure G (compose g f) <⋆> a.
  Proof.
    intros. rewrite fmap_to_ap.
    rewrite <- ap4. now rewrite 2(ap2).
  Qed.
   *)

  Ltac dtm3_lhs_step G1 :=
    repeat rewrite fmap_ap; (* Bring LHS <<fmap>> up to the constructor *)
    rewrite (app_pure_natural G1). (* Fuse <<fmap>> and the <<pure (constructor)>> *)

  Ltac dtm3_rhs_step G2 G1 :=
    (rewrite_strat innermost (terms (ap_compose2 G2 G1)));
    repeat rewrite fmap_ap;
    rewrite (app_pure_natural G1);
    rewrite <- ap_fmap;
    repeat rewrite fmap_ap;
    rewrite (app_pure_natural G1).

  Lemma mbinddt_mbinddt_term :
    forall (F : Type -> Type)
      (G : Type -> Type)
      `{Applicative F}
      `{Applicative G}
      `(g : forall k, list atom * B -> G (T k C))
      `(f : forall k, list atom * A -> F (T k B)),
      (fmap F (mbinddt term G g) ∘ mbinddt term F f) =
        mbinddt term (F ∘ G) (compose_dtm (T := T) g f).
  Proof.
    intros. ext t. unfold compose at 1.
    generalize dependent g.
    generalize dependent f.
    induction t; intros f g.
    - cbn. change [] with (Ƶ : list atom). now rewrite incr_zero.
    - cbn.
      (* left side *)
      do 2 rewrite fmap_ap.
      rewrite (app_pure_natural F).
      (* right side, IH *)
      rewrite <- IHt1.
      rewrite <- IHt2.
      (* right side, constructor *)
      unfold_ops @Pure_compose.
      (* right side, first argument *)
      rewrite_strat innermost (terms (ap_compose2 G F)).
      rewrite (app_pure_natural F).
      rewrite <- ap_fmap.
      rewrite (app_pure_natural F).
      (* right side, outer *)
      rewrite_strat innermost (terms (ap_compose2 G F)).
      rewrite fmap_ap.
      rewrite (app_pure_natural F).
      rewrite <- ap_fmap.
      rewrite fmap_ap.
      rewrite (app_pure_natural F).
      (* Done *)
      reflexivity.
    - cbn.
      (* left side *)
      rewrite fmap_ap.
      rewrite (app_pure_natural F).
      (* right side, IH *)
      rewrite (compose_dtm_incr (ix := Unit) (list atom) T g f).
      rewrite <- IHt.
      (* right side, constructor *)
      unfold_ops @Pure_compose.
      (* right side, first argument *)
      rewrite_strat innermost (terms (ap_compose2 G F)).
      rewrite (app_pure_natural F).
      rewrite <- ap_fmap.
      rewrite (app_pure_natural F).
      (* Done *)
      reflexivity.
    - cbn.
      (* left side *)
      do 2 rewrite fmap_ap.
      rewrite (app_pure_natural F).
      (* right side, IH *)
      rewrite (compose_dtm_incr (ix := Unit) (list atom) T g f).
      rewrite <- IHt1.
      rewrite <- IHt2.
      (* right side, constructor *)
      unfold_ops @Pure_compose.
      (* right side, first argument *)
      rewrite_strat innermost (terms (ap_compose2 G F)).
      rewrite (app_pure_natural F).
      rewrite <- ap_fmap.
      rewrite (app_pure_natural F).
      (* right side, second argument *)
      rewrite_strat innermost (terms (ap_compose2 G F)).
      rewrite fmap_ap.
      rewrite (app_pure_natural F).
      rewrite <- ap_fmap.
      rewrite fmap_ap.
      rewrite (app_pure_natural F).
      (* Done *)
      reflexivity.
  Qed.

(*|
------------------------
Law 4
------------------------

|*)
  Section law4.

    Context
      (F : Type -> Type)
      (G : Type -> Type)
     `{ApplicativeMorphism F G ϕ}.

    Ltac invert_applicative :=
      match goal with
        | hyp : ApplicativeMorphism F G ϕ |- _ => inversion hyp
      end.

    Set Keyed Unification.
    Lemma mbinddt_morphism_term :
      forall `(f : forall k, list atom * A -> F (T k B)),
        ϕ (term B) ∘ mbinddt term F f =
          mbinddt term G (fun k => ϕ (T k B) ∘ f k).
    Proof.
      intros. ext t. unfold compose at 1.
      generalize dependent f.
      induction t; cbn; intro f.
      - reflexivity.
      - (* left side *)
        repeat rewrite ap_morphism_1.
        rewrite (appmor_pure F G).
        (* right side *)
        rewrite <- IHt1.
        rewrite <- IHt2.
        (* Done *)
        reflexivity.
      - (* left side *)
        repeat rewrite ap_morphism_1.
        rewrite (appmor_pure F G).
        (* right side *)
        rewrite <- IHt.
        (* Done *)
        reflexivity.
      - (* left side *)
        repeat rewrite ap_morphism_1.
        rewrite (appmor_pure F G).
        (* right side *)
        rewrite <- IHt1.
        rewrite <- IHt2.
        (* Done *)
        reflexivity.
    Qed.
    Unset Keyed Unification.

  End law4.

End laws.
(*|
-------------------------
Multisorted DTM instance
-------------------------
|*)

#[export] Instance DTP_term: DTPreModule (list atom) term T :=
  {| dtp_mbinddt_mret := @mbinddt_mret_term;
     dtp_mbinddt_mbinddt := @mbinddt_mbinddt_term;
     dtp_mbinddt_morphism := @mbinddt_morphism_term;
  |}.

#[export] Instance: forall k : unit, DTPreModule (list atom) (T k) T :=
  fun k => match k with tt => DTP_term end.

#[export] Instance: DTM (list atom) T :=
  {| dtm_mbinddt_comp_mret := mbinddt_comp_mret_T;
  |}.
