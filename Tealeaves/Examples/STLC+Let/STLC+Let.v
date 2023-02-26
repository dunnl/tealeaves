(*|
############################################################
Adding let constructor to untyped lambda calculus
############################################################

.. contents:: Table of Contents
   :depth: 2

============================
Imports and setup
============================

|*)
From Tealeaves Require Import
  Categories.TypeFamilies
  Classes.Applicative
  Functors.List
  Data.Natural
  Backends.LN
  Classes.DT.Functor.

Import Setlike.Functor.Notations.

From Tealeaves.Multisorted Require Import
  Classes.DTM.

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
#[export] Instance Keq : EqDec unit eq.
Proof.
  change (forall x y : unit, {x = y} + {x <> y}).
  decide equality.
Defined.

#[export] Instance I1 : Index := {| K := unit |}.

Inductive term (v : Type) :=
| tvar : v -> term v
| letin : atom -> term v -> term v -> term v.

Definition T (k : unit) (v : Type) : Type := term v.

(*|
========================================
Definition of `binddt` and `return`
========================================
|*)

About MReturn.
Print MReturn.
#[program, export] Instance: MReturn T := fun (A : Type) (k : unit) => @tvar A.

Fixpoint binddt_term (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : forall k, list atom * v1 -> G (T k v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar _ v => f tt (nil, v)
  | letin _ name def body => pure G (@letin v2 name)
                       <⋆> binddt_term G f def
                       <⋆> binddt_term G (fun k => f k ∘ incr [name]) body
  end.

#[export] Instance MReturn_SystemF : MReturn T :=
  fun A k => match k with | MkK1 => @tvar A end.

#[export] Instance MBind_term : MBind (list atom) T term := @binddt_term.

#[export] Instance MBind_T : forall k, MBind (list atom) T (T k) :=
  ltac:(intros []; typeclasses eauto).

(*|
Helpers
|*)

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

  Context
    `{Applicative G}
    `{Applicative F}
    `{! Monoid W}
    {A B C : Type}
    (g : forall k, W * B -> G (T k C))
    (f : forall k, W * A -> F (T k B)).


  Locate "_ ⋆dtm _".
  About compose_dtm.
  Search compose_dtm.
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
  {G}%function_scope {H0 H1 H2} {F}%function_scope {H4 H5 H6 Monoid0} {A B C}%type_scope (_ _)%function_scope _.

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

(*|
-----------------------------
Law 1
-----------------------------
|*)

  Lemma mbinddt_comp_mret_term :
    forall (F : Type -> Type)
      `{Applicative F}
      `(f : forall k, (list atom) * A -> F (T k B)),
      mbinddt term F f ∘ mret T MkK1 = f MkK1 ∘ pair nil.
  Proof.
    reflexivity.
  Qed.

  Corollary mbinddt_comp_mret_T :
    forall k F `{Applicative F}
      `(f : forall k, (list atom) * A -> F (T k B)),
      mbinddt (W := (list atom)) (T := T) (T k) F f ∘ mret T k = (fun a => f k (Ƶ, a)).
  Proof.
    intros []. apply mbinddt_comp_mret_term.
  Qed.

(*|
-----------------------------
Law 2
-----------------------------
|*)

  Lemma mbinddt_mret_term : forall (A : Type),
      mbinddt term (fun A => A) (fun k => mret T k ∘ extract ((list atom) ×)) = @id (term A).
  Proof.
    intros. ext t. unfold id. induction t.
    - cbn. reflexivity.
    - cbn. unfold_ops @Pure_I. unfold id.
      fequal.
      + assumption.
      + replace (fun k : K1 => mret (ix := I1) T k ∘ extract (prod (list atom)) ∘ incr [a]) with
          (fun k : K1 => mret (A := A) T k ∘ extract (prod (list atom))).
        * assumption.
        * ext k. reassociate ->. rewrite (extract_incr). reflexivity.
  Qed.

  Corollary mbinddt_mret_T :
    forall k A, mbinddt (T k) (fun A => A) (fun k => mret T k ∘ extract ((list atom) ×)) = @id (T k A).
  Proof.
    intros [] A. apply mbinddt_mret_term.
  Qed.

(*|
-----------------------------
Law 3
-----------------------------
|*)
  Section law3.

  Corollary ap6_simple {G} `{Applicative G} {A B C} : forall (g : B -> C) (f : A -> B) (a : G A) ,
      fmap G g (pure G f <⋆> a) = pure G (compose g f) <⋆> a.
  Proof.
    intros. rewrite fmap_to_ap.
    rewrite <- ap4. now rewrite 2(ap2).
  Qed.

  Lemma mbinddt_mbinddt_term :
    forall
      (F : Type -> Type)
      (G : Type -> Type)
      `{Applicative F}
      `{Applicative G}
      `(g : forall k, list atom * B -> G (T k C))
      `(f : forall k, list atom * A -> F (T k B)),
      (fmap F (mbinddt term G g) ∘ mbinddt term F f) =
        (mbinddt term (F ∘ G) (compose_dtm (ix := I1) g f)).
  Proof.
    intros. ext t.
    generalize dependent g.
    generalize dependent f.
    unfold compose at 1. induction t; intros f g.
    - cbn. fequal.
      fequal. ext k. change [] with (Ƶ : list atom). rewrite incr_zero.
      reflexivity.
    - cbn.
      (* left side *)
      do 2 rewrite ap6.
      rewrite (app_pure_natural F).
      (* right side, constructor *)
      unfold_ops @Pure_compose.
      (* right side, first argument *)
      rewrite_strat innermost (terms (ap_compose3 G F)).
      rewrite (app_pure_natural F).
      rewrite <- IHt1.
      rewrite <- ap7.
      rewrite (app_pure_natural F).
      (* right side, outer *)
      rewrite_strat innermost (terms (ap_compose3 G F)).
      rewrite (compose_dtm_incr g f).
      rewrite <- IHt2.
      rewrite (ap6_simple (G := F) (ap G)).
      rewrite <- (ap7 (G := F)).
      rewrite ap6.
      rewrite (app_pure_natural F).
      (* Done *)
      reflexivity.
  Qed.

  End law3.

(*|
------------------------
Law 4
------------------------

|*)
  Section law4.

    Set Keyed Unification.

    Context
      (F : Type -> Type)
      (G : Type -> Type)
     `{ApplicativeMorphism F G ϕ}.

  Lemma mbinddt_morphism_term :
    forall `(f : forall k, list atom * A -> F (T k B)),
      ϕ (term B) ∘ mbinddt term F f =
        mbinddt term G (fun k => ϕ (T k B) ∘ f k).
  Proof.
    intros. ext t.
    generalize dependent f.
    induction t.
    - reflexivity.
    - match goal with
      | hyp : ApplicativeMorphism F G ϕ |- _ => inversion hyp
      end.
      intros. unfold compose at 1. cbn.
      (* left side *)
      do 2 rewrite ap_morphism_1.
      rewrite appmor_pure.
      (* right side *)
      rewrite <- IHt1.
      rewrite <- IHt2.
      (* Done *)
      reflexivity.
  Qed.

  End law4.

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

#[export] Instance: forall k, DTPreModule (list atom) (T k) T :=
  fun k => match k with
        | MkK1 => DTP_term
        end.

#[export] Instance: DTM (list atom) T :=
  {| dtm_mbinddt_comp_mret := mbinddt_comp_mret_T;
  |}.
