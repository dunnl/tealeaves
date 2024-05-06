From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Category
  Functors.Writer.

Export EqDec_eq.
Import Product.Notations.
Import Category.Notations.
#[local] Open Scope category_scope.

Class Index : Type :=
  { K : Type;
    ix_dec_eq :> EqDec_eq K }.

Definition allK `{Index} {A B: Type}: (A -> B) -> K -> A -> B := const.

Definition vec_compose `{Index}
  {A: K -> Type} {B: K -> Type} {C: K -> Type}
   (g: forall k:K, B k -> C k)
  (f: forall k:K, A k -> B k) :=
  fun k => g k ∘ f k.

(** * The category of constant k-families *)
(******************************************************************************)
Section category_kconst.

  Context
    `{Index}.

  Definition kconst_id {A} := fun (k : K) (a : A) => a.

  #[global] Instance kconst_arrows : Arrows Type :=
    fun (a b : Type) => forall k : K, a -> b.

  #[global] Instance kconst_idents : Identities Type :=
    @kconst_id.

  #[global] Instance kconst_comp : Composition Type :=
    fun (a b c : Type) (g : b ⟶ c) (f : a ⟶ b ) =>
      vec_compose g f.

  #[global] Instance kconst_cat : Category Type.
  Proof.
    intros. constructor; easy.
  Qed.

End category_kconst.

(** * The category of K-indexed type families *)
(******************************************************************************)

Definition KType `{ix: Index}: Type := K -> Type.

Section category_kfam.

  Context
    `{Index}.

  Definition kid {A:KType} := fun (k:K) (a: A k) => a.

  #[global] Instance kfam_arrows : Arrows KType :=
    fun (a b: KType) => forall k : K, a k -> b k.

  #[global] Instance kfam_idents : Identities KType :=
    @kid.

  #[global] Instance kfam_comp : Composition KType :=
    fun (a b c : KType) (g : b ⟶ c) (f : a ⟶ b ) =>
      vec_compose g f.

  #[global] Instance kfam_cat : Category KType.
  Proof.
    intros. constructor; easy.
  Qed.

End category_kfam.

(** ** Specialized notations for multisorted Tealeaves *)
(******************************************************************************)
Declare Scope tealeaves_multi_scope.
Delimit Scope tealeaves_multi_scope with tea_multi.
Open Scope tealeaves_multi_scope.

Module Notations.

  Infix "-k->" := (homset (Arrows:=kconst_arrows))
                    (at level 90, right associativity) : tealeaves_multi_scope.

  Notation "A ~k~> G B" :=
    (forall k, A -> G k B%type) (at level 70, G at level 5, B at level 5) : tealeaves_multi_scope.

  (** This notation is similar to but more general than <<⊙>> because it works even
  when <<g>> or <<f>> are dependently-typed (and hence not morphisms in the
  category of constant K-families). This is particularly intended for composition with Kleisli morphisms. *)
  Notation "g ◻ f" := (vec_compose g f) (at level 50) : tealeaves_multi_scope.

  (*
  Infix "⊙":= (@comp Type _ kconst_comp _ _ _)
                (at level 40, left associativity) : tealeaves_multi_scope.
   *)

  Notation "F ⇒ G" := (forall A : Type, F A -> G A)
                        (at level 50) : tealeaves_multi_scope.
End Notations.

Import Notations.

(** * Other lemmas *)
(******************************************************************************)
Section vec_compose_rw.

  Context
    `{Index}
      {A: K -> Type} {B: K -> Type} {C D: K -> Type}
      (h: forall k:K, C k -> D k)
      (g: forall k:K, B k -> C k)
      (f: forall k:K, A k -> B k).

  Lemma vec_compose_k: forall k,
      (g ◻ f) k = g k ∘ f k.
  Proof.
    reflexivity.
  Qed.

  Lemma vec_compose_assoc:
      (h ◻ g) ◻ f = h ◻ (g ◻ f).
  Proof.
    reflexivity.
  Qed.

  Lemma vec_compose_allK {A' B' C'}
    (g': B' -> C')
    (f': A' -> B'):
    (allK g' ◻ allK f') =
      (allK (g' ∘ f')).
  Proof.
    reflexivity.
  Qed.

End vec_compose_rw.

(** * Targeted morphisms *)
(** Combinators and operations for "multisorted" morphisms that only
    target values tagged with a particular value of <<k>>, e.g. an
    operation that only affects type variables in an expression
    instead of all variables. *)
(******************************************************************************)
Section targeted_morphisms.

  Context
    `{ix : Index}.

  (** *** Rewriting Hints for [tgt]-like combinators *)
  (******************************************************************************)
  (** We create some hint databases for rewriting expressions involving the
    "targeting" combinators defined in this section and elsewhere. These should
    typically be used with [autorewrite*] in order to ensure the correct lemmas
    are invoked (namely, those which do not raise side-conditions that cannot be
    solved, typically because a <<XXX_neq>> lemma has been chosen when
    <<XXX_eq>> is the right one). Due to a bug involving [autorewrite*] we also
    create smaller databases that are convenient to use with [autorewrite]
    (without the <<*>>), at the cost of verbosity. *)
  (** See #<a href="https://github.com/coq/coq/issues/14344">https://github.com/coq/coq/issues/14344</a>#,
   *)
  Create HintDb tea_tgt.
  Create HintDb tea_tgt_eq.
  Create HintDb tea_tgt_neq.

  (** *** Map-building combinators: [tgt], [tgt_def] *)
  (** Build a k-morphism that targets only the leaves belonging to a partition
    <<k>>. This must be restricted to morphisms that do not change the leaf type
    because leaves of the other partitions are left unchanged. *)
  (******************************************************************************)
  Definition tgt {A} (k : K) (f : A -> A) : A -k-> A :=
    fun j => if k == j then f else id.

  Definition tgt_def {A B} (k : K) (f def : A -> B) : A -k-> B :=
    fun j => if k == j then f else def.

  (** *** Lemmas for [tgt], [tgt_def] *)
  (******************************************************************************)
  Lemma tgt_id {A} (k : K) :
    tgt k (@id A) = kid.
  Proof.
    unfold tgt. ext j. compare values k and j.
  Qed.

  Lemma tgt_tgt_eq {A} (k : K) (g f : A -> A) :
    tgt k (g ∘ f) = tgt k g ◻ tgt k f.
  Proof.
    unfold vec_compose, tgt. ext j.
    compare values k and j.
  Qed.

  Lemma tgt_tgt_neq {A} (k1 k2 : K) (g f : A -> A) :
    k1 <> k2 -> tgt k2 g ◻ tgt k1 f = tgt k1 f ◻ tgt k2 g.
  Proof.
    introv neq.
    unfold vec_compose, tgt, Category.comp, kconst_comp.
    ext k. compare k to both of {k1 k2}.
  Qed.

  Lemma tgt_eq {A} (k : K) (f : A -> A) : tgt k f k = f.
  Proof.
    unfold tgt. compare values k and k.
  Qed.

  Lemma tgt_neq {A} (k j : K) (p : k <> j) (f : A -> A) : tgt k f j = id.
  Proof.
    unfold tgt. compare values k and j.
  Qed.

  (** Build a multisorted morphism that targets only the leaves
    belonging to a partition [k]. A default function is applied to all
    other partitions, so in general the leaf types may change to some
    [B]. *)
  Lemma tgt_def_eq {A B} (k : K) (f def : A -> B) : tgt_def k f def k = f.
  Proof.
    unfold tgt_def. compare values k and k.
  Qed.

  Lemma tgt_def_neq {A B} (k j : K) (p : k <> j) (f def : A -> B) : tgt_def k f def j = def.
  Proof.
    unfold tgt_def. compare values k and j.
  Qed.

  Lemma tgt_def_tgt_def_eq {A B C} (k : K) (f def1 : A -> B) (g def2 : B -> C) :
    tgt_def k (g ∘ f) (def2 ∘ def1) = tgt_def k g def2 ◻ tgt_def k f def1.
  Proof.
    unfold vec_compose, tgt_def. ext j. compare values k and j.
  Qed.

  Lemma tgt_def_tgt_def_neq {A B C} (k1 k2 : K) (f def1 : A -> B) (g def2 : B -> C)  :
    k1 <> k2 ->
    tgt_def k2 g def2 ◻ tgt_def k1 f def1 =
    fun k => if k == k1 then def2 ∘ f else
            if k == k2 then g ∘ def1 else def2 ∘ def1.
  Proof.
    introv neq. unfold vec_compose, tgt_def.
    ext k. compare k to both of {k1 k2}.
  Qed.

  Lemma tgt_def_same {A B} (k : K) (f : A -> B) : tgt_def k f f = const f.
  Proof.
    unfold tgt_def. ext j. compare values k and j.
  Qed.

  (** *** Lemmas for [tgtd] *)
  (******************************************************************************)
  #[program] Definition tgtd `{ix : Index} {A W : Type}
    (j : K) (f : W * A -> A) : K -> W * A -> A :=
    fun k '(w, a) => if k == j then f (w, a) else a.

  Context {W A: Type}.

  Lemma tgtd_eq : forall k (f : W * A -> A),
      tgtd (W := W) k f k = f.
  Proof.
    introv. unfold tgtd. ext [w a].
    compare values k and k.
  Qed.

  Lemma tgtd_neq : forall {k j} (f : W * A -> A),
      k <> j -> tgtd j f k = extract (W := (W ×)).
  Proof.
    introv. unfold tgtd. intro hyp. ext [w a].
    compare values k and j.
  Qed.

  Lemma tgtd_id (j : K) :
    tgtd (W := W) (A := A) j extract = allK extract.
  Proof.
    unfold tgtd. ext k [w a]. compare values k and j.
  Qed.

End targeted_morphisms.

(** ** Automation support *)
#[export] Hint Rewrite @tgt_eq @tgt_def_eq @tgt_def_same : tea_tgt.
#[export] Hint Rewrite @tgt_eq @tgt_def_eq @tgt_def_same : tea_tgt_eq.
#[export] Hint Rewrite @tgt_neq @tgt_def_neq using auto : tea_tgt.
#[export] Hint Rewrite @tgt_neq @tgt_def_neq using auto : tea_tgt_neq.

(** <<autorewrite>>* seems to be bit by this bug:
      https://github.com/coq/coq/issues/14344 *)
Tactic Notation "simpl_tgt" := (autorewrite* with tea_tgt).
Tactic Notation "simpl_tgt" "in" hyp(H) := (autorewrite* with tea_tgt in H).
Tactic Notation "simpl_tgt" "in" "*" := (autorewrite* with tea_tgt in *).

Ltac simpl_tgt_fallback :=
  repeat first [ let n1:= numgoals in
          autorewrite with tea_tgt_neq;
          let n2:= numgoals in guard n1 = n2 |
          let n1:= numgoals in
          autorewrite with tea_tgt_eq;
          let n2:= numgoals in guard n1 = n2 ].

Ltac simpl_tgt_fallback_all :=
  repeat first [ let n1:= numgoals in
          autorewrite with tea_tgt_neq in *;
          let n2:= numgoals in guard n1 = n2 |
          let n1:= numgoals in
          autorewrite with tea_tgt_eq in *;
          let n2:= numgoals in guard n1 = n2 ].

Ltac simpl_tgt_fallback_in H :=
  repeat first [ let n1:= numgoals in
          autorewrite with tea_tgt_neq in H;
          let n2:= numgoals in guard n1 = n2 |
          let n1:= numgoals in
          autorewrite with tea_tgt_eq in H;
          let n2:= numgoals in guard n1 = n2 ].

Tactic Notation "simpl_tgt_fallback" "in" hyp(H) := (simpl_tgt_fallback_in H).
Tactic Notation "simpl_tgt_fallback" "in" "*" := (simpl_tgt_fallback_all).
