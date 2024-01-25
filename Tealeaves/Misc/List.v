From Tealeaves Require Import
  Classes.Monoid
  Classes.Functor.

Import List.ListNotations.
Import Monoid.Notations.
Open Scope list_scope.

#[local] Generalizable Variables A B M.

(** * Automation: <<simpl_list>> *)
(******************************************************************************)
Create HintDb tea_list.
Tactic Notation "simpl_list" := (autorewrite with tea_list).
Tactic Notation "simpl_list" "in" hyp(H) := (autorewrite with tea_list H).
Tactic Notation "simpl_list" "in" "*" := (autorewrite with tea_list in *).

(** * [list] monoid *)
(******************************************************************************)
#[export] Instance Monoid_op_list {A} : Monoid_op (list A) := @app A.

#[export] Instance Monoid_unit_list {A} : Monoid_unit (list A) := nil.

#[export, program] Instance Monoid_list {A} :
  @Monoid (list A) (@Monoid_op_list A) (@Monoid_unit_list A).

Solve Obligations with (intros; unfold transparent tcs; auto with datatypes).

(** * Folding over lists *)
(******************************************************************************)
Fixpoint fold (M : Type) `{op : Monoid_op M} `{unit : Monoid_unit M} (l : list M) : M :=
  match l with
  | nil => Ƶ
  | cons x l' => x ● fold M l'
  end.

(** ** Rewriting lemmas for [fold] *)
(******************************************************************************)
Section fold_rewriting_lemmas.

  Context
    (M : Type)
    `{Monoid M}.

  Lemma fold_nil : fold M (@nil M) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_cons : forall (m : M) (l : list M),
      fold M (m :: l) = m ● fold M l.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_one : forall (m : M), fold M [ m ] = m.
  Proof.
    intro. cbn. now simpl_monoid.
  Qed.

  Lemma fold_app : forall (l1 l2 : list M),
      fold M (l1 ++ l2) = fold M l1 ● fold M l2.
  Proof.
    intros l1 ?. induction l1 as [| ? ? IHl].
    - cbn. now simpl_monoid.
    - cbn. rewrite IHl. now simpl_monoid.
  Qed.

End fold_rewriting_lemmas.

(** * Filtering lists *)
(******************************************************************************)
Fixpoint filter `(P : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons a rest =>
    if P a then a :: filter P rest else filter P rest
  end.

(** ** Folding a list is a monoid homomorphism *)
(** <<fold : list M -> M>> is homomorphism of monoids. *)
(******************************************************************************)
#[export] Instance Monmor_fold (M : Type) `{Monoid M} :
  Monoid_Morphism (list M) M (fold M) :=
  {| monmor_unit := fold_nil M;
    monmor_op := fold_app M
  |}.

(** ** Rewriting lemmas for [filter] *)
(******************************************************************************)
Section filter_lemmas.

  Context
    `(P : A -> bool).

  Lemma filter_nil :
    filter P nil = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_cons : forall (a : A) (l : list A),
      filter P (a :: l) = if P a then a :: filter P l else filter P l.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_one : forall (a : A),
      filter P [a] = if P a then [a] else nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_app : forall (l1 l2 : list A),
      filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
  Proof.
    intros. induction l1.
    - reflexivity.
    - cbn. rewrite IHl1. now destruct (P a).
  Qed.

End filter_lemmas.

#[export] Hint Rewrite @filter_nil @filter_cons @filter_app @filter_one : tea_list.

(** * The list [Functor] instance *)
(******************************************************************************)
#[export] Instance Map_list : Map list :=
  fun A B => @List.map A B.

(** *** Rewriting lemmas for <<map>> *)
(******************************************************************************)
Section map_list_rw.

  Context
    {A B : Type}
    (f : A -> B).

  Lemma map_list_nil : map f (@nil A) = @nil B.
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_cons : forall (x : A) (xs : list A),
      map f (x :: xs) = f x :: map f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_one (a : A) : map f [ a ] = [f a].
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_app : forall (l1 l2 : list A),
      map f (l1 ++ l2) = map f l1 ++ map f l2.
  Proof.
    intros.
    unfold transparent tcs.
    now rewrites List.map_app.
  Qed.

End map_list_rw.

#[export] Hint Rewrite @map_list_nil @map_list_cons
     @map_list_one @map_list_app : tea_list.

(** *** Functor laws *)
(******************************************************************************)
Theorem map_id_list {A} : map (F := list) (@id A) = id.
Proof.
  ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

Theorem map_map_list {A B C} : forall (f : A -> B) (g : B -> C),
    map g ∘ map f = map (F := list) (g ∘ f).
Proof.
  intros. unfold compose. ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

#[export] Instance Functor_list : Functor list :=
  {| fun_map_id := @map_id_list;
     fun_map_map := @map_map_list;
  |}.

(** * <<Tolist>> and <<TolistCtx>> operations *)
(******************************************************************************)
Import Classes.Functor.Notations.

Class Tolist (F : Type -> Type) :=
  tolist : F ⇒ list.

Class TolistCtx (F : Type -> Type) (W : Type) :=
  tolist_ctx : forall (A : Type), F A -> list (W * A).

#[global] Arguments tolist {F}%function_scope {Tolist} {A}%type_scope _.
#[global] Arguments tolist_ctx {F}%function_scope {W} {TolistCtx} {A}%type_scope _.
