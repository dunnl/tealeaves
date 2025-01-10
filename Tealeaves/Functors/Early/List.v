From Tealeaves Require Import
  Misc.List
  Classes.Functor.

Import List.ListNotations.
Import Monoid.Notations.
Open Scope list_scope.

#[local] Generalizable Variables A B M.

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
