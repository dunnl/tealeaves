From Tealeaves Require Export
  Classes.Functor
  Classes.Monoid.

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
#[export] Instance Monoid_op_list {A}: Monoid_op (list A) := @app A.

#[export] Instance Monoid_unit_list {A}: Monoid_unit (list A) := nil.

#[export, program] Instance Monoid_list {A} :
  @Monoid (list A) (@Monoid_op_list A) (@Monoid_unit_list A).

Solve Obligations with (intros; unfold transparent tcs; auto with datatypes).

(** * The list [Functor] instance *)
(******************************************************************************)
#[export] Instance Map_list : Map list :=
  fun A B => @List.map A B.

(** ** Rewriting lemmas for <<map>> *)
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

(** ** Functor laws *)
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

(** * Folding over lists *)
(******************************************************************************)
Fixpoint crush_list
  `{op: Monoid_op M}
  `{unit: Monoid_unit M} (l: list M): M :=
  match l with
  | nil => Ƶ
  | cons x l' => x ● crush_list l'
  end.

(** ** Rewriting lemmas for [fold] *)
(******************************************************************************)
Section crush_list_rewriting_lemmas.

  Context
    `{Monoid M}.

  Lemma crush_list_nil: crush_list (@nil M) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma crush_list_cons: forall (m: M) (l: list M),
      crush_list (m :: l) = m ● crush_list l.
  Proof.
    reflexivity.
  Qed.

  Lemma crush_list_one: forall (m: M), crush_list [ m ] = m.
  Proof.
    intro. cbn. now simpl_monoid.
  Qed.

  Lemma crush_list_app: forall (l1 l2: list M),
      crush_list (l1 ++ l2) = crush_list l1 ● crush_list l2.
  Proof.
    intros l1 ?. induction l1 as [| ? ? IHl].
    - cbn. now simpl_monoid.
    - cbn. rewrite IHl. now simpl_monoid.
  Qed.

End crush_list_rewriting_lemmas.

(** ** Misc properties *)
(******************************************************************************)
(** <<crush_list>> commutes with monoid homomorphisms *)
Lemma crush_list_mon_hom:
  forall `(ϕ: M1 -> M2) `{Monoid_Morphism M1 M2 ϕ},
    ϕ ∘ crush_list = crush_list ∘ map ϕ.
Proof.
  intros ? ? ϕ ? ? ? ? ?. unfold compose. ext l.
  induction l as [| ? ? IHl].
  - cbn. apply monmor_unit.
  - cbn. now rewrite (monmor_op (ϕ := ϕ)), IHl.
Qed.

(** ** Folding a list is a monoid homomorphism *)
(** <<crush_list: list M -> M>> is homomorphism of monoids. *)
(******************************************************************************)
#[export] Instance Monmor_crush_list (M: Type) `{Monoid M} :
  Monoid_Morphism (list M) M crush_list :=
  {| monmor_unit := crush_list_nil;
    monmor_op := crush_list_app;
  |}.
