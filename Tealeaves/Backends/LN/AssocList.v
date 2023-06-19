From Tealeaves.Theory Require Import
  Traversable.Functor.
From Tealeaves.Functors Require Import
  Writer.
From Tealeaves.Backends.LN Require Import
  Atom
  AtomSet.

From Coq Require Import
  Logic.Decidable
  Sorting.Permutation.

Import Product.Notations.
Import List.ListNotations.
Import LN.AtomSet.Notations.
Import Sets.ElNotations.

Create HintDb tea_alist.

(** * The <<alist>> functor *)
(******************************************************************************)
(** An association list is a list of pairs of type <<atom * A>>.  A
functor instance is provided by mapping over <<A>>, leaving atoms
alone.  Technically the functor is the composition of [list] and
<<prod atom>>. *)
(******************************************************************************)
Module Notations.
  Notation "'one'" := (ret list _).
  Notation "x ~ a" := (ret list _ (x, a)) (at level 50).
End Notations.

Import Notations.

Definition alist := list ∘ (atom ×).

(** ** Functor instance for <<alist>> *)
(******************************************************************************)
#[export] Instance Functor_alist : Functor alist := Functor_compose list (atom ×).

(*
(** ** DT functor instance for <<alist>> *)
(******************************************************************************)
Section DecoratedTraversableFunctor_alist.

  (** ** Traversable instance *)
  (******************************************************************************)
  #[global] Instance Dist_alist : Dist alist
    := Dist_compose.

  #[global] Instance Traversable_alist : TraversableFunctor alist
    := Traversable_compose.

  (** ** Decorated instance *)
  (******************************************************************************)
  #[global] Instance Decorate_alist :
    Decorate W (alist)
    := Decorate_zero.

  #[global] Instance DecoratedFunctor_alist :
    Algebraic.Decorated.Functor.DecoratedFunctor W (alist)
    := DecoratedFunctor_zero.

  (** ** DTM instance *)
  (******************************************************************************)
  #[global] Instance DecoratedTraversableFunctor_alist :
    DecoratedTraversableFunctor W (alist).
  Proof.
    constructor.
    typeclasses eauto.
    typeclasses eauto.
    intros.
    unfold_ops @Dist_alist @Dist_compose.
    unfold_ops @Fmap_compose.
    unfold_ops @Decorate_alist @Decorate_zero.
    reassociate <-.
    change (fmap G (fmap (list ○ prod atom) ?f))
      with (fmap (G ∘ list) (fmap (prod atom) f)).
    #[local] Set Keyed Unification.
    rewrite (natural (Natural := dist_natural list) (G := G ∘ list)).
    reassociate -> on right.
    rewrite (fun_fmap_fmap list).
    change (fmap list (fmap (prod atom) ?f)) with (fmap (list ∘ prod atom) f).
    (*
    rewrite <- (natural (Natural := dist_natural list) (G := G ∘ list)).
    rewrite (natural (Natural := dist_natural list)).
    rewrite (dist_natural (prod atom)).
    reassociate -> on left. rewrite (fun_fmap_fmap list).
    reassociate -> on left. rewrite (fun_fmap_fmap list).
    rewrite (fun_fmap_fmap (prod atom)). reflexivity.
    #[local] Unset Keyed Unification.
    *)
  Qed.

End DecoratedTraversableFunctor_alist.
 *)

(** * <<envmap>>  *)
(******************************************************************************)
(** [envmap] is just [fmap] specialized to <<alist>>. *)

Definition envmap {A B : Type} : (A -> B) -> alist A -> alist B :=
  map alist.

(** ** Rewriting principles for [envmap] *)
(******************************************************************************)
Section envmap_lemmas.

  Context
    (A B : Type).

  Implicit Types (f : A -> B) (x : atom) (a : A) (Γ : list (atom * A)).

  Lemma envmap_nil : forall f,
    envmap f (@nil (atom * A)) = nil.
  Proof.
    unfold envmap. unfold_ops @Map_compose.
    now simpl_list.
  Qed.

  Lemma envmap_one : forall f x a,
    envmap f (x ~ a) = (x ~ f a).
  Proof.
    reflexivity.
  Qed.

  Lemma envmap_cons : forall f x a Γ,
    envmap f ((x, a) :: Γ) = x ~ f a ++ envmap f Γ.
  Proof.
    reflexivity.
  Qed.

  Lemma envmap_app : forall f Γ1 Γ2,
    envmap f (Γ1 ++ Γ2) = envmap f Γ1 ++ envmap f Γ2.
  Proof.
    intros. unfold envmap. unfold_ops @Map_compose.
    now simpl_list.
  Qed.

End envmap_lemmas.

Create HintDb tea_rw_envmap.
#[export] Hint Rewrite envmap_nil envmap_one
  envmap_cons envmap_app : tea_rw_envmap.

(** ** Specifications for [∈] and <<envmap>>*)
(******************************************************************************)
Section in_envmap_lemmas.

  Context
    {A B : Type}
    (l : alist A)
    (f : A -> B).

  Lemma in_envmap_iff : forall (x : atom) (b : B),
      (x, b) ∈ (envmap f l : list (atom * B)) <->
      exists a : A, (x, a) ∈ (l : list (atom * A)) /\ f a = b.
  Proof.
    intros. unfold envmap.
    unfold_ops @Map_compose @Map_Env @El_list.
    unfold_ops @Map_list.
    Set Printing All.
    Search "in_map_iff".
    admit.
    (*
    rewrite (in_map_iff list). split; intros; preprocess; eauto.
     *)
  Admitted.

End in_envmap_lemmas.

(** ** Rewriting principles for [∈] *)
(******************************************************************************)
Section in_rewriting_lemmas.

  Context
    (A B : Type).

  Implicit Types (x : atom) (a : A) (b : B).

  Lemma in_nil_iff : forall x a,
      (x, a) ∈ nil <-> False.
  Proof.
    now autorewrite with tea_list.
  Qed.

  Lemma in_cons_iff : forall x y a1 a2 Γ,
      (x, a1) ∈ ((y, a2) :: Γ) <-> (x = y /\ a1 = a2) \/ (x, a1) ∈ Γ.
  Proof.
    introv. autorewrite with tea_list.
    now rewrite pair_equal_spec.
  Qed.

  Lemma in_one_iff : forall x y a1 a2,
      (x, a1) ∈ (y ~ a2) <-> x = y /\ a1 = a2.
  Proof.
    introv. autorewrite with tea_list.
    now rewrite pair_equal_spec.
  Qed.

  Lemma in_app_iff : forall x a Γ1 Γ2,
      (x, a) ∈ (Γ1 ++ Γ2) <-> (x, a) ∈ Γ1 \/ (x, a) ∈ Γ2.
  Proof.
    introv. now autorewrite with tea_list.
  Qed.

End in_rewriting_lemmas.

Create HintDb tea_rw_in.
#[export] Hint Rewrite @in_nil_iff @in_cons_iff
  @in_one_iff @in_app_iff @in_envmap_iff : tea_rw_in.

(** ** Tactical lemmas for [∈] *)
(******************************************************************************)
Section in_theorems.

  Context
    (A B : Type).

  Implicit Types (x y : atom) (a b : A) (f : A -> B) (Γ : list (atom * A)).

  Lemma in_one1 : forall x a y b,
    (x, a) ∈ (y ~ b) ->
    x = y.
  Proof.
    introv. now autorewrite with tea_rw_in.
  Qed.

  Lemma in_one2 : forall x a y b,
      (x, a) ∈ (y ~ b) ->
      a = b.
  Proof.
    introv. now autorewrite with tea_rw_in.
  Qed.

  Lemma in_one_3 : forall x a,
    (x, a) ∈ (x ~ a).
  Proof.
    introv. now autorewrite with tea_rw_in.
  Qed.

  Lemma in_cons1 : forall x y a b Γ,
    (x, a) ∈ ((y, b) :: Γ) ->
    (x = y /\ a = b) \/ (x, a) ∈ Γ.
  Proof.
    introv. now autorewrite with tea_rw_in.
  Qed.

  Lemma in_cons2 : forall x a E,
      (x, a) ∈ ((x, a) :: E).
  Proof.
    intros. autorewrite with tea_rw_in.
    now left.
  Qed.

  Lemma in_cons_3 : forall x a y b E,
    (x, a) ∈ E ->
    (x, a) ∈ ((y, b) :: E).
  Proof.
    intros. autorewrite with tea_rw_in.
    auto.
  Qed.

  Lemma in_app2 : forall x a Γ1 Γ2,
      (x, a) ∈ Γ1 ->
      (x, a) ∈ (Γ1 ++ Γ2).
  Proof.
    intros. autorewrite with tea_rw_in.
    auto.
  Qed.

  Lemma in_app_3 :forall x a Γ1 Γ2,
      (x, a) ∈ Γ2 ->
      (x, a) ∈ (Γ1 ++ Γ2).
  Proof.
    intros. autorewrite with tea_rw_in.
    auto.
  Qed.

  Lemma in_map_mono : forall x a f Γ,
    (x, a) ∈ Γ ->
    (x, f a) ∈ (envmap f Γ : list (atom * B)).
  Proof.
    introv hyp. autorewrite with tea_rw_in.
    eauto.
  Qed.

End in_theorems.

#[export] Hint Resolve in_one_3 in_cons2 in_cons_3 in_app2
 in_app_3 in_map_mono : tea_alist.
#[export] Hint Immediate in_one1 in_one2 : tea_alist.

(** * Domain and range on alists *)
(******************************************************************************)

(** [dom] computes the list of keys of an association list. *)
Definition dom {A} (Γ : alist A) : list atom :=
  map list fst Γ.

(** [domset] computes the keys as an [AtomSet.t] for use with <<fsetdec>>. *)
Definition domset {A} (Γ : alist A) : AtomSet.t :=
  atoms (dom Γ).

(** [range] computes the list of values of an association list. *)
Definition range {A} ( Γ : alist A) : list A :=
  map list (extract (atom ×) A)  Γ.

(** ** Rewriting lemmas for [dom] *)
(******************************************************************************)
Section dom_lemmas.

  Context
    (A : Type).

  Lemma dom_nil :
    dom (@nil (atom * A)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma dom_cons : forall (x : atom) (a : A) (E : alist A),
      dom ((x, a) :: E) = [ x ] ++ dom E.
  Proof.
    reflexivity.
  Qed.

  Lemma dom_one : forall (x : atom) (a : A),
      dom (x ~ a) = [ x ].
  Proof.
    reflexivity.
  Qed.

  Lemma dom_app : forall (E F : alist A),
      dom (E ++ F) = dom E ++ dom F.
  Proof.
    intros. unfold dom. now simpl_list.
  Qed.

  Lemma dom_map : forall {B} {f : A -> B} (l : alist A),
      dom (envmap f l) = dom l.
  Proof.
    intros. unfold dom, envmap. compose near l on left.
    unfold_ops @Map_compose.
    rewrite (fun_map_map list _ _ _ (map (prod atom) f) fst).
    fequal. now ext [? ?].
  Qed.

End dom_lemmas.

Create HintDb tea_rw_dom.
#[export] Hint Rewrite dom_nil dom_cons dom_app dom_one dom_map : tea_rw_dom.

Lemma push_not : forall P Q,
    ~ (P \/ Q) <-> ~P /\ ~ Q.
Proof.
  firstorder.
Qed.

#[export] Hint Rewrite push_not : tea_rw_dom.

(** ** Rewriting lemmas for [domset] *)
(******************************************************************************)
Section domset_lemmas.

  Context
    (A : Type).

  Lemma domset_nil :
    domset (@nil (atom * A)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma domset_cons : forall (x : atom) (a : A) (Γ : alist A),
      domset ((x, a) :: Γ) [=] {{ x }} ∪ domset Γ.
  Proof.
    intros. unfold domset. autorewrite with tea_rw_dom tea_rw_atoms.
    fsetdec.
  Qed.

  Lemma domset_one : forall (x : atom) (a : A),
      domset (x ~ a) [=] {{ x }}.
  Proof.
    intros. unfold domset. autorewrite with tea_rw_dom tea_rw_atoms.
    fsetdec.
  Qed.

  Lemma domset_app : forall (Γ1 Γ2 : alist A),
      domset (Γ1 ++ Γ2) [=] domset Γ1 ∪ domset Γ2.
  Proof.
    intros. unfold domset. autorewrite with tea_rw_dom tea_rw_atoms.
    fsetdec.
  Qed.

  Corollary domset_app_one_l : forall (Γ1 : alist A) (x : atom) (a : A),
      domset (Γ1 ++ x ~ a) [=] domset Γ1 ∪ {{ x }}.
  Proof.
    intros. unfold domset. autorewrite with tea_rw_dom tea_rw_atoms.
    fsetdec.
  Qed.

  Lemma domset_map : forall {B} {f : A -> B} (Γ : alist A),
      domset (envmap f Γ) [=] domset Γ.
  Proof.
    intros. unfold domset. autorewrite with tea_rw_dom.
    fsetdec.
  Qed.

End domset_lemmas.

#[export] Hint Rewrite domset_nil domset_cons
  domset_one domset_app domset_map : tea_rw_dom.

(** ** Rewriting lemmas for [range] *)
(******************************************************************************)
Section range_lemmas.

  Context
    (A : Type).

  Lemma range_nil :
    range (@nil (atom * A)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma range_one : forall (x : atom) (a : A),
      range (x ~ a) = [ a ].
  Proof.
    reflexivity.
  Qed.

  Lemma range_cons : forall (x : atom) (a : A) (Γ : alist A),
      range ((x, a) :: Γ) = [ a ] ++ range Γ.
  Proof.
    reflexivity.
  Qed.

  Lemma range_app : forall (Γ1 Γ2 : alist A),
      range (Γ1 ++ Γ2) = range Γ1 ++ range Γ2.
  Proof.
    intros. unfold range.
    now autorewrite with tea_list.
  Qed.

  Lemma range_map : forall {B} {f : A -> B} (Γ : alist A),
      range (envmap f Γ) = map list f (range Γ).
  Proof.
    intros. unfold range, envmap. compose near Γ.
    unfold_ops @Map_compose.
    rewrite (fun_map_map list _ _ _ (map (prod atom) f) (extract (atom ×) B)).
    rewrite (fun_map_map list _ _ _ (extract (atom ×) A) f).
    fequal. now ext [? ?].
  Qed.

End range_lemmas.

Create HintDb tea_rw_range.
#[export] Hint Rewrite range_nil range_cons
     range_one range_app range_map : tea_rw_range.

(** ** Rewriting lemmas for [∈] [dom] *)
(******************************************************************************)
Section in_dom_lemmas.

  Context
    (A : Type).

  Lemma in_dom_nil : forall x,
      x ∈ dom (@nil (atom * A)) <-> False.
  Proof.
    intros; now autorewrite with tea_rw_dom.
  Qed.

  Lemma in_dom_cons : forall (x y : atom) (a : A) (Γ : alist A),
      y ∈ dom ((x, a) :: Γ) <-> y = x \/ y ∈ dom Γ.
  Proof.
    intros; now autorewrite with tea_rw_dom tea_list.
  Qed.

  Lemma in_dom_one : forall (x y : atom) (a : A),
      y ∈ dom (x ~ a) <-> y = x.
  Proof.
    intros. now autorewrite with tea_rw_dom tea_list.
  Qed.

  Lemma in_dom_app : forall x (Γ1 Γ2 : alist A),
      x ∈ dom (Γ1 ++ Γ2) <-> x ∈ dom Γ1 \/ x ∈ dom Γ2.
  Proof.
    intros; now autorewrite with tea_rw_dom tea_list.
  Qed.

  Lemma in_dom_map : forall {B} {f : A -> B} (Γ : alist A) x,
      x ∈ dom (envmap f Γ) <-> x ∈ dom Γ.
  Proof.
    intros; now autorewrite with tea_rw_dom.
  Qed.

End in_dom_lemmas.

#[export] Hint Rewrite in_dom_nil in_dom_one in_dom_cons
  in_dom_app in_dom_map : tea_rw_dom.

(** ** Rewriting lemmas for [∈] [domset] *)
(******************************************************************************)
Section in_domset_lemmas.

  Context
    (A : Type).

  Lemma in_domset_nil : forall x,
      x ∈@ domset (@nil (atom * A)) <-> False.
  Proof.
    intros. autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma in_domset_one : forall (x y : atom) (a : A),
      y ∈@ domset (x ~ a) <-> y = x.
  Proof.
    intros. autorewrite with tea_rw_dom.
    fsetdec.
  Qed.

  Lemma in_domset_cons : forall (x y : atom) (a : A) (Γ : alist A),
      y ∈@ domset ((x, a) :: Γ) <-> y = x \/ y ∈@ domset Γ.
  Proof.
    intros. autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma in_domset_app : forall x (Γ1 Γ2 : alist A),
    x ∈@ domset (Γ1 ++ Γ2) <-> x ∈@ domset Γ1 \/ x ∈@ domset Γ2.
  Proof.
    intros. autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma in_domset_map : forall {B} {f : A -> B} (l : alist A) x,
      x ∈@ domset (envmap f l) <-> x ∈@ domset l.
  Proof.
    intros. autorewrite with tea_rw_dom. fsetdec.
  Qed.

End in_domset_lemmas.

#[export] Hint Rewrite in_domset_nil in_domset_one
     in_domset_cons in_domset_app in_domset_map : tea_rw_dom.

(** ** Elements of [range] *)
(******************************************************************************)
Section in_range_lemmas.

  Context
    (A : Type).

  Lemma in_range_nil : forall x,
    x ∈ range (@nil (atom * A)) <-> False.
  Proof.
    intros; now autorewrite with tea_rw_range.
  Qed.

  Lemma in_range_cons : forall (x : atom) (a1 a2 : A) (Γ : alist A),
      a2 ∈ range ((x, a1) :: Γ) <-> a2 = a1 \/ a2 ∈ range Γ.
  Proof.
    intros; now autorewrite with tea_rw_range tea_list.
  Qed.

  Lemma in_range_one : forall (x : atom) (a1 a2 : A),
      a2 ∈ range (x ~ a1) <-> a1 = a2.
  Proof.
    intros; now autorewrite with tea_rw_range tea_list.
  Qed.

  Lemma in_range_app : forall x (Γ1 Γ2 : alist A),
    x ∈ range (Γ1 ++ Γ2) <-> x ∈ range Γ1 \/ x ∈ range Γ2.
  Proof.
    intros; now autorewrite with tea_rw_range tea_list.
  Qed.

  Lemma in_range_map : forall {B} {f : A -> B} (l : alist A) (b : B),
      b ∈ range (envmap f l) <-> exists a, a ∈ range l /\ f a = b.
  Proof.
    intros. autorewrite with tea_rw_range. now rewrite (in_map_iff list).
  Qed.

End in_range_lemmas.

#[export] Hint Rewrite in_range_nil in_range_one
  in_range_cons in_range_app in_range_map : tea_rw_range.

(** * Specifications for operations on association lists *)
(******************************************************************************)

(** ** Specifications for <<∈>> and [dom], [domset], [range] *)
(******************************************************************************)
Section in_operations_lemmas.

  Context
    {A : Type}
    (Γ : alist A).

  Ltac auto_star ::= intro; preprocess; eauto.

  Lemma in_dom_iff : forall (x : atom),
    x ∈ dom Γ <-> exists a : A, (x, a) ∈ (Γ : list (atom * A)).
  Proof.
    intros. unfold dom. rewrite (in_map_iff list).
    splits*.
  Qed.

  Lemma in_range_iff : forall a,
      a ∈ range Γ <-> exists x : atom, (x, a) ∈ (Γ : list (atom * A)).
  Proof.
    intros. unfold range. rewrite (in_map_iff list).
    splits*.
  Qed.

  Lemma in_domset_iff : forall x,
      x ∈@ domset Γ <-> exists a : A, (x, a) ∈ (Γ : list (atom * A)).
  Proof.
    unfold domset. intro x. rewrite <- in_atoms_iff.
    setoid_rewrite in_dom_iff. easy.
  Qed.

  Lemma in_domset_iff_dom : forall x,
      x ∈@ domset Γ <-> x ∈ dom Γ.
  Proof.
    intros. setoid_rewrite in_domset_iff.
    setoid_rewrite in_dom_iff. easy.
  Qed.

End in_operations_lemmas.

Section in_envmap_lemmas.

  Context
    {A B : Type}
    (l : alist A)
    (f : A -> B).

  Lemma in_range_envmap_iff : forall (b : B),
      b ∈ range (envmap f l) <->
      exists a : A, a ∈ range l /\ f a = b.
  Proof.
    intros. setoid_rewrite in_range_iff.
    setoid_rewrite in_envmap_iff.
    firstorder.
  Qed.

  Lemma in_dom_envmap_iff : forall (x : atom),
      x ∈ dom (envmap f l) <-> x ∈ dom l.
  Proof.
    intros. setoid_rewrite in_dom_iff.
    setoid_rewrite in_envmap_iff.
    firstorder eauto.
  Qed.

End in_envmap_lemmas.

Section in_in.

  Context (A B : Type).
  Implicit Types (x : atom) (a : A) (b : B).

  Lemma in_in_dom : forall x a Γ,
      (x, a) ∈ Γ ->
      x ∈ dom (A := A) Γ.
  Proof.
    setoid_rewrite in_dom_iff. eauto.
  Qed.

  Lemma in_in_domset : forall x a Γ,
      (x, a) ∈ Γ ->
      x ∈@ domset (A := A) Γ.
  Proof.
    setoid_rewrite in_domset_iff. eauto.
  Qed.

  Lemma in_in_range : forall x a Γ,
      (x, a) ∈ Γ ->
      a ∈ range (A := A) Γ.
  Proof.
    setoid_rewrite in_range_iff. eauto.
  Qed.

End in_in.

#[export] Hint Immediate in_in_dom in_in_domset in_in_range : tea_alist.

(** ** Support for prettifying association lists *)
(** The following rewrite rules can be used for normalizing
    alists. Note that we prefer <<one x ++ l>> to <<cons x l>>.  These
    rules are put into a rewrite hint database that can be invoked as
    <<simpl_alist>>. *)
(******************************************************************************)
Section alist_simpl_lemmas.

  Variable  X : Type.
  Variables x : X.
  Variables l l1 l2 l3 : list X.

  Lemma cons_app_one :
    cons x l = one x ++ l.
  Proof. clear. reflexivity. Qed.

  Lemma cons_app_assoc :
    (cons x l1) ++ l2 = cons x (l1 ++ l2).
  Proof. clear. reflexivity. Qed.

  Lemma app_assoc :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof. clear. auto with datatypes. Qed.

  Lemma app_nil_l :
    nil ++ l = l.
  Proof. clear. reflexivity. Qed.

  Lemma app_nil_r :
    l ++ nil = l.
  Proof. clear. auto with datatypes. Qed.

End alist_simpl_lemmas.

Create HintDb tea_simpl_alist.
#[export] Hint Rewrite cons_app_one cons_app_assoc : tea_simpl_alist.
#[export] Hint Rewrite app_assoc app_nil_l app_nil_r : tea_simpl_alist.

Ltac simpl_alist :=
  autorewrite with tea_simpl_alist.
Tactic Notation "simpl_alist" "in" hyp(H) :=
  autorewrite with tea_simpl_alist in H.
Tactic Notation "simpl_alist" "in" "*" :=
  autorewrite with tea_simpl_alist in *.

(** ** Tactics for normalizing alists *)
(******************************************************************************)
(** The tactic <<change_alist>> can be used to replace an alist with
    an equivalent form, as long as the two forms are equal after
    normalizing with <<simpl_alist>>. *)
Tactic Notation "change_alist" constr(E) :=
  match goal with
    | |- context[?x] =>
      change x with E
    | |- context[?x] =>
      replace x with E;
        [| simpl_alist; reflexivity ]
  end.

Tactic Notation "change_alist" constr(E) "in" hyp(H) :=
  match type of H with
    | context[?x] =>
      change x with E in H
    | context[?x] =>
      replace x with E in H;
        [| simpl_alist; reflexivity ]
  end.

(** ** Induction principles for alists *)
(** The tactic <<alist induction>> can be used for induction on
alists. The difference between this and ordinary induction on lists is
that the induction hypothesis is stated in terms of <<one>> and <<++>>
rather than <<cons>>.*)
(******************************************************************************)
Lemma alist_ind : forall (A : Type) (P : alist A -> Type),
    P nil ->
    (forall x a xs, P xs -> P (x ~ a ++ xs)) ->
    (forall xs, P xs).
Proof.
  induction xs as [ | [x a] xs ].
  auto.
  change (P (x ~ a ++ xs)). auto.
Defined.

Tactic Notation "alist" "induction" ident(E) :=
  try (intros until E);
  let T := type of E in
  let T := eval compute in T in
      match T with
      | list (?key * ?A) => induction E using (alist_ind A)
      end.

Tactic Notation "alist" "induction" ident(E) "as" simple_intropattern(P) :=
  try (intros until E);
  let T := type of E in
  let T := eval compute in T in
      match T with
      | list (?key * ?A) => induction E as P using (alist_ind A)
      end.

(** <<uniq l>> whenever the keys of <<l>> contain no duplicates. *)
Inductive uniq {A} : alist A -> Prop :=
| uniq_nil : uniq nil
| uniq_push : forall (x : atom) (v : A) ( Γ : alist A),
    uniq  Γ -> ~ x ∈@ domset  Γ -> uniq (x ~ v ++  Γ).

(** <<disjoint E F>> whenever the keys of <<E>> and <<F>> contain no
common elements. *)
Definition disjoint {A B} (Γ1 : alist A) (Γ2 : alist B) :=
  domset Γ1 ∩ domset Γ2 [=] ∅.

(** ** Rewriting principles for [disjoint] *)
(******************************************************************************)
Section disjoint_rewriting_lemmas.

  Context
    (A B C : Type).

  Lemma disjoint_sym : forall (Γ1 : alist A) (Γ2 : alist B),
    disjoint Γ1 Γ2 <-> disjoint Γ2 Γ1.
  Proof.
    intros. unfold disjoint. split; fsetdec.
  Qed.

  Lemma disjoint_nil_l : forall (Γ : alist A),
      disjoint (nil : alist A) Γ <-> True.
  Proof.
    unfold disjoint. fsetdec.
  Qed.

  Lemma disjoint_nil_r : forall (Γ : alist A),
      disjoint Γ (nil : alist B) <-> True.
  Proof.
    intros. rewrite disjoint_sym. now rewrite disjoint_nil_l.
  Qed.

  Lemma disjoint_cons_l : forall (x : atom) (a : A) (Γ1 : alist A) (Γ2 : alist B),
      disjoint ((x, a) :: Γ1) Γ2 <-> ~ x ∈@ domset Γ2 /\ disjoint Γ1 Γ2.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_cons_r : forall (x : atom) (b : B) (Γ1 : alist A) (Γ2 : alist B),
      disjoint Γ1 ((x, b) :: Γ2) <-> ~ x ∈@ domset Γ1 /\ disjoint Γ1 Γ2.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_one_l : forall (x : atom) (a : A) (Γ2 : alist B),
      disjoint (x ~ a) Γ2 <-> ~ x ∈@ domset Γ2.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_one_r : forall (x : atom) (b : B) (Γ1 : alist A),
      disjoint Γ1 (x ~ b) <-> ~ x ∈@ domset Γ1.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_app_l : forall (Γ1 Γ2 : alist A) (Γ3 : alist B),
      disjoint (Γ1 ++ Γ2) Γ3 <-> disjoint Γ1 Γ3 /\ disjoint Γ2 Γ3.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_app_r : forall (Γ1 Γ2 : alist A) (Γ3 : alist B),
      disjoint Γ3 (Γ1 ++ Γ2) <-> disjoint Γ1 Γ3 /\ disjoint Γ2 Γ3.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_map_l : forall (Γ1 : alist A) (Γ2 : alist B) (f : A -> C),
      disjoint (envmap f Γ1) Γ2 <-> disjoint Γ1 Γ2.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    reflexivity.
  Qed.

  Lemma disjoint_map_r : forall (Γ1 : alist A) (Γ2 : alist B) (f : A -> C),
    disjoint Γ2 (envmap f Γ1) <-> disjoint Γ1 Γ2.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

End disjoint_rewriting_lemmas.

Create HintDb tea_rw_disj.
#[export] Hint Rewrite @disjoint_nil_l @disjoint_nil_r @disjoint_cons_l @disjoint_cons_r
     @disjoint_one_l @disjoint_one_r @disjoint_app_l @disjoint_app_r
     @disjoint_map_l @disjoint_map_r : tea_rw_disj.



(** ** Tactical lemmas for [disjoint] *)
(******************************************************************************)
Section disjoint_auto_lemmas.

  Context
    {A B C : Type}.

  Implicit Types (a : A) (b : B).

  Lemma disjoint_sym1 : forall (Γ1 : alist A) (Γ2 : alist B),
      disjoint Γ1 Γ2 ->
      disjoint Γ2 Γ1.
  Proof.
    intros. now rewrite disjoint_sym.
  Qed.

  Lemma disjoint_app1 : forall  (Γ1 Γ2 : alist A) (Γ3 : alist B),
      disjoint (Γ1 ++ Γ2) Γ3 ->
      disjoint Γ1 Γ3.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_app2 : forall (Γ1 Γ2 : alist A) (Γ3 : alist B),
      disjoint (Γ1 ++ Γ2) Γ3 ->
      disjoint Γ2 Γ3.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_app_3 : forall (Γ1 Γ2 : alist A) (Γ3 : alist B),
      disjoint Γ1 Γ3 ->
      disjoint Γ2 Γ3 ->
      disjoint (Γ1 ++ Γ2) Γ3.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_envmap1 : forall (Γ1 : alist A) (Γ2 : alist B) (f : A -> C),
      disjoint (envmap f Γ1) Γ2 ->
      disjoint Γ1 Γ2.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_envmap2 : forall (Γ1 : alist A) (Γ2 : alist B) (f : A -> C),
      disjoint Γ1 Γ2 ->
      disjoint (envmap f Γ1) Γ2.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_one_l1 : forall x a (Γ : alist B),
      disjoint (x ~ a) Γ -> ~ x ∈@ domset Γ.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_one_l2 : forall x a (Γ : alist B),
      ~ x ∈@ domset Γ -> disjoint (x ~ a) Γ.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_cons_hd : forall x a (Γ1 : alist A) (Γ2 : alist B),
      disjoint ((x, a) :: Γ1) Γ2 -> ~ x ∈@ domset Γ2.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_cons_hd_one : forall x a (Γ1 : alist A) (Γ2 : alist B),
      disjoint (x ~ a ++ Γ1) Γ2 -> ~ x ∈@ domset Γ2.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_cons_tl : forall x a (Γ1 : alist A) (Γ2 : alist B),
      disjoint ((x, a) :: Γ1) Γ2 -> disjoint Γ1 Γ2.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_dom1 : forall x (Γ1 : alist A) (Γ2 : alist B),
      disjoint Γ1 Γ2 ->
      x ∈@ domset Γ1 ->
      ~ x ∈@ domset Γ2.
  Proof.
    unfold disjoint in *. fsetdec.
  Qed.

  Lemma disjoint_dom2 : forall x (Γ1 : alist A) (Γ2 : alist B),
      disjoint Γ1 Γ2 ->
      x ∈@ domset Γ2 ->
      ~ x ∈@ domset Γ1.
  Proof.
    unfold disjoint in *. fsetdec.
  Qed.

  Lemma disjoint_binds1 : forall x a (Γ1 : alist A) (Γ2 : alist A),
      disjoint Γ1 Γ2 ->
      (x, a) ∈ (Γ1 : list (prod atom A)) ->
      ~ (x, a) ∈ (Γ2 : list (prod atom A)).
  Proof.
    introv Hdisj He Hf.
    apply in_in_domset in He.
    apply in_in_domset in Hf.
    unfold disjoint in *.
    fsetdec.
  Qed.

  Lemma disjoint_binds2 : forall x a (Γ1 : alist A) (Γ2 : alist A),
      disjoint Γ1 Γ2 ->
      (x, a) ∈ (Γ1 : list (prod atom A)) ->
      ~ (x, a) ∈ (Γ2 : list (prod atom A)).
  Proof.
    introv Hd Hf.
    eauto using disjoint_binds1.
  Qed.

End disjoint_auto_lemmas.

#[export] Hint Resolve disjoint_sym1 disjoint_app_3
 disjoint_envmap2 : tea_alist.

(** These introduce existential variables, so only
apply them if they immediately solve the goal. *)
#[export] Hint Immediate disjoint_app1 disjoint_app2
 disjoint_one_l1 disjoint_envmap1
 disjoint_dom1 disjoint_dom2
 disjoint_binds1 disjoint_binds2 : tea_alist.

(** ** Tactical lemmas for [uniq] *)
(** For automating proofs about uniqueness, it is typically easier to
work with (one-way) lemmas rather than rewriting principles, in
contrast to most of the other parts of Tealeaves internals. *)
(******************************************************************************)
Section uniq_auto_lemmas.

  Context
    (A B : Type)
    (Γ1 Γ2 : alist A).

  Implicit Types (x : atom) (a : A) (b : B).

  Lemma uniq_one : forall x a,
      uniq (x ~ a).
  Proof.
    intros. change_alist ((x ~ a) ++ nil).
    constructor; [constructor | fsetdec].
  Qed.

  Lemma uniq_cons1 : forall x a,
      uniq ((x, a) :: Γ1) ->
      uniq Γ1.
  Proof.
    now inversion 1.
  Qed.

  Lemma uniq_cons2 : forall x a,
      uniq ((x, a) :: Γ1) ->
      ~ x ∈@ domset Γ1.
  Proof.
    now inversion 1.
  Qed.

  Lemma uniq_cons_3 : forall x a,
      ~ x ∈@ domset Γ1 ->
      uniq Γ1 ->
      uniq ((x, a) :: Γ1).
  Proof.
    intros. constructor; auto.
  Qed.

  Lemma uniq_app1 :
      uniq (Γ1 ++ Γ2) ->
      uniq Γ1.
  Proof.
    introv Hu. alist induction Γ1.
    - constructor.
    - simpl_alist in Hu. inverts Hu.
      autorewrite with tea_rw_dom in *.
      constructor; tauto.
  Qed.

  Lemma uniq_app2 :
      uniq (Γ1 ++ Γ2) ->
      uniq Γ2.
  Proof.
    introv Hu. alist induction Γ1.
    - trivial.
    - inverts Hu. auto.
  Qed.

  Lemma uniq_app_3 :
      uniq (Γ1 ++ Γ2) ->
      disjoint Γ1 Γ2.
  Proof.
    introv Hu. unfold disjoint. alist induction Γ1 as [| ? ? ? IH].
    - fsetdec.
    - inverts Hu. autorewrite with tea_rw_dom in *.
      lapply IH.
      + fsetdec.
      + auto.
  Qed.

  Lemma uniq_app_4 : forall C (Γx : alist C) (Γy : alist C),
      uniq Γx ->
      uniq Γy ->
      disjoint Γx Γy ->
      uniq (Γx ++ Γy).
  Proof.
    intros. alist induction Γx as [| ? ? Γz ?].
    - cbn. assumption.
    - change_alist (x ~ a ++ (Γz ++ Γy)).
      inverts H. autorewrite with tea_rw_disj in *. constructor.
      + tauto.
      + now autorewrite with tea_rw_dom.
  Qed.

  Lemma uniq_app_5 : forall x a Γ,
      uniq (x ~ a ++ Γ) ->
      ~ x ∈@ domset Γ.
  Proof.
    now inversion 1.
  Qed.

  (* For some reason, [uniq_app_4] will not be applied
     by auto on this goal. *)
  Lemma uniq_symm :
      uniq (Γ1 ++ Γ2) ->
      uniq (Γ2 ++ Γ1).
  Proof.
    intros. eapply uniq_app_4.
    all: eauto using uniq_app_4, uniq_app2,
         uniq_app1, uniq_app_3, disjoint_sym1.
  Qed.

  Lemma uniq_envmap1 : forall (f : A -> B),
      uniq (envmap f Γ1) ->
      uniq Γ1.
  Proof.
    introv Hu. alist induction Γ1.
    - constructor.
    - autorewrite with tea_rw_envmap in *. inverts Hu.
      constructor.
      + auto.
      + now autorewrite with tea_rw_dom in *.
  Qed.

  Lemma uniq_envmap2 : forall (f : A -> B),
      uniq Γ1 ->
      uniq (envmap f Γ1).
  Proof.
    introv Hu. alist induction Γ1.
    - constructor.
    - autorewrite with tea_rw_envmap. inverts Hu.
      constructor.
      + auto.
      + now autorewrite with tea_rw_dom in *.
  Qed.

  Lemma uniq_map1 : forall (f : A -> B),
      uniq (map (list ∘ prod atom) f Γ1) ->
      uniq Γ1.
  Proof.
    intros. eapply uniq_envmap1. exact H.
  Qed.

  Lemma uniq_map2 : forall (f : A -> B),
      uniq Γ1 ->
      uniq (map (list ∘ prod atom) f Γ1).
  Proof.
    intros. now apply uniq_envmap2.
  Qed.

End uniq_auto_lemmas.

#[export] Hint Resolve uniq_nil uniq_push uniq_one
 uniq_cons_3 uniq_app_3 uniq_app_4 uniq_envmap2 uniq_symm : tea_alist.

(** These introduce existential variables *)
#[export] Hint Immediate uniq_cons1
 uniq_cons2 uniq_app1 uniq_app2
 uniq_app_5 uniq_envmap1 : tea_alist.

(** ** Rewriting principles for [uniq] *)
(* *********************************************************************** *)
Section uniq_rewriting_lemmas.

  Context
    (A B : Type).

  Implicit Types (x : atom) (a : A) (b : B) (Γ : alist A).

  Lemma uniq_nil_iff :
    uniq ([] : list (atom * A)) <-> True.
  Proof.
    split; auto with tea_alist.
  Qed.

  Lemma uniq_cons_iff : forall x a Γ,
      uniq ((x, a) :: Γ) <->  ~ x ∈@ domset Γ /\ uniq Γ.
  Proof.
    split.
    - eauto with tea_alist.
    - intuition auto with tea_alist.
  Qed.

  Lemma uniq_one_iff : forall x b,
      uniq (x ~ b) <-> True.
  Proof.
    split; auto with tea_alist.
  Qed.

  Lemma uniq_app_iff : forall Γ1 Γ2,
      uniq (Γ1 ++ Γ2) <-> uniq Γ1 /\ uniq Γ2 /\ disjoint Γ1 Γ2.
  Proof.
    intuition eauto with tea_alist.
  Qed.

  Lemma uniq_envmap_iff : forall Γ1 (f : A -> B),
      uniq (envmap f Γ1) <-> uniq Γ1.
  Proof.
    intuition eauto with tea_alist.
  Qed.

  Lemma uniq_map_iff : forall Γ1 (f : A -> B),
      uniq (map (list ∘ prod atom) f Γ1) <-> uniq Γ1.
  Proof.
    intros. now rewrite uniq_envmap_iff.
  Qed.

End uniq_rewriting_lemmas.

Create HintDb tea_rw_uniq.
#[export] Hint Rewrite uniq_nil_iff uniq_cons_iff
     uniq_one_iff uniq_app_iff uniq_envmap_iff uniq_map_iff : tea_rw_uniq.

(** ** More facts about [uniq] *)
(* *********************************************************************** *)
Section uniq_theorems.

  Context
    (A : Type).

  Implicit Types (x : atom) (a b : A) (Γ : list (atom * A)).

  Lemma uniq_insert_mid : forall x a Γ1 Γ2,
    uniq (Γ1 ++ Γ2) ->
    ~ x ∈@ domset Γ1 ->
    ~ x ∈@ domset Γ2 ->
    uniq (Γ1 ++ x ~ a ++ Γ2).
  Proof.
    intros. autorewrite with tea_rw_uniq tea_rw_disj in *.
    rewrite disjoint_sym. intuition.
  Qed.

  Lemma uniq_remove_mid : forall Γ1 Γ2 Γ3,
    uniq (Γ1 ++ Γ3 ++ Γ2) ->
    uniq (Γ1 ++ Γ2).
  Proof.
    intros.
    autorewrite with tea_rw_uniq tea_rw_disj in *.
    unfold disjoint. intuition.
    now rewrite disjoint_sym in H4.
  Qed.

  Lemma uniq_reorder1 : forall Γ1 Γ2,
    uniq (Γ1 ++ Γ2) ->
    uniq (Γ2 ++ Γ1).
  Proof.
    intros. now apply uniq_symm.
  Qed.

  Lemma uniq_reorder2 : forall Γ1 Γ2 Γ3,
    uniq (Γ1 ++ Γ3 ++ Γ2) ->
    uniq (Γ1 ++ Γ2 ++ Γ3).
  Proof.
    intros. autorewrite with tea_rw_uniq tea_rw_disj in *.
    unfold disjoint. rewrite <- (disjoint_sym _ _ Γ2 Γ3) in *.
    intuition.
  Qed.

  Lemma uniq_map_app_l : forall Γ1 Γ2 (f : A -> A),
    uniq (Γ1 ++ Γ2) ->
    uniq (envmap f Γ1 ++ Γ2).
  Proof.
    intros. autorewrite with tea_rw_uniq tea_rw_disj in *.
    tauto.
  Qed.

  Lemma fresh_mid_tail : forall x a Γ1 Γ2,
    uniq (Γ1 ++ x ~ a ++ Γ2) ->
    ~ x ∈@ domset Γ2.
  Proof.
    intros. autorewrite with tea_rw_uniq tea_rw_disj in *.
    tauto.
  Qed.

  Lemma fresh_mid_head : forall x a Γ1 Γ2,
    uniq (Γ1 ++ x ~ a ++ Γ2) ->
    ~ x ∈@ domset Γ1.
  Proof.
    intros. autorewrite with tea_rw_uniq tea_rw_disj in *.
    tauto.
  Qed.

End uniq_theorems.

(** ** Stronger theorems for <<∈>> on [uniq] lists *)
(******************************************************************************)
Section in_theorems_uniq.

  Context
    (A B : Type).

  Implicit Types (x : atom) (a : A) (b : B).

  Lemma in_app_uniq_iff : forall x a Γ1 Γ2,
      uniq (Γ1 ++ Γ2) ->
      (x, a) ∈ (Γ1 ++ Γ2) <->
      ((x, a) ∈ Γ1 /\ ~ x ∈@ domset Γ2) \/
      ((x, a) ∈ Γ2 /\ ~ x ∈@ domset Γ1).
  Proof.
    introv H. autorewrite with tea_rw_uniq tea_rw_in in *.
    destructs H. split.
    - intros [inΓ1|inΓ2].
      + left. split.
        * auto.
        * eauto using disjoint_dom1 with tea_alist.
      + right. split.
        * auto.
        * eauto using disjoint_dom1 with tea_alist.
    - tauto.
  Qed.

  Lemma in_cons_uniq_iff : forall x y (a b : A) Γ,
    uniq ((y, b) :: Γ) ->
    (x, a) ∈ ((y, b) :: Γ) <->
     (x = y /\ a = b /\ ~ x ∈@ domset Γ) \/
     ((x, a) ∈ Γ /\ x <> y).
  Proof.
    introv. change_alist (y ~ b ++ Γ).
    intro. rewrite in_app_uniq_iff; auto.
    autorewrite with tea_rw_in tea_rw_dom.
    tauto.
  Qed.

End in_theorems_uniq.

(** * Facts about [binds] *)
(* *********************************************************************** *)
Section binds_theorems.

  Context
    (A : Type).

  Implicit Types
    (x y : atom)
    (a b : A)
    (Γ : list (atom * A)).

  Lemma in_decide : forall x a Γ,
    (forall a b : A, {a = b} + {a <> b}) ->
    {(x, a) ∈ Γ} + {~ (x, a) ∈ Γ}.
  Proof.
    clear. intros. alist induction Γ.
    - right. auto.
    - destruct IHΓ.
      + left. simpl_list. now right.
      + compare values x and x0.
        { destruct (X a a0); subst.
          - left. now left.
          - right. simpl_list. intros [hyp|hyp].
            inversion hyp; contradiction. contradiction. }
        { right. intros [hyp|hyp].
          inversion hyp; contradiction. contradiction. }
  Defined.

  Lemma in_lookup : forall x Γ,
    {a : A | (x, a) ∈ Γ} + (forall a, ~ (x, a) ∈ Γ).
  Proof.
    clear. intros. induction Γ.
    - simpl_list; cbn; now right.
    - destruct a as [y a]. destruct IHΓ.
      + destruct s. left. eexists. right. eauto.
      + compare values x and y.
        { left. exists a. now left. }
        { right. introv. simpl_list.
          intros [contra|contra].
          - inversion contra; subst. contradiction.
          - eapply n; eauto.
        }
  Defined.

  Lemma in_decidable : forall x Γ,
    decidable (exists a, (x, a) ∈ Γ).
  Proof with intuition eauto.
    intros. unfold decidable.
    destruct (in_lookup x Γ) as [[? ?] | ?]...
    right. intros [? ?]...
  Defined.

  Lemma in_weaken1 : forall x a Γ1 Γ2 Γ3,
    (x, a) ∈ (Γ1 ++ Γ3) ->
    (x, a) ∈ (Γ1 ++ Γ2 ++ Γ3).
  Proof.
    clear. intros. simpl_list in *. intuition.
  Qed.

  Lemma binds_mid_eq : forall x a b Γ1 Γ2,
    (x, a) ∈ (Γ1 ++ (x ~ b) ++ Γ2) ->
    uniq (Γ1 ++ (x ~ b) ++ Γ2) ->
    a = b.
  Proof.
    introv J ?.
    autorewrite with tea_rw_uniq tea_rw_disj in *.
    simpl_list in *. destruct J.
    - intuition. contradiction H. rewrite in_domset_iff. eauto.
    - destruct H0; subst.
      + now inversion H0.
      + intuition. contradiction H6. rewrite in_domset_iff. eauto.
  Qed.

  Lemma binds_remove_mid : forall x y a b Γ1 Γ2,
    (x, a) ∈ (Γ1 ++ (y ~ b) ++ Γ2) ->
    x <> y ->
    (x, a) ∈ (Γ1 ++ Γ2).
  Proof.
    introv J. simpl_list in *.
    intros. intuition (preprocess; easy).
  Qed.

  Lemma in_unique : forall x a b Γ,
    (x, a) ∈ Γ ->
    (x, b) ∈ Γ ->
    uniq Γ ->
    a = b.
  Proof.
    introv hyp1 hyp2 Hu. alist induction Γ as [ | ? ? Γ' IH ].
    - inversion hyp1.
    - simpl_list in *. destruct hyp1 as [hyp1|hyp1];
                         destruct hyp2 as [hyp2|hyp2].
      + inverts hyp1. now inverts hyp2.
      + inverts hyp1. inverts Hu.
        now (apply in_in_domset in hyp2).
      + inverts hyp2. inverts Hu.
        now (apply in_in_domset in hyp1).
      + inverts Hu. auto.
  Qed.

  Lemma fresh_app_l : forall x a Γ1 Γ2,
    uniq (Γ1 ++ Γ2) ->
    (x, a) ∈ Γ1 ->
    ~ x ∈@ (domset Γ2).
  Proof.
    intros. autorewrite with tea_rw_uniq in *.
    preprocess. apply in_in_domset in H0.
    eauto with tea_alist.
  Qed.

  Lemma fresh_app_r : forall x a Γ1 Γ2,
    uniq (Γ1 ++ Γ2) ->
    (x, a) ∈ Γ2 ->
    ~ x ∈@ domset Γ1.
  Proof.
    intros. autorewrite with tea_rw_uniq in *.
    preprocess. apply in_in_domset in H0.
    rewrite disjoint_sym in H2.
    eauto with tea_alist.
  Qed.

  (* If x is in an alist, it is either in the front half or
   the back half. *)
  Lemma in_split : forall x a Γ,
    (x, a) ∈ Γ -> exists Γ1 Γ2, Γ = Γ1 ++ x ~ a ++ Γ2.
  Proof.
    introv Hin. induction Γ.
    - now simpl_list in *.
    - destruct a0 as [z a']. simpl_list in *.
      destruct Hin as [Hin|Hin].
      + inverts Hin. exists (@nil (atom * A)) Γ. reflexivity.
      + specialize (IHΓ Hin). destruct IHΓ as [Γ1 [Γ2 rest]].
        subst. exists ((z, a') :: Γ1) Γ2. reflexivity.
  Qed.

End binds_theorems.

(** ** Permutation lemmas *)
(*******************************************************************************)
Section permute_lemmas.

  Context
    {A : Type}
    (l1 l2 : alist A)
    (Hperm : Permutation l1 l2).

  Lemma perm_dom : forall (x : atom),
      x ∈ dom l1 <-> x ∈ dom l2.
  Proof.
    setoid_rewrite in_dom_iff.
    setoid_rewrite (List.perm_set_eq Hperm).
    reflexivity.
  Qed.

  Lemma perm_domset :
    domset l1 [=] domset l2.
  Proof.
    unfold domset.
    intro a; rewrite <- 2(in_atoms_iff).
    apply perm_dom.
  Qed.

  Lemma perm_range : forall (a : A),
      a ∈ range l1 <-> a ∈ range l2.
  Proof.
    setoid_rewrite in_range_iff.
    setoid_rewrite (List.perm_set_eq Hperm).
    reflexivity.
  Qed.

  Lemma perm_disjoint_l : forall (l3 : alist A),
      disjoint l1 l3 <-> disjoint l2 l3.
  Proof.
    intros. unfold disjoint. now rewrite perm_domset.
  Qed.

  Lemma perm_disjoint_r : forall (l3 : alist A),
      disjoint l3 l1 <-> disjoint l3 l2.
  Proof.
    intros. unfold disjoint. now rewrite perm_domset.
  Qed.

End permute_lemmas.

Lemma uniq_perm : forall (A : Type) (l1 l2 : alist A),
    Permutation l1 l2 ->
    uniq l1 <-> uniq l2.
Proof.
  introv J. induction J.
  - reflexivity.
  - destruct x. autorewrite with tea_rw_uniq.
    rewrite IHJ, perm_domset; eauto. tauto.
  - destruct x, y. autorewrite with tea_rw_uniq tea_rw_dom.
    intuition.
  - tauto.
Qed.

Lemma binds_perm : forall (A : Type) (l1 l2 : list (atom * A)) (x : atom) (a : A),
    Permutation l1 l2 -> (x, a) ∈ l1 <-> (x, a) ∈ l2.
Proof.
  intros. now erewrite List.perm_set_eq; eauto.
Qed.

Create HintDb tea_rw_perm.
#[export] Hint Rewrite @perm_dom @perm_range @perm_domset @perm_disjoint_l @perm_disjoint_r
     @uniq_perm using (auto; try symmetry; auto) : tea_rw_perm.

(** For any given finite set of atoms, we can generate an atom fresh
    for it. *)
Lemma atom_fresh : forall L : AtomSet.t, { x : atom | ~ x ∈@ L }.
Proof.
  intros L. destruct (atom_fresh_for_list (AtomSet.elements L)) as [a H].
  rewrite <- in_elements_iff in H.
  now exists a.
Qed.

(** * Tactic support for picking fresh atoms *)
(* ********************************************************************** *)

Ltac ltac_remove_dups xs :=
  let rec remove xs acc :=
    match xs with
      | List.nil => acc
      | List.cons ?x ?xs =>
        match acc with
          | context [x] => remove xs acc
          | _ => remove xs (List.cons x acc)
        end
    end
  in
  match type of xs with
    | List.list ?A =>
      let xs := eval simpl in xs in
      let xs := remove xs (@List.nil A) in
      eval simpl in (List.rev xs)
  end.

(** The auxiliary tactic [simplify_list_of_atom_sets] takes a list of
    finite sets of atoms and unions everything together, returning the
    resulting single finite set. *)
Ltac simplify_list_of_atom_sets L :=
  let L := eval simpl in L in
  let L := ltac_remove_dups L in
  let L := eval simpl in (List.fold_right AtomSet.union AtomSet.empty L) in
  match L with
    | context C [AtomSet.union ?E AtomSet.empty] => context C [ E ]
  end.

(** [gather_atoms_with F] returns the union of all the finite sets
    [F x] where [x] is a variable from the context such that [F x]
    type checks. *)

Ltac gather_atoms_with F :=
  let apply_arg x :=
    match type of F with
      | _ -> _ -> _ -> _ => constr:(@F _ _ x)
      | _ -> _ -> _ => constr:(@F _ x)
      | _ -> _ => constr:(@F x)
    end in
  let rec gather V :=
    match goal with
      | H : _ |- _ =>
        let FH := apply_arg H in
        match V with
          | context [FH] => fail 1
          | _ => gather (AtomSet.union FH V)
        end
      | _ => V
    end in
  let L := gather AtomSet.empty in eval simpl in L.

(** [beautify_fset V] assumes that [V] is built as a union of finite
    sets and returns the same set cleaned up: empty sets are removed
    and items are laid out in a nicely parenthesized way. *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | AtomSet.union ?E1 ?E2 => let Acc2 := go Acc E2 in go Acc2 E1
     | AtomSet.empty => Acc
     | ?E1 => match Acc with
                | AtomSet.empty => E1
                | _ => constr:(AtomSet.union E1 Acc)
              end
     end
  in go AtomSet.empty V.

(** The tactic [pick fresh Y for L] takes a finite set of atoms [L]
    and a fresh name [Y], and adds to the context an atom with name
    [Y] and a proof that [~ In Y L], i.e., that [Y] is fresh for [L].
    The tactic will fail if [Y] is already declared in the context.
    The variant [pick fresh Y] is similar, except that [Y] is fresh
    for "all atoms in the context."  This version depends on the
    tactic [gather_atoms], which is responsible for returning the set
    of "all atoms in the context."  By default, it returns the empty
    set, but users are free (and expected) to redefine it. *)

Ltac gather_atoms :=
  constr:(AtomSet.empty).

Tactic Notation "pick" "fresh" ident(Y) "for" constr(L) :=
  let Fr := fresh "Hfresh" in
  let L := beautify_fset L in
  (destruct (atom_fresh L) as [Y Fr]).

Tactic Notation "pick" "fresh" ident(Y) :=
  let L := gather_atoms in
  pick fresh Y for L.

Ltac pick_fresh y :=
  pick fresh y.

(** Example: We can redefine [gather_atoms] to return all the
    "obvious" atoms in the context using the [gather_atoms_with] thus
    giving us a "useful" version of the "[pick fresh]" tactic. *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : AtomSet.t => x) in
  let B := gather_atoms_with (fun x : atom => AtomSet.singleton x) in
  constr:(AtomSet.union A B).

Lemma example_pick_fresh_use : forall (x y z : atom) (L1 L2 L3 : AtomSet.t), True.
(* begin show *)
Proof.
  intros x y z L1 L2 L3.
  pick fresh k.

  (** At this point in the proof, we have a new atom [k] and a
      hypothesis [Fr] that [k] is fresh for [x], [y], [z], [L1], [L2],
      and [L3]. *)

  trivial.
Qed.

Tactic Notation
  "pick" "fresh" ident(atom_name)
  "excluding" constr(L)
  "and" "apply" constr(H)
  :=
    first [apply (@H L) | eapply (@H L)];
      match goal with
        | |- forall _, ~ AtomSet.In _ _ -> _ =>
          let Fr := fresh "Fr" in intros atom_name Fr
        | |- forall _, ~ AtomSet.In _ _ -> _ =>
          fail 1 "because" atom_name "is already defined"
        | _ =>
          idtac
      end.

Tactic Notation
  "pick" "fresh" ident(atom_name)
  "and" "apply" constr(H)
  :=
    let L := gather_atoms in
    let L := beautify_fset L in
    pick fresh atom_name excluding L and apply H.

Ltac specialize_cof H e :=
  specialize (H e ltac:(fsetdec)).

Ltac specialize_freshly H :=
  let e := fresh "e" in
  pick fresh e;
  specialize_cof H e.

(** When the goal is a cofinite quantification, introduce a new atom
      and specialize assumption H to this variable. *)
Ltac intros_cof H :=
  match goal with
  | |- forall e, ~ AtomSet.In e _ -> _ =>
    match type of H with
    | forall e, ~ AtomSet.In _ _ -> _ =>
      let e := fresh "e" in
      let Notin := fresh "Notin" in
      intros e Notin; specialize_cof H e
    | _ => fail "Argument should be cofinitely quantified hypothesis"
    end
  end.

Ltac apply_cof H :=
  intros_cof H; apply H.

Ltac eapply_cof H :=
  intros_cof H; eapply H.

Ltac cleanup_cofinite :=
  repeat
    match goal with
    | H : forall e, ?x |- _ => specialize_freshly H
    end.

Ltac cc := cleanup_cofinite.
