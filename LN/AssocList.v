From Tealeaves Require Import
     Util.Prelude
     Util.LibTactics
     LN.Atom LN.AtomSet
     Singlesorted.Theory.Product
     Singlesorted.Classes.SetlikeFunctor
     Singlesorted.Classes.ListableFunctor
     Singlesorted.Functors.Writer.

From Coq Require Import
     Logic.Decidable
     Sorting.Permutation.

Import List.ListNotations.
Import LN.AtomSet.Notations.
Import SetlikeFunctor.Notations.
Local Open Scope tealeaves_scope.
Local Open Scope set_scope.

Create HintDb tea_alist.

(** * Miscellaneous tactics *)
Lemma nin_app_iff : forall X (x : X) (l1 l2 : list X),
    ~ x ∈ (l1 ++ l2) <-> ~ x ∈ l1 /\ ~ x ∈ l2.
Proof.
  intros. rewrite List.in_list_app.
  firstorder.
Qed.

Lemma push_not : forall P Q,
    ~ (P \/ Q) <-> ~P /\ ~ Q.
Proof.
  firstorder.
Qed.

(** TODO : Put this somewhere useful *)
Hint Rewrite push_not : tea_rw_dom.

(** * The [alist] functor *)
(* An association list is a list of pairs of type <<atom * A>>.  A
functor instance is provided by mapping over <<A>>, leaving atoms
alone.  Technically the functor is the composition of [list] and
<<prod atom>>. *)
Module Notations.
  Notation "'one'" := (ret list).
  Notation "x ~ a" := (ret list (x, a)) (at level 50).
  Notation "'alist' A" := (list (atom * A)) (at level 50, no associativity).
End Notations.

Import Notations.

(** ** Functor instance for [alist] *)
Instance Fmap_alist : Fmap (fun A => alist A) :=
  fun (A B : Type) => fmap (list ∘ prod atom).

Instance Functor_alist : Functor (fun A => list (atom * A)).
Proof.
  constructor; intros; unfold_ops @Fmap_alist @Fmap_compose.
  - now rewrite 2(fun_fmap_id _).
  - now rewrite 2(fun_fmap_fmap _).
Qed.

(** Envmap is just [fmap] specialized to <<alist>>. It is given a
slightly more friendly name, primarily to avoid
writing <<fun A => alist A>> all the time. *)
Definition envmap {A B} (f : A -> B) : alist A -> alist B :=
  fmap (fun A => alist A) f.

(** ** Operations on association lists *)

(** [dom] computes the list of keys of an association list. *)
Definition dom {A} (E : alist A) : list atom :=
  fmap list fst E.

(** [domset] computes the keys as an [AtomSet.t] for use with <<fsetdec>>. *)
Definition domset {A} (E : alist A) : AtomSet.t :=
  atoms (dom E).

(** [range] computes the list of values of an association list. *)
Definition range {A} (E : alist A) : list A :=
  fmap list (extract (prod atom)) E.

(** <<uniq l>> whenever the keys of <<l>> contain no duplicates. *)
Inductive uniq {A} : alist A -> Prop :=
| uniq_nil : uniq nil
| uniq_push : forall (x : atom) (v : A) (E : alist A),
    uniq E -> ~ x ∈@ domset E -> uniq (x ~ v ++ E).

(** <<disjoint E F>> whenever the keys of <<E>> and <<F>> contain no
common elements. *)
Definition disjoint {A B} (E : alist A) (F : alist B) :=
  domset E ∩ domset F [=] ∅.

(** ** Support for prettifying association lists *)
(** The following rewrite rules can be used for normalizing
    alists. Note that we prefer <<one x ++ l>> to <<cons x l>>.  These
    rules are put into a rewrite hint database that can be invoked as
    <<simpl_alist>>. *)
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
Hint Rewrite cons_app_one cons_app_assoc : tea_simpl_alist.
Hint Rewrite app_assoc app_nil_l app_nil_r : tea_simpl_alist.

Ltac simpl_alist :=
  autorewrite with tea_simpl_alist.
Tactic Notation "simpl_alist" "in" hyp(H) :=
  autorewrite with tea_simpl_alist in H.
Tactic Notation "simpl_alist" "in" "*" :=
  autorewrite with tea_simpl_alist in *.

(** *** Rewriting alists *)
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

(** ** Induction principles for association lists *)
(** The tactic <<alist induction>> can be used for induction on
alists. The difference between this and ordinary induction on lists is
that the induction hypothesis is stated in terms of <<one>> and <<++>>
rather than <<cons>>.*)
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

(** ** Specifications for [∈] and [dom], [domset], [range], [envmap]  *)
Section in_operations_lemmas.

  Context
    {A : Type}
    (l : alist A).

  Ltac auto_star ::= intro; preprocess; eauto.

  Lemma in_dom_iff : forall x,
    x ∈ dom l <-> exists a : A, (x, a) ∈ l.
  Proof.
    intros. unfold dom. rewrite (in_fmap_iff list).
    splits*.
  Qed.

  Lemma in_range_iff : forall a,
      a ∈ range l <-> exists x : atom, (x, a) ∈ l.
  Proof.
    intros. unfold range. rewrite (in_fmap_iff list).
    splits*.
  Qed.

  Lemma in_domset_iff : forall x,
      x ∈@ domset l <-> exists a : A, (x, a) ∈ l.
  Proof.
    unfold domset. setoid_rewrite in_atoms_iff.
    setoid_rewrite in_dom_iff. easy.
  Qed.

  Lemma in_domset_iff_dom : forall x,
      x ∈@ domset l <-> x ∈ dom l.
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

  Lemma in_envmap_iff : forall x b,
      (x, b) ∈ envmap f l <->
      exists a : A, (x, a) ∈ l /\ f a = b.
  Proof.
    intros. unfold envmap. unfold_ops @Fmap_alist @Fmap_compose @Fmap_prod.
    rewrite (in_fmap_iff list). split; intros; preprocess; eauto.
  Qed.

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

(** ** Rewriting principles for [envmap] *)
Section envmap_lemmas.

  Variables A B   : Type.
  Variable  f     : A -> B.
  Variable  x     : atom.
  Variable  a     : A.
  Variables E F G : list (atom * A).

  Lemma envmap_nil :
    envmap f (@nil (atom * A)) = nil.
  Proof.
    unfold envmap, fmap, Fmap_alist.
    simpl_list. trivial.
  Qed.

  Lemma envmap_one :
    envmap f (x ~ a) = (x ~ f a).
  Proof.
    reflexivity.
  Qed.

  Lemma envmap_cons :
    envmap f ((x, a) :: E) = x ~ f a ++ envmap f E.
  Proof.
    reflexivity.
  Qed.

  Lemma envmap_app :
    envmap f (E ++ F) = envmap f E ++ envmap f F.
  Proof.
    unfold envmap. unfold_ops @Fmap_alist @Fmap_compose.
    simpl_list. trivial.
  Qed.

End envmap_lemmas.

Create HintDb tea_rw_envmap.
Hint Rewrite envmap_nil envmap_one envmap_cons envmap_app :
  tea_rw_envmap.

(** ** Rewriting lemmas for [dom] *)
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

  Lemma dom_fmap : forall {B} {f : A -> B} (l : alist A),
      dom (envmap f l) = dom l.
  Proof.
    intros. unfold dom, envmap. compose near l on left.
    unfold_ops @Fmap_alist @Fmap_compose @Fmap_prod.
    rewrite (fun_fmap_fmap list). fequal. now ext [? ?].
  Qed.

End dom_lemmas.

Create HintDb tea_rw_dom.
Hint Rewrite dom_nil dom_cons dom_app dom_one dom_fmap : tea_rw_dom.

(** *** Elements of [dom] *)
Section in_dom_lemmas.

  Context
    (A : Type).

  Lemma in_dom_nil : forall x,
      x ∈ dom (@nil (atom * A)) <-> False.
  Proof.
    intros; now autorewrite with tea_rw_dom.
  Qed.

  Lemma in_dom_cons : forall (x y : atom) (a : A) (E : alist A),
      y ∈ dom ((x, a) :: E) <-> y = x \/ y ∈ dom E.
  Proof.
    intros; now autorewrite with tea_rw_dom tea_list.
  Qed.

  Lemma in_dom_one : forall (x y : atom) (a : A),
      y ∈ dom (x ~ a) <-> y = x.
  Proof.
    intros. now autorewrite with tea_rw_dom tea_list.
  Qed.

  Lemma in_dom_app : forall x (E F : alist A),
      x ∈ dom (E ++ F) <-> x ∈ dom E \/ x ∈ dom F.
  Proof.
    intros; now autorewrite with tea_rw_dom tea_list.
  Qed.

  Lemma in_dom_fmap : forall {B} {f : A -> B} (l : alist A) x,
      x ∈ dom (envmap f l) <-> x ∈ dom l.
  Proof.
    intros; now autorewrite with tea_rw_dom.
  Qed.

End in_dom_lemmas.

Hint Rewrite in_dom_nil in_dom_one in_dom_cons
     in_dom_app in_dom_fmap : tea_rw_dom.

(** ** Rewriting lemmas for [domset] *)
Section domset_lemmas.

  Context
    (A : Type).

  Lemma domset_nil :
    domset (@nil (atom * A)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma domset_cons : forall (x : atom) (a : A) (E : alist A),
      domset ((x, a) :: E) [=] {{ x }} ∪ domset E.
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

  Lemma domset_app : forall (l1 l2 : alist A),
      domset (l1 ++ l2) [=] domset l1 ∪ domset l2.
  Proof.
    intros. unfold domset. autorewrite with tea_rw_dom tea_rw_atoms.
    fsetdec.
  Qed.

  Corollary domset_app_one_l : forall (l1 : alist A) (x : atom) (a : A),
      domset (l1 ++ x ~ a) [=] domset l1 ∪ {{ x }}.
  Proof.
    intros. unfold domset. autorewrite with tea_rw_dom tea_rw_atoms.
    fsetdec.
  Qed.

  Lemma domset_fmap : forall {B} {f : A -> B} (l : alist A),
      domset (envmap f l) [=] domset l.
  Proof.
    intros. unfold domset. autorewrite with tea_rw_dom.
    fsetdec.
  Qed.

End domset_lemmas.

Hint Rewrite domset_nil domset_cons
     domset_one domset_app domset_fmap : tea_rw_dom.

(** Elements of domset *)
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
    intros. autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma in_domset_cons : forall (x y : atom) (a : A) (E : alist A),
      y ∈@ domset ((x, a) :: E) <-> y = x \/ y ∈@ domset E.
  Proof.
    intros. autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma in_domset_app : forall x (E F : alist A),
    x ∈@ domset (E ++ F) <-> x ∈@ domset E \/ x ∈@ domset F.
  Proof.
    intros. autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma in_domset_fmap : forall {B} {f : A -> B} (l : alist A) x,
      x ∈@ domset (envmap f l) <-> x ∈@ domset l.
  Proof.
    intros. autorewrite with tea_rw_dom. fsetdec.
  Qed.

End in_domset_lemmas.

Hint Rewrite in_domset_nil in_domset_one
     in_domset_cons in_domset_app in_domset_fmap : tea_rw_dom.

(** ** Rewriting lemmas for [range] *)
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

  Lemma range_cons : forall (x : atom) (a : A) (E : alist A),
      range ((x, a) :: E) = [ a ] ++ range E.
  Proof.
    reflexivity.
  Qed.

  Lemma range_app : forall (l1 l2 : alist A),
      range (l1 ++ l2) = range l1 ++ range l2.
  Proof.
    intros. unfold range.
    now autorewrite with tea_list.
  Qed.

  Lemma range_fmap : forall {B} {f : A -> B} (l : alist A),
      range (envmap f l) = fmap list f (range l).
  Proof.
    intros. unfold range, envmap. compose near l.
    unfold_ops @Fmap_alist @Fmap_compose.
    rewrite 2(fun_fmap_fmap list).
    fequal. now ext [? ?].
  Qed.

End range_lemmas.

Create HintDb tea_rw_range.
Hint Rewrite range_nil range_cons
     range_one range_app range_fmap : tea_rw_range.

(** *** Elements of [range] *)
Section in_range_lemmas.

  Context
    (A : Type).

  Lemma in_range_nil : forall x,
    x ∈ range (@nil (atom * A)) <-> False.
  Proof.
    intros; now autorewrite with tea_rw_range.
  Qed.

  Lemma in_range_cons : forall (x : atom) (a1 a2 : A) (E : alist A),
      a2 ∈ range ((x, a1) :: E) <-> a2 = a1 \/ a2 ∈ range E.
  Proof.
    intros; now autorewrite with tea_rw_range tea_list.
  Qed.

  Lemma in_range_one : forall (x : atom) (a1 a2 : A),
      a2 ∈ range (x ~ a1) <-> a1 = a2.
  Proof.
    intros; now autorewrite with tea_rw_range tea_list.
  Qed.

  Lemma in_range_app : forall x (E F : alist A),
    x ∈ range (E ++ F) <-> x ∈ range E \/ x ∈ range F.
  Proof.
    intros; now autorewrite with tea_rw_range tea_list.
  Qed.

  Lemma in_range_fmap : forall {B} {f : A -> B} (l : alist A) (b : B),
      b ∈ range (envmap f l) <-> exists a, a ∈ range l /\ f a = b.
  Proof.
    intros. autorewrite with tea_rw_range. now rewrite (in_fmap_iff list).
  Qed.

End in_range_lemmas.

Hint Rewrite in_range_nil in_range_one
     in_range_cons in_range_app in_range_fmap : tea_rw_range.

(** ** Rewriting principles for [∈] *)
Section binds_rewriting_lemmas.

  Context
    {A B : Type}.

  Implicit Types (x : atom) (a : A) (b : B).

  Lemma binds_nil_iff : forall x a,
      (x, a) ∈ nil <-> False.
  Proof.
    now autorewrite with tea_list.
  Qed.

  Lemma binds_cons_iff : forall x y a1 a2 E,
      (x, a1) ∈ ((y, a2) :: E) <-> (x = y /\ a1 = a2) \/ (x, a1) ∈ E.
  Proof.
    introv. autorewrite with tea_list.
    now rewrite pair_equal_spec.
  Qed.

  Lemma binds_one_iff : forall x y a1 a2,
      (x, a1) ∈ (y ~ a2) <-> x = y /\ a1 = a2.
  Proof.
    introv. autorewrite with tea_list.
    now rewrite pair_equal_spec.
  Qed.

  Lemma binds_app_iff : forall x a E F,
      (x, a) ∈ (E ++ F) <-> (x, a) ∈ E \/ (x, a) ∈ F.
  Proof.
    introv. now autorewrite with tea_list.
  Qed.

  Lemma binds_envmap_iff : forall x b f E,
      (x, b) ∈ envmap f E <->
      exists a, (x, a) ∈ E /\ f a = b.
  Proof.
    introv. unfold envmap. now rewrite in_envmap_iff.
  Qed.

End binds_rewriting_lemmas.

Create HintDb tea_rw_binds.
Hint Rewrite @binds_nil_iff @binds_cons_iff
     @binds_one_iff @binds_app_iff @binds_envmap_iff : tea_rw_binds.

(* *********************************************************************** *)
(** ** Tactical lemmas for [binds] *)

Section binds_theorems.

  Context
    (A B : Type).

  Implicit Types
           (x y : atom) (a b : A) (E F : alist A).

  Lemma binds_one_1 : forall x a y b,
    (x, a) ∈ (y ~ b) ->
    x = y.
  Proof.
    introv. now autorewrite with tea_rw_binds.
  Qed.

  Lemma binds_one_2 : forall x a y b,
      (x, a) ∈ (y ~ b) ->
      a = b.
  Proof.
    introv. now autorewrite with tea_rw_binds.
  Qed.

  Lemma binds_one_3 : forall x a,
    (x, a) ∈ (x ~ a).
  Proof.
    introv. now autorewrite with tea_rw_binds.
  Qed.

  Lemma binds_cons_1 : forall x y a b E,
    (x, a) ∈ ((y, b) :: E) ->
    (x = y /\ a = b) \/ (x, a) ∈ E.
  Proof.
    introv. now autorewrite with tea_rw_binds.
  Qed.

  Lemma binds_cons_2 : forall x a E,
      (x, a) ∈ ((x, a) :: E).
  Proof.
    intros. autorewrite with tea_rw_binds.
    now left.
  Qed.

  Lemma binds_cons_3 : forall x a y b E,
    (x, a) ∈ E ->
    (x, a) ∈ ((y, b) :: E).
  Proof.
    intros. autorewrite with tea_rw_binds.
    auto.
  Qed.

  Lemma binds_app_2 : forall x a E F,
      (x, a) ∈ E ->
      (x, a) ∈ (E ++ F).
  Proof.
    intros. autorewrite with tea_rw_binds.
    auto.
  Qed.

  Lemma binds_app_3 :forall x a E F,
      (x, a) ∈ F ->
      (x, a) ∈ (E ++ F).
  Proof.
    intros. autorewrite with tea_rw_binds.
    auto.
  Qed.

  Lemma binds_fmap_mono : forall x a E (f : A -> B),
    (x, a) ∈ E ->
    (x, f a) ∈ (envmap f E).
  Proof.
    introv hyp. autorewrite with tea_rw_binds.
    eauto.
  Qed.

  Lemma binds_in_dom : forall x a E,
      (x, a) ∈ E ->
      x ∈ dom E.
  Proof.
    setoid_rewrite in_dom_iff. eauto.
  Qed.

  Lemma binds_in_domset : forall x a E,
      (x, a) ∈ E ->
      x ∈@ domset E.
  Proof.
    setoid_rewrite in_domset_iff. eauto.
  Qed.

  Lemma binds_in_range : forall x a E,
      (x, a) ∈ E ->
      a ∈ range E.
  Proof.
    setoid_rewrite in_range_iff. eauto.
  Qed.

End binds_theorems.

#[export] Hint Resolve binds_one_3 binds_cons_2 binds_cons_3 binds_app_2
 binds_app_3 binds_fmap_mono : tea_alist.
#[export] Hint Immediate binds_one_1 binds_one_2 binds_in_dom
 binds_in_domset binds_in_range : tea_alist.

(** ** Rewriting principles for [disjoint] *)
Section disjoint_rewriting_lemmas.

  Lemma disjoint_sym {A B} : forall (E : alist A) (F : alist B),
    disjoint E F <-> disjoint F E.
  Proof.
    intros. unfold disjoint. split; fsetdec.
  Qed.

  Lemma disjoint_nil_l {A B} : forall (F : alist B),
      disjoint (nil : alist A) F <-> True.
  Proof.
    unfold disjoint. fsetdec.
  Qed.

  Lemma disjoint_nil_r {A B} : forall (E : alist A),
      disjoint E (nil : alist B) <-> True.
  Proof.
    intros. now rewrite disjoint_sym, disjoint_nil_l.
  Qed.

  Context
    {A B : Type}.

  Lemma disjoint_cons_l : forall (x : atom) (a : A) (E : alist A) (F : alist B),
      disjoint ((x, a) :: E) F <-> ~ x ∈@ domset F /\ disjoint E F.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_cons_r : forall (x : atom) (b : B) (E : alist A) (F : alist B),
      disjoint E ((x, b) :: F) <-> ~ x ∈@ domset E /\ disjoint E F.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_one_l : forall (x : atom) (a : A) (F : alist B),
      disjoint (x ~ a) F <-> ~ x ∈@ domset F.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_one_r : forall (x : atom) (b : B) (E : alist A),
      disjoint E (x ~ b) <-> ~ x ∈@ domset E.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_app_l : forall (E F : alist A) (G : alist B),
      disjoint (E ++ F) G <-> disjoint E G /\ disjoint F G.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_app_r : forall (E F : alist A) (G : alist B),
      disjoint G (E ++ F) <-> disjoint E G /\ disjoint F G.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

  Lemma disjoint_fmap_l :
    forall A B C (E : alist A) (F : alist B) (f : A -> C),
      disjoint (envmap f E) F <-> disjoint E F.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    reflexivity.
  Qed.

  Lemma disjoint_fmap_r :
    forall A B C (E : alist A) (F : alist B) (f : A -> C),
    disjoint F (envmap f E) <-> disjoint E F.
  Proof.
    intros. unfold disjoint. autorewrite with tea_rw_dom.
    intuition fsetdec.
  Qed.

End disjoint_rewriting_lemmas.

Create HintDb tea_rw_disj.
Hint Rewrite @disjoint_nil_l @disjoint_nil_r @disjoint_cons_l @disjoint_cons_r
     @disjoint_one_l @disjoint_one_r @disjoint_app_l @disjoint_app_r
  @disjoint_fmap_l @disjoint_fmap_r : tea_rw_disj.

(** ** Tactical lemmas for [disjoint] *)
Section disjoint_auto_lemmas.

  Context
    {A B : Type}.

  Implicit Types (a : A) (b : B) (E : alist A) (F : alist B).

  Lemma disjoint_sym_1 : forall E F,
      disjoint E F ->
      disjoint F E.
  Proof.
    intros. now rewrite disjoint_sym.
  Qed.

  Lemma disjoint_app_1 : forall E1 E2 F,
      disjoint (E1 ++ E2) F ->
      disjoint E1 F.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_app_2 : forall E1 E2 F,
      disjoint (E1 ++ E2) F ->
      disjoint E2 F.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_app_3 : forall E1 E2 F,
      disjoint E1 F ->
      disjoint E2 F ->
      disjoint (E1 ++ E2) F.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_envmap_1 : forall E F C (f : A -> C),
      disjoint (envmap f E) F ->
      disjoint E F.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_envmap_2 : forall E F C (f : A -> C),
      disjoint E F ->
      disjoint (envmap f E) F.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_one_l_1 : forall x a E,
      disjoint (x ~ a) E -> ~ x ∈@ domset E.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_one_l_2 : forall x a E,
      ~ x ∈@ domset E -> disjoint (x ~ a) E.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_cons_hd : forall x a E F,
      disjoint ((x, a) :: E) F -> ~ x ∈@ domset F.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_cons_hd_one : forall x a E F,
      disjoint (x ~ a ++ E) F -> ~ x ∈@ domset F.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_cons_tl : forall x a E F,
      disjoint ((x, a) :: E) F -> disjoint E F.
  Proof.
    introv. now autorewrite with tea_rw_disj.
  Qed.

  Lemma disjoint_dom_1 : forall x E (F : alist A),
      disjoint E F ->
      x ∈@ domset E ->
      ~ x ∈@ domset F.
  Proof.
    unfold disjoint in *. fsetdec.
  Qed.

  Lemma disjoint_dom_2 : forall x E (F : alist A),
      disjoint E F ->
      x ∈@ domset F ->
      ~ x ∈@ domset E.
  Proof.
    unfold disjoint in *. fsetdec.
  Qed.

  Lemma disjoint_binds_1 : forall x a E (F : alist A),
      disjoint E F ->
      (x, a) ∈ E ->
      ~ (x, a) ∈ F.
  Proof.
    introv Hdisj He Hf.
    apply binds_in_domset in He.
    apply binds_in_domset in Hf.
    unfold disjoint in *.
    false. fsetdec.
  Qed.

  Lemma disjoint_binds_2 : forall x a E (F : alist A),
      disjoint E F ->
      (x, a) ∈ F ->
      ~ (x, a) ∈ E.
  Proof.
    introv Hd Hf.
    rewrite disjoint_sym in Hd.
    eauto using disjoint_binds_1.
  Qed.

End disjoint_auto_lemmas.

#[export] Hint Resolve disjoint_sym_1 disjoint_app_3
 disjoint_envmap_2 : tea_alist.

(** These introduce existential variables, so only
apply them if they immediately solve the goal. *)
#[export] Hint Immediate disjoint_app_1 disjoint_app_2
 disjoint_one_l_1 disjoint_envmap_1
 disjoint_dom_1 disjoint_dom_2
 disjoint_binds_1 disjoint_binds_2 : tea_alist.

(** ** Tactical lemmas for [uniq] *)
(** For automating proofs about uniqueness, it is typically easier to
work with (one-way) lemmas rather than rewriting principles, in
contrast to most of the other parts of Tealeaves internals. *)
Section uniq_auto_lemmas.

  Context
    (A B : Type).

  Implicit Types
           (x : atom) (a : A) (b : B) (E F : alist A).

  Lemma uniq_one : forall x a,
      uniq (x ~ a).
  Proof.
    intros. change_alist ((x ~ a) ++ nil).
    constructor; [constructor | fsetdec].
  Qed.

  Lemma uniq_cons_1 : forall x a E,
      uniq ((x, a) :: E) ->
      uniq E.
  Proof.
    now inversion 1.
  Qed.

  Lemma uniq_cons_2 : forall x a E,
      uniq ((x, a) :: E) ->
      ~ x ∈@ domset E.
  Proof.
    now inversion 1.
  Qed.

  Lemma uniq_cons_3 : forall x a E,
      ~ x ∈@ domset E ->
      uniq E ->
      uniq ((x, a) :: E).
  Proof.
    intros. constructor; auto.
  Qed.

  Lemma uniq_app_1 : forall E F,
      uniq (E ++ F) ->
      uniq E.
  Proof.
    introv Hu. alist induction E.
    - constructor.
    - simpl_alist in Hu. inverts Hu.
      autorewrite with tea_rw_dom in *.
      constructor; tauto.
  Qed.

  Lemma uniq_app_2 : forall E F,
      uniq (E ++ F) ->
      uniq F.
  Proof.
    introv Hu. alist induction E.
    - trivial.
    - inverts Hu. auto.
  Qed.

  Lemma uniq_app_3 : forall E F,
      uniq (E ++ F) ->
      disjoint E F.
  Proof.
    introv Hu. unfold disjoint. alist induction E as [| ? ? ? IH].
    - fsetdec.
    - inverts Hu. autorewrite with tea_rw_dom in *.
      lapply IH.
      + fsetdec.
      + auto.
  Qed.

  Lemma uniq_app_4 : forall E F,
      uniq E ->
      uniq F ->
      disjoint E F ->
      uniq (E ++ F).
  Proof.
    introv He ? ?. alist induction E as [| ? ? E ?].
    - assumption.
    - inverts He. change_alist (x ~ a ++ (E ++ F)).
      autorewrite with tea_rw_disj in *. constructor.
      + tauto.
      + now autorewrite with tea_rw_dom.
  Qed.

  Lemma uniq_app_5 : forall x a E,
      uniq (x ~ a ++ E) ->
      ~ x ∈@ domset E.
  Proof.
    now inversion 1.
  Qed.

  (* For some reason, [uniq_app_4] will not be applied
     by auto on this goal. *)
  Lemma uniq_comm : forall E F,
      uniq (E ++ F) ->
      uniq (F ++ E).
  Proof.
    intros. apply uniq_app_4.
    all: eauto using uniq_app_4, uniq_app_2,
         uniq_app_1, uniq_app_3, disjoint_sym_1.
  Qed.

  Lemma uniq_envmap_1 : forall E (f : A -> B),
      uniq (envmap f E) ->
      uniq E.
  Proof.
    introv Hu. alist induction E.
    - constructor.
    - autorewrite with tea_rw_envmap in *. inverts Hu.
      constructor.
      + auto.
      + now autorewrite with tea_rw_dom in *.
  Qed.

  Lemma uniq_envmap_2 : forall E (f : A -> B),
      uniq E ->
      uniq (envmap f E).
  Proof.
    introv Hu. alist induction E.
    - constructor.
    - autorewrite with tea_rw_envmap. inverts Hu.
      constructor.
      + auto.
      + now autorewrite with tea_rw_dom in *.
  Qed.

End uniq_auto_lemmas.

#[export] Hint Resolve uniq_nil uniq_push uniq_one
 uniq_cons_3 uniq_app_3 uniq_app_4 uniq_envmap_2 uniq_comm : tea_alist.

(** These introduce existential variables *)
#[export] Hint Immediate uniq_cons_1
 uniq_cons_2 uniq_app_1 uniq_app_2
 uniq_app_5 uniq_envmap_1 : tea_alist.

(** ** Rewriting principles for [uniq] *)
Section uniq_rewriting_lemmas.

  Context
    (A B : Type).

  Implicit Types
           (x : atom) (a : A) (b : B) (E F : alist A).

  Lemma uniq_nil_iff :
    uniq ([] : list (atom * A)) <-> True.
  Proof.
    split; auto with tea_alist.
  Qed.

  Lemma uniq_cons_iff : forall x a E,
      uniq ((x, a) :: E) <->  ~ x ∈@ domset E /\ uniq E.
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

  Lemma uniq_app_iff : forall E F,
      uniq (E ++ F) <-> uniq E /\ uniq F /\ disjoint E F.
  Proof.
    intuition eauto with tea_alist.
  Qed.

  Lemma uniq_fmap_iff : forall E (f : A -> B),
      uniq (envmap f E) <-> uniq E.
  Proof.
    intuition eauto with tea_alist.
  Qed.

End uniq_rewriting_lemmas.

Create HintDb tea_rw_uniq.
Hint Rewrite uniq_nil_iff uniq_cons_iff
     uniq_one_iff uniq_app_iff uniq_fmap_iff : tea_rw_uniq.

(** ** Stronger theorems about unique lists *)
Section binds_theorems_uniq.

  Context
    (A B : Type).

  Implicit Types
           (x : atom) (a : A) (b : B) (E F : alist A).

  Lemma binds_app_uniq_iff : forall x a E F,
    uniq (E ++ F) ->
    (x, a) ∈ (E ++ F) <->
    ((x, a) ∈ E /\ ~ x ∈@ domset F) \/
    ((x, a) ∈ F /\ ~ x ∈@ domset E).
  Proof.
    introv H. autorewrite with tea_rw_uniq tea_rw_binds in *.
    destructs H. split.
    - intros [inE|inF].
      + left. split.
        * auto.
        * eauto using disjoint_dom_1 with tea_alist.
      + right. split.
        * auto.
        * eauto using disjoint_dom_1 with tea_alist.
    - tauto.
  Qed.

  Lemma binds_cons_uniq_iff : forall x y (a b : A) E,
    uniq ((y, b) :: E) ->
    (x, a) ∈ ((y, b) :: E) <->
     (x = y /\ a = b /\ ~ x ∈@ domset E) \/
     ((x, a) ∈ E /\ x <> y).
  Proof.
    introv. change_alist (y ~ b ++ E).
    intro. rewrite binds_app_uniq_iff; auto.
    autorewrite with tea_rw_binds tea_rw_dom.
    tauto.
  Qed.

End binds_theorems_uniq.

(** ** Permutation lemmas for [dom], [range], [domset], [disjoint], [uniq], [binds]. *)
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
    intro a; rewrite 2(in_atoms_iff).
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

Lemma binds_perm : forall (A : Type) (l1 l2 : alist A) (x : atom) (a : A),
    Permutation l1 l2 -> (x, a) ∈ l1 <-> (x, a) ∈ l2.
Proof.
  intros. now erewrite List.perm_set_eq; eauto.
Qed.

Create HintDb tea_rw_perm.
Hint Rewrite @perm_dom @perm_range @perm_domset @perm_disjoint_l @perm_disjoint_r
     @uniq_perm using (auto; try symmetry; auto) : tea_rw_perm.


(* *********************************************************************** *)
(** * List properties *)

(** The following properties are an assortment of structural
    properties about association lists. *)

(* TODO : Investigate where these came from and what they are used for
Section AssortedListProperties.
  Variable  X : Type.
  Variables x : X.
  Variables xs ys zs : list X.

  Lemma one_eq_app :
    one x ++ xs = ys ++ zs ->
    (exists qs, ys = x :: qs /\ xs = qs ++ zs) \/
    (ys = nil /\ zs = x :: xs).
  Proof. clear. Search "cons" "eq".
         auto using CoqListFacts.cons_eq_app. Qed.

  Lemma app_eq_one :
    ys ++ zs = one x ++ xs ->
    (exists qs, ys = x :: qs /\ xs = qs ++ zs) \/
    (ys = nil /\ zs = x :: xs).
  Proof. clear. auto using CoqListFacts.app_eq_cons. Qed.

  Lemma nil_neq_one_mid :
    nil <> xs ++ one x ++ ys.
  Proof. clear. induction xs; simpl_alist; intros J; inversion J. Qed.

  Lemma one_mid_neq_nil :
    xs ++ one x ++ ys <> nil.
  Proof. clear. intros H. symmetry in H. auto using nil_neq_one_mid. Qed.

End AssortedListProperties.
 *)

(* *********************************************************************** *)
(** * Tactic support for [disjoint] and [uniq] *)

(** [destruct_uniq] decomposes all [uniq] and [disjoint] hypotheses. *)

(*
Ltac destruct_uniq :=
  match goal with
    | H : uniq nil |- _ =>
      clear H;
      destruct_uniq
    | H : uniq (?x ~ ?a) |- _ =>
      clear H;
      destruct_uniq
    | H : uniq ((?x, ?a) :: ?E) |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply uniq_cons_1 in H;
      apply uniq_cons_2 in J;
      autorewrite with tea_alist in J;
      destruct_uniq
    | H : uniq (?E ++ ?F) |- _ =>
      let J1 := fresh "UniqTac" in
      let J2 := fresh "UniqTac" in
      pose proof H as J1;
      pose proof H as J2;
      apply uniq_app_1 in H;
      apply uniq_app_2 in J1;
      apply uniq_app_3 in J2;
      destruct_uniq
    | H : uniq (envmap ?f ?E) |- _ =>
      apply uniq_fmap_1 in H;
      destruct_uniq
    | H : disjoint nil ?E |- _ =>
      clear H;
      destruct_uniq
    | H : disjoint (?x ~ ?a) ?F |- _ =>
      apply disjoint_one_1 in H;
      autorewrite with tea_alist in H;
      destruct_uniq
    | H : disjoint ((?x, ?a) :: ?E) ?F |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply disjoint_cons_1 in H;
      apply disjoint_cons_2 in J;
      autorewrite with tea_alist in H;
      destruct_uniq
    | H : disjoint (?E ++ ?F) ?G |- _ =>
      let J := fresh "UniqTac" in
      pose proof H as J;
      apply disjoint_app_1 in H;
      apply disjoint_app_2 in J;
      destruct_uniq
    | H : disjoint (envmap ?f ?E) ?F |- _ =>
      apply disjoint_fmap_1 in H;
      destruct_uniq
    | H : disjoint ?E nil |- _ =>
      clear H;
      destruct_uniq
    | H : disjoint ?F (?x ~ ?a) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?F ((?x, ?a) :: ?E) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?G (?E ++ ?F) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | H : disjoint ?F (envmap ?f ?E) |- _ =>
      apply disjoint_sym_1 in H;
      destruct_uniq
    | _ =>
      idtac
  end.
(** [solve_uniq] attempts to solve goals by first decomposing
    hypotheses about [disjoint] and [uniq] and then trying some
    simple, if perhaps slow, heuristics. *)

Ltac solve_uniq :=
  intros;
  destruct_uniq;
  repeat first [ apply uniq_push
               | apply uniq_cons_3
               | apply uniq_app_4
               | apply uniq_one_1
               | apply uniq_nil ];
  auto;
  try tauto;
  unfold disjoint in *;
  try fsetdec;
  fail "Not solvable by [solve_uniq]; try [destruct_uniq]".

*)

(* *********************************************************************** *)
(** * More facts about [uniq] *)

(*
Section uniq_theorems.

  Variable  A     : Type.
  Variables x y   : atom.
  Variables a b   : A.
  Variables E F G : alist A.

  Lemma uniq_insert_mid :
    uniq (G ++ E) ->
    ~ x ∈@ domset G ->
    ~ x ∈@ domset E ->
    uniq (G ++ x ~ a ++ E).
  Proof.
    clear. autorewrite with tea_rw_uniq tea_rw_disj.
    unfold disjoint. intuition fsetdec.
  Qed.

  Lemma uniq_remove_mid :
    uniq (E ++ F ++ G) ->
    uniq (E ++ G).
  Proof.
    clear.
    autorewrite with tea_rw_uniq tea_rw_disj.
    unfold disjoint. intuition fsetdec.
  Qed.

  Lemma uniq_reorder_1 :
    uniq (E ++ F) ->
    uniq (F ++ E).
  Proof.
    autorewrite with tea_rw_uniq tea_rw_disj.
    unfold disjoint. intuition fsetdec.
  Qed.

  Lemma uniq_reorder_2 :
    uniq (E ++ F ++ G) ->
    uniq (F ++ E ++ G).
  Proof.
    autorewrite with tea_rw_uniq tea_rw_disj.
    unfold disjoint. intuition fsetdec.
  Qed.

  Lemma uniq_fmap_app_l : forall (f : A -> A),
    uniq (F ++ E) ->
    uniq (envmap f F ++ E).
  Proof.
    intros. autorewrite with tea_rw_uniq tea_rw_disj in *.
    tauto.
  Qed.

  Lemma fresh_mid_tail :
    uniq (F ++ x ~ a ++ E) ->
    ~ x ∈@ domset E.
  Proof.
    intros. autorewrite with tea_rw_uniq tea_rw_disj in *.
    tauto.
  Qed.

  Lemma fresh_mid_head :
    uniq (F ++ x ~ a ++ E) ->
    ~ x ∈@ domset F.
  Proof.
    intros. autorewrite with tea_rw_uniq tea_rw_disj in *.
    tauto.
  Qed.

End uniq_theorems.
*)

(* *********************************************************************** *)
(*
(** * Tactic support for [binds] *)

(** [destruct_binds_hyp] and [destruct_binds_hyp_uniq] tactics
    decompose a hypotheses of the form [binds x a E], with the latter
    tactic assuming that [uniq E] holds.  The tactic [solve_uniq] is
    used for discharging any [uniq] obligations that arise.
    Implementation note (BEA, XXX): No support for [fmap].  I'm not
    sure what to do about the "injectivity" side condition on
    [binds_fmap_inv].  Perhaps just generate the extra subgoal, on the
    assumption that the condition is usually provable?  It's not as
    if I want to implement even more tactics here... *)

Ltac destruct_binds_hyp H :=
  match type of H with
    | binds ?x ?a nil =>
      inversion H
    | binds ?x ?a (?y ~ ?b) =>
      let J1 := fresh "BindsTacKey" in
      let J2 := fresh "BindsTacVal" in
      rename H into J1;
      pose proof J1 as J2;
      apply binds_one_1 in J1;
      apply binds_one_2 in J2;
      try (subst x);
      try (subst a);
      try (subst y);
      try (subst b)
    | binds ?x ?a ((?y, ?b) :: ?E) =>
      change (binds x a (y ~ b ++ E)) in H;
      destruct_binds_hyp H
    | binds ?x ?a (?E ++ ?F) =>
      let J := fresh "BindsTac" in
      apply binds_app_1 in H;
      destruct H as [J | J];
      destruct_binds_hyp J
    | _ =>
      idtac
  end.

Ltac destruct_binds_hyp_uniq H :=
  match type of H with
    | binds ?x ?a nil =>
      inversion H
    | binds ?x ?a (?y ~ ?b) =>
      let J1 := fresh "BindsTacKey" in
      let J2 := fresh "BindsTacVal" in
      rename H into J1;
      pose proof J1 as J2;
      apply binds_one_1 in J1;
      apply binds_one_2 in J2;
      try (subst x);
      try (subst a);
      try (subst y);
      try (subst b)
    | binds ?x ?a ((?y, ?b) :: ?E) =>
      change (binds x a (y ~ b ++ E)) in H;
      destruct_binds_hyp_uniq H
    | binds ?x ?a (?E ++ ?F) =>
      let J1 := fresh "BindsTacSideCond" in
      assert (J1 : uniq (E ++ F));
        [ destruct_uniq; auto
        | match type of J1 with
            | @uniq ?A _ =>
              let J2 := fresh "BindsTac" in
              destruct (@binds_app_uniq_1 A x a E F J1 H)
                as [[J2 ?] | [J2 ?]];
              clear H;
              destruct_binds_hyp_uniq J2
          end
        ]
    | _ =>
      idtac
  end.

(** An auxiliary tactic.  Not intended for use on its own. *)
Ltac analyze_binds_cleanup :=
  auto;
  try tauto;
  try discriminate;
  try match goal with
        | J : ~ AtomSet.In ?x ?E |- _ =>
          match E with
            | context [x] => elim J; clear; simpl_alist; simpl_alist; auto with set
          end
      end.

(** The [analyze_binds] and [analyze_binds_uniq] tactics decompose a
    hypothesis of the form [binds x a E], with the latter assuming
    that [uniq E] holds, and then try some simple heuristics for
    solving the resulting goals. *)

Ltac analyze_binds H :=
  destruct_binds_hyp H;
  analyze_binds_cleanup.

Ltac analyze_binds_uniq H :=
  destruct_binds_hyp_uniq H;
  analyze_binds_cleanup.
*)

(* *********************************************************************** *)
(** * Facts about [binds] *)

(*
Section binds_theorems.

  Variables A B   : Type.
  Variables f     : A -> B.
  Variables x y   : atom.
  Variables a b   : A.
  Variables E F G : alist A.

  Lemma binds_dec :
    (forall a b : A, {a = b} + {a <> b}) ->
    {binds x a E} + {~ binds x a E}.
  Proof.
    clear. intros. unfold binds.
    alist induction E.
    - right. auto.
    - destruct IHl.
      + left. rewrite List.in_list_app. right; auto.
      + assert (tmp : {x = x0} + {x <> x0}).
        { apply EqDec_eq_of_EqDec. typeclasses eauto. }
        destruct tmp; destruct (X a a0).
        * left; left. subst. reflexivity.
        * right. rewrite List.in_list_app.
          intuition.  apply n0. inversion H0.
          inversion H. auto. contradiction.
        * right. rewrite List.in_list_app.
          intuition.  apply n0. inversion H0.
          inversion H. auto. contradiction.
        * right.  rewrite List.in_list_app.
          intuition.  apply n0. inversion H0.
          inversion H. auto. contradiction.
  Defined.

  Lemma binds_lookup :
    {a : A | binds x a E} + (forall a, ~ binds x a E).
  Proof with intuition eauto.
    clear. intros. alist induction E as [ | x1 a1 ? [[a' J] | J] ]...
    destruct (eq_dec x x1)...
    right. unfold binds. intros ? [K | ?]...
    injection K...
  Defined.

  Lemma binds_lookup_dec :
    decidable (exists a, binds x a E).
  Proof with intuition eauto.
    clear. intros. unfold decidable.
    destruct binds_lookup as [[? ?] | ?]...
    right. intros [? ?]...
  Defined.

  Lemma binds_weaken :
    binds x a (E ++ G) ->
    binds x a (E ++ F ++ G).
  Proof. clear. intros H. analyze_binds H. Qed.

  Lemma binds_mid_eq :
    binds x a (F ++ (x ~ b) ++ E) ->
    uniq (F ++ (x ~ b) ++ E) ->
    a = b.
  Proof.
    clear. intros J ?. analyze_binds_uniq J.
  Qed.

  Lemma binds_remove_mid :
    binds x a (F ++ (y ~ b) ++ G) ->
    x <> y ->
    binds x a (F ++ G).
  Proof. clear. intros H. analyze_binds H. Qed.

  Lemma binds_In : forall x a (E : alist A),
    binds x a E -> AtomSet.In x (domset E).
  Proof.
    clear. alist induction E as [ | y ? F ]; intros J; simpl_alist.
      analyze_binds J.
      analyze_binds J. simpl_alist. auto. simpl_alist. auto.
  Qed.

  Lemma binds_In_inv : forall x (E : alist A),
     x ∈@ domset E -> exists a, binds x a E.
  Proof.
    clear. introv H. now rewrite in_domset_iff_ in H.
  Qed.

  Lemma binds_unique :
    binds x a E ->
    binds x b E ->
    uniq E ->
    a = b.
  Proof.
    clear. alist induction E as [ | ? ? F IH ].
    inversion 1.
    unfold binds. simpl. intros [J1 | J1] [J2 | J2] J3.
  Admitted.

  Lemma fresh_app_l :
    uniq (F ++ E) ->
    binds x a E ->
    ~ AtomSet.In x (domset F).
  Proof.
    clear. intros.
    assert (AtomSet.In x (domset E)) by eauto using binds_In.
    solve_uniq.
  Qed.

  Lemma fresh_app_r :
    uniq (F ++ E) ->
    binds x a F ->
    ~ AtomSet.In x (domset E).
  Proof.
    clear. intros.
    assert (AtomSet.In x (domset F)) by eauto using binds_In.
    solve_uniq.
  Qed.

  (* If x is in an alist, it is either in the front half or
   the back half. *)
  Lemma binds_split : binds x a G -> exists G1 G2, G = G2 ++ one (x, a) ++ G1.
  Proof.
    clear. intro HB. induction G.
    + inversion HB.
    + destruct a0 as [y b].
      apply binds_cons_1 in HB.
      destruct HB as [[E1 E2]|E]. subst.
      ++ exists l. exists (@nil (atom * A)). simpl_alist. auto.
      ++ destruct (IHl E) as [G1 [G2 E2]].
         subst.
         eexists. exists ((y ~ b) ++ G2). simpl_alist.
         eauto.
  Qed.
End BindsDerived.
*)


(*
Hint Resolve @nil_neq_one_mid @one_mid_neq_nil : core.

#[export] Hint Resolve uniq_insert_mid uniq_fmap_app_l : core.

#[export] Hint Immediate uniq_remove_mid : core.

#[export] Hint Resolve binds_weaken : core.

#[export] Hint Immediate binds_remove_mid binds_In : core.
*)


(** * Facts about <<uniq>> lists of a particular form *)
(*
(* Facts about uniq alists of the form <<E ++ (x ~ a) ++ F.>> *)
Section UniqMid.

  Variables A B   : Type.
  Variables f     : A -> B.
  Variables x y   : atom.
  Variables a     : A.
  Variables E F   : alist A.

  (* If we have identified a variable in the middle of a uniq alistironment,
   it fixes the front and back. *)
  Lemma uniq_mid : forall b E' F',
      uniq (E ++ (x ~ a) ++ F) ->
      (E ++ x ~ a ++ F) = (E' ++ x ~ b ++ F') ->
      E = E' /\ a = b /\ F = F'.
  Proof.
    generalize F a. clear.
    induction E.
    + intros; destruct E'; inversion H0; simpl_alist in *. auto.
      subst. destruct_uniq. fsetdec.
    + intros.
      destruct a as [y b0].
      simpl_alist in *.
      destruct_uniq.
      assert (NE: not (y = x)). fsetdec.
      destruct E' as [|[z c]]. simpl_alist in H0. inversion H0. subst. contradiction.
      inversion H0. subst.
      simpl_alist in *.
      specialize (IHl F a0 b E' F').
      destruct IHl as [E1 [E2 E3]]; auto.
      subst. auto.
  Qed.

  (* If we divide up an alist containing a variable, it either appears in the
     front half or the back half *)
  Lemma uniq_align_eq : forall E' F',
    uniq (E ++ x ~ a ++ F) ->
    E ++ x ~ a ++ F = E' ++ F' ->
    (exists E1 E2, E' = E1 ++ x ~ a ++ E2 /\ E = E1 /\ F = E2 ++ F') \/
    (exists F1 F2, F' = F1 ++ x ~ a ++ F2 /\ E = E' ++ F1 /\ F = F2).
   Proof.
     clear.
     intros E' F' U Eq.
     assert (HB: binds x a (E' ++ F')). { rewrite <- Eq. auto. }
     rewrite -> binds_app_iff in HB.
     destruct HB as [h1|h1].
     + left.
       destruct (binds_split _ _ _ _ h1) as [G0'' [E1 E2]].
       eexists. eexists. split. eauto.
       subst.
       simpl_alist in Eq.
       edestruct (uniq_mid _ _ _ U Eq); eauto. tauto.
     + right.
       destruct (binds_split _ _ _ _ h1) as [G0'' [G0' E2]].
       eexists. eexists. split. eauto.
       subst.
       rewrite <- (app_assoc _ E') in Eq.
       edestruct (uniq_mid _ _ _ U Eq); eauto.
       tauto.
   Qed.

End UniqMid.
*)

(** For any given finite set of atoms, we can generate an atom fresh
    for it. *)
Lemma atom_fresh : forall L : AtomSet.t, { x : atom | ~ x ∈@ L }.
Proof.
  intros L. destruct (atom_fresh_for_list (AtomSet.elements L)) as [a H].
  rewrite <- in_elements_iff in H.
  now exists a.
Qed.

(* ********************************************************************** *)
(** * Tactic support for picking fresh atoms *)

(* begin hide *)

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

(* end hide *)

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
  let Fr := fresh "Fr" in
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
(* end show *)


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
