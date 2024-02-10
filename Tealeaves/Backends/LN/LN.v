(** This files contains metatheorems for the locally nameless variables
 that closely parallel those of LNgen. *)
From Tealeaves.Backends.LN Require Import
  Atom AtomSet.
From Tealeaves.Misc Require Import
  NaturalNumbers.
From Tealeaves.Theory Require Import
  TraversableFunctor
  DecoratedTraversableMonad.

Import
  Product.Notations
  Monoid.Notations
  Batch.Notations
  List.ListNotations
  Subset.Notations
  Kleisli.Monad.Notations
  Kleisli.Comonad.Notations
  ContainerFunctor.Notations
  DecoratedMonad.Notations
  DecoratedContainerFunctor.Notations
  DecoratedTraversableMonad.Notations
  LN.AtomSet.Notations.

#[local] Generalizable Variable T.

(** * Locally nameless variables *)
(******************************************************************************)
Inductive LN :=
| Fr : atom -> LN
| Bd : nat -> LN.

Theorem eq_dec_LN : forall l1 l2 : LN, {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
  - compare values a and a0; auto.
  - compare values n and n0; auto.
Qed.

#[export] Instance EqDec_LN : EquivDec.EqDec LN eq := eq_dec_LN.

(** [compare_to_atom] is an induction principle for leaves that splits
      the <<Fr x>> case into subcases <<x = y>> and <<x <> y>> for
      some user-specified atom <<y>>. *)
Lemma compare_to_atom : forall x l (P : LN -> Prop),
    P (Fr x) ->
    (forall a : atom, a <> x -> P (Fr a)) ->
    (forall n : nat, P (Bd n)) ->
    P l.
Proof.
  introv case1 case2 case3. destruct l.
  - destruct_eq_args x a. auto.
  - auto.
Qed.

Tactic Notation "compare" constr(l) "to" "atom" constr(x) :=
  (induction l using (compare_to_atom x)).

(** * Locally nameless operations *)
(******************************************************************************)

(** ** Localized operations *)
(******************************************************************************)
Section locally_nameless_local_operations.

  Context
    `{Return T}.

  #[local] Arguments ret (T)%function_scope {Return} {A}%type_scope _.

  Definition free_loc : LN -> list atom :=
    fun l => match l with
          | Fr x => cons x List.nil
          | _ => List.nil
          end.

  Definition subst_loc (x : atom) (u : T LN) : LN -> T LN :=
    fun l => match l with
          | Fr y => if x == y then u else ret T (Fr y)
          | Bd n => ret T (Bd n)
          end.

  Definition open_loc (u : T LN) : nat * LN -> T LN :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => ret T (Fr x)
            | Bd n =>
              match Nat.compare n w with
              | Gt => ret T (Bd (n - 1))
              | Eq => u
              | Lt => ret T (Bd n)
              end
            end
          end.

  Definition is_opened : nat * LN -> Prop :=
    fun p =>
      match p with
      | (ctx, l) =>
        match l with
        | Fr y => False
        | Bd n => n = ctx
        end
      end.

  Definition close_loc (x : atom ) : nat * LN -> LN :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr y => if x == y then Bd w else Fr y
            | Bd n =>
              match Nat.compare n w with
              | Gt => Bd (S n)
              | Eq => Bd (S n)
              | Lt => Bd n
              end
            end
          end.

  (** The argument <<n>> is appended the context---to define local
      closure we will take <<n = 0>>, but we can also consider more
      notions like ``local closure within a gap of 1 binder,'' which
      is useful for backend reasoning. **)
  Definition is_bound_or_free (gap : nat) : nat * LN -> Prop :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => True
            | Bd n => n < w ● gap
            end
          end.

End locally_nameless_local_operations.

(** ** Extended operations *)
(******************************************************************************)
Section locally_nameless_operations.

  Context
    `{DecoratedTraversableMonadFull nat T}.

  Definition open (u : T LN) : T LN -> T LN  :=
    bindd (open_loc u).

  Definition close x : T LN -> T LN :=
    mapd (close_loc x).

  Definition subst x (u : T LN) : T LN -> T LN :=
    bind (subst_loc x u).

  Definition free : T LN -> list atom :=
    fun t => foldMap free_loc t.

  Definition freeset : T LN -> AtomSet.t :=
    fun t => LN.AtomSet.atoms (free t).

  Definition locally_closed_gap (gap : nat) : T LN -> Prop :=
    fun t => forall w l, (w, l) ∈d t -> is_bound_or_free gap (w, l).

  Definition locally_closed : T LN -> Prop :=
    locally_closed_gap 0.

  Definition scoped : T LN -> AtomSet.t -> Prop :=
    fun t γ => freeset t ⊆ γ.

End locally_nameless_operations.

(** ** Notations *)
(******************************************************************************)
Module Notations.
  Notation "t '{ x ~> u }" := (subst x u t) (at level 35).
  Notation "t '( u )" := (open u t) (at level 35).
  Notation "'[ x ] t" := (close x t) (at level 35).
End Notations.

Import Notations.

Section test_notations.

  Context
    `{DecoratedTraversableMonadFull nat T}.

  Context
    (t : T LN)
    (u : T LN)
    (x : atom)
    (n : nat).

  Check u '{x ~> t}.
  Check u '(t).
  Check '[ x ] u.

End test_notations.

(** * Lemmas for local reasoning *)
(******************************************************************************)
Create HintDb tea_local.

Tactic Notation "unfold_monoid" :=
  repeat unfold monoid_op, Monoid_op_plus,
  monoid_unit, Monoid_unit_zero in *.

Tactic Notation "unfold_lia" :=
  unfold_monoid; lia.

(** * Basic principles and lemmas *)
(******************************************************************************)
Section locally_nameless_basic_principles.

  Import Notations.

  Context
    `{DecoratedTraversableMonadFull nat T
     (unit := Monoid_unit_zero)
     (op := Monoid_op_plus)}.

  Implicit Types (l : LN) (n : nat) (t : T LN) (x : atom).

  (** ** Reasoning principles for proving equalities *)
  (******************************************************************************)

  (** *** <<open>> *)
  (******************************************************************************)
  Lemma open_eq : forall t u1 u2,
      (forall w l, (w, l) ∈d t -> open_loc u1 (w, l) = open_loc u2 (w, l)) ->
      t '(u1) = t '(u2).
  Proof.
    intros. unfold open.
    now apply bindd_respectful.
  Qed.

  Lemma open_id : forall t u,
      (forall w l, (w, l) ∈d t -> open_loc u (w, l) = ret l) ->
      t '(u) = t.
  Proof.
    intros. unfold open.
    now apply bindd_respectful_id.
  Qed.

  (** *** <<close>> *)
  (******************************************************************************)
  Lemma close_eq : forall t x y,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = close_loc y (w, l)) ->
      '[x] t = '[y] t.
  Proof.
    intros. unfold close.
    now apply mapd_respectful.
  Qed.

  Lemma close_id : forall t x,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = l) ->
      '[x] t = t.
  Proof.
    intros. unfold close.
    now apply mapd_respectful_id.
  Qed.

  (** *** <<subst>> *)
  (******************************************************************************)
  Lemma subst_eq : forall t x y u1 u2,
      (forall l, l ∈ t -> subst_loc x u1 l = subst_loc y u2 l) ->
      t '{x ~> u1} = t '{y ~> u2}.
  Proof.
    intros. unfold subst.
    now apply bind_respectful.
  Qed.

  Lemma subst_id : forall t x u,
      (forall l, l ∈ t -> subst_loc x u l = ret l) ->
      t '{x ~> u} = t.
  Proof.
    intros. unfold subst.
    now apply bind_respectful_id.
  Qed.

  (** ** Occurrence analysis lemmas *)
  (******************************************************************************)

  (** *** <<open>> *)
  (******************************************************************************)
  Lemma ind_open_iff : forall l n u t,
      (n, l) ∈d t '(u) <-> exists n1 n2 l1,
        (n1, l1) ∈d t /\ (n2, l) ∈d open_loc u (n1, l1) /\ n = n1 ● n2.
  Proof.
    intros. unfold open.
    now rewrite ind_bindd_iff.
  Qed.

  Lemma in_open_iff : forall l u t,
      l ∈ t '(u) <-> exists n1 l1,
        (n1, l1) ∈d t /\ l ∈ open_loc u (n1, l1).
  Proof.
    intros. unfold open.
    now rewrite in_bindd_iff.
  Qed.

  (** *** <<close>> *)
  (******************************************************************************)
  Lemma ind_close_iff : forall l n x t,
      (n, l) ∈d '[x] t <-> exists l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite ind_mapd_iff.
  Qed.

  Lemma in_close_iff : forall l x t,
      l ∈ '[x] t <-> exists n l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite in_mapd_iff.
  Qed.

  (** *** <<subst>> *)
  (******************************************************************************)
  Lemma ind_subst_iff : forall n l u t x,
      (n, l) ∈d t '{x ~> u} <-> exists n1 n2 l1,
        (n1, l1) ∈d t /\ (n2, l) ∈d subst_loc x u l1 /\ n = n1 ● n2.
  Proof.
    intros. unfold subst.
    now rewrite ind_bind_iff.
  Qed.

  Lemma in_subst_iff : forall l u t x,
      l ∈ t '{x ~> u} <-> exists l1,
       l1 ∈ t /\ l ∈ subst_loc x u l1.
  Proof.
    intros. unfold subst.
    now rewrite in_bind_iff.
  Qed.

  (** ** Free variables *)
  (******************************************************************************)

  (** *** Specifications for [free] and [freeset] *)
  (******************************************************************************)
  Lemma in_free_iff_local : forall (x : atom) (y : LN),
      x ∈ free_loc y = (Fr x = y).
  Proof.
    intros.
    destruct y.
    - cbv. propext.
      + intros [hyp|hyp].
        * now subst.
        * contradiction.
      + inversion 1. now left.
    - cbv. propext.
      + inversion 1.
      + inversion 1.
  Qed.

  Theorem in_free_iff : forall (t : T LN) (x : atom),
      x ∈ free t = Fr x ∈ t.
  Proof.
    intros. unfold free.
    change_left ((evalAt x ∘ element_of ∘ foldMap free_loc) t).
    reassociate -> on left.
    rewrite (foldMap_morphism (list atom) (subset atom)).
    rewrite (foldMap_morphism (subset atom) Prop).
    rewrite element_to_foldMap2.
    fequal.
    ext y.
    apply in_free_iff_local.
  Qed.

  Theorem free_iff_freeset : forall (t : T LN) (x : atom),
      x ∈ free t <-> x ∈@ freeset t.
  Proof.
    intros.
    unfold freeset.
    rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  (** *** Opening *)
  (******************************************************************************)
  Lemma free_open_iff : forall u t x,
      x ∈ free (t '(u)) <-> exists w l1,
        (w, l1) ∈d t /\ x ∈ free (open_loc u (w, l1)).
  Proof.
    intros.
    rewrite in_free_iff.
    setoid_rewrite in_free_iff.
    now rewrite in_open_iff.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma free_close_iff : forall t x y,
      y ∈ free ('[x] t) <-> exists w l1,
        (w, l1) ∈d t /\ close_loc x (w, l1) = Fr y.
  Proof.
    intros.
    rewrite in_free_iff.
    now rewrite in_close_iff.
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma free_subst_iff : forall u t x y,
      y ∈ free (t '{x ~> u}) <-> exists l1,
        l1 ∈ t /\ y ∈ free (subst_loc x u l1).
  Proof.
    intros.
    rewrite in_free_iff.
    setoid_rewrite in_free_iff.
    now rewrite in_subst_iff.
  Qed.

End locally_nameless_basic_principles.

(** * Utilities for reasoning at the leaves *)
(******************************************************************************)
Section locally_nameless_utilities.

  Context
    `{DecoratedTraversableMonadFull nat T
     (unit := Monoid_unit_zero)
     (op := Monoid_op_plus)}.

  Import Notations.

  (** ** (In)equalities between leaves *)
  (******************************************************************************)
  Lemma Fr_injective : forall (x y : atom),
      (Fr x = Fr y) <-> (x = y).
  Proof.
    intros. split; intro hyp.
    now injection hyp. now subst.
  Qed.

  Lemma Fr_injective_not_iff : forall (x y : atom),
      (Fr x <> Fr y) <-> (x <> y).
  Proof.
    intros. split; intro hyp; contradict hyp.
    now subst. now injection hyp.
  Qed.

  Lemma Fr_injective_not : forall (x y : atom),
      x <> y -> ~ (Fr x = Fr y).
  Proof.
    intros. now rewrite Fr_injective.
  Qed.

  Lemma Bd_neq_Fr : forall n x,
      (Bd n = Fr x) = False.
  Proof.
    introv. propext. discriminate. contradiction.
  Qed.

  (** ** [subst_loc] *)
  (******************************************************************************)
  Lemma subst_loc_eq : forall (u : T LN) x,
      subst_loc x u (Fr x) = u.
  Proof. intros. cbn. now compare values x and x. Qed.

  Lemma subst_loc_neq : forall (u : T LN) x y,
      y <> x -> subst_loc x u (Fr y) = ret (Fr y).
  Proof. intros. cbn. now compare values x and y. Qed.

  Lemma subst_loc_b : forall u x n,
      subst_loc x u (Bd n) = ret (Bd n).
  Proof. reflexivity. Qed.

  Lemma subst_loc_fr_neq : forall (u : T LN) l x,
      Fr x <> l -> subst_loc x u l = ret l.
  Proof.
    introv neq. unfold subst_loc.
    destruct l as [a|?]; [compare values x and a | reflexivity ].
  Qed.

  (** ** [open_loc] *)
  (******************************************************************************)
  Lemma open_loc_lt : forall (u : T LN) w n,
      n < w -> open_loc u (w, Bd n) = ret (Bd n).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and w.
  Qed.

  Lemma open_loc_gt : forall (u : T LN) n w,
      n > w -> open_loc u (w, Bd n) = ret (Bd (n - 1)).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and w.
  Qed.

  Lemma open_loc_eq : forall w (u : T LN),
      open_loc u (w, Bd w) = u.
  Proof.
    introv. unfold open_loc. compare naturals w and w.
  Qed.

  Lemma open_loc_atom : forall (u : T LN) w x,
      open_loc u (w, Fr x) = ret (Fr x).
  Proof.
    reflexivity.
  Qed.

  (** ** [Miscellaneous utilities] *)
  (******************************************************************************)
  Lemma ninf_in_neq : forall x l (t : T LN),
      ~ x ∈ free t ->
      l ∈ t ->
      Fr x <> l.
  Proof.
    introv hyp1 hyp2.
    rewrite in_free_iff in hyp1. destruct l.
    - injection. intros; subst.
      contradiction.
    - discriminate.
  Qed.

  Lemma neq_symmetry : forall X (x y : X),
      (x <> y) = (y <> x).
  Proof.
    intros. propext; intro hyp; contradict hyp; congruence.
  Qed.

End locally_nameless_utilities.

#[export] Hint Rewrite @in_ret_iff @ind_ret_iff
     using typeclasses eauto : tea_local.

#[export] Hint Rewrite Fr_injective Fr_injective_not_iff Bd_neq_Fr : tea_local.
#[export] Hint Resolve Fr_injective_not : tea_local.

#[export] Hint Rewrite
     @subst_loc_eq (*@subst_in_ret*)
     using typeclasses eauto : tea_local.
#[export] Hint Rewrite
     @subst_loc_neq @subst_loc_b @subst_loc_fr_neq (*@subst_in_ret_neq*)
     using first [ typeclasses eauto | auto ] : tea_local.
#[export] Hint Rewrite
     @open_loc_lt @open_loc_gt
     using first [ typeclasses eauto | auto ] : tea_local.
#[export] Hint Rewrite
     @open_loc_eq @open_loc_atom
     using typeclasses eauto : tea_local.

Tactic Notation "simpl_local" := (autorewrite* with tea_local).

(** * Locally nameless metatheory *)
(******************************************************************************)
Section locally_nameless_metatheory.

  Context
    `{DecoratedTraversableMonadFull nat T
     (unit := Monoid_unit_zero)
     (op := Monoid_op_plus)}.

  Open Scope set_scope.

  Lemma subst_in_ret : forall x l (u : T LN),
      (ret l) '{x ~> u} = subst_loc x u l.
  Proof.
    intros. unfold subst. compose near l on left.
    change_left ((bind (subst_loc x u) ∘ ret) l).
    now rewrite kmon_bind0.
  Qed.

  Implicit Types
           (l : LN) (p : LN)
           (x : atom) (t : T LN)
           (w : nat) (n : nat).

  (** ** LN analysis: substitution with contexts *)
  (******************************************************************************)
  Lemma ind_subst_loc_iff : forall l w p (u : T LN) x,
      (w, p) ∈d subst_loc x u l <->
      l <> Fr x /\ w = Ƶ /\ l = p \/ (* l is not replaced *)
      l = Fr x /\ (w, p) ∈d u. (* l is replaced *)
  Proof.
    introv. compare l to atom x; simpl_local; intuition.
  Qed.

  Theorem ind_subst_iff' : forall w t u l x,
      (w, l) ∈d t '{x ~> u} <->
      (w, l) ∈d t /\ l <> Fr x \/
      exists w1 w2 : nat, (w1, Fr x) ∈d t /\ (w2, l) ∈d u /\ w = w1 ● w2.
  Proof.
    intros. rewrite ind_subst_iff.
    setoid_rewrite ind_subst_loc_iff. split.
    - intros [l' [n1 [n2 conditions]]].
      destruct conditions as [c1 [[c2|c2] c3]]; subst.
      + left. destructs c2; subst. now rewrite monoid_id_l.
      + right. destructs c2; subst. eauto.
    - intros [[? ?] | [n1 [n2 [? [? ?]]]]].
      + exists w (Ƶ : nat) l. rewrite monoid_id_l. splits; auto.
      + exists n1 n2 (Fr x). splits; auto.
  Qed.

  (** ** LN analysis: substitution without contexts *)
  (******************************************************************************)
  Lemma in_subst_loc_iff : forall l p (u : T LN) x,
      p ∈ subst_loc x u l <->
      l <> Fr x /\ l = p \/
      l = Fr x /\ p ∈ u.
  Proof.
    introv. compare l to atom x; autorewrite* with tea_local; intuition.
  Qed.

  Theorem in_subst_iff' : forall t u l x,
      l ∈ t '{x ~> u} <->
      l ∈ t /\ l <> Fr x \/
      Fr x ∈ t /\ l ∈ u.
  Proof with auto.
    intros. rewrite in_subst_iff.
    setoid_rewrite in_subst_loc_iff. split.
    - intros [? [? in_sub]].
      destruct in_sub as [[? heq] | [heq ?]]; subst...
    - intros [[? ?]|[? ?]]; eauto.
  Qed.

  (** ** Free variables after substitution *)
  (******************************************************************************)
  Corollary in_free_subst_iff : forall t u x y,
      y ∈ free (t '{x ~> u}) <->
      y ∈ free t /\ y <> x \/ x ∈ free t /\ y ∈ free u.
  Proof.
    intros. repeat rewrite in_free_iff.
    rewrite in_subst_iff'. now simpl_local.
  Qed.

  Corollary in_freeset_subst_iff : forall t u x y,
      y ∈@ freeset (t '{x ~> u}) <->
      y ∈@ freeset t /\ y <> x \/
      x ∈@ freeset t /\ y ∈@ freeset u.
  Proof.
    intros. repeat rewrite <- free_iff_freeset.
    apply in_free_subst_iff.
  Qed.

  (** ** Upper and lower bounds for leaves after substitution *)
  (******************************************************************************)
  Corollary in_subst_upper : forall t u l x,
      l ∈ t '{x ~> u} ->
      (l ∈ t /\ l <> Fr x) \/ l ∈ u.
  Proof.
    introv hin. rewrite in_subst_iff' in hin.
    intuition.
  Qed.

  Corollary in_free_subst_upper : forall t u x y,
      y ∈ free (t '{x ~> u}) ->
      (y ∈ free t /\ y <> x) \/ y ∈ free u.
  Proof.
    introv. rewrite ?(in_free_iff). rewrite in_subst_iff'.
    rewrite Fr_injective_not_iff. tauto.
  Qed.

 
  Corollary freeset_subst_upper : forall t u x,
      freeset (t '{x ~> u}) ⊆
              (freeset t \\ {{x}} ∪ freeset u)%set.
  Proof.
    intros t y x a.
    rewrite AtomSet.union_spec, AtomSet.diff_spec,
    AtomSet.singleton_spec.
    rewrite <- ?(free_iff_freeset).
    apply in_free_subst_upper.
  Qed.

  Corollary in_subst_lower : forall t u l x,
      l ∈ t /\ l <> Fr x ->
      l ∈ t '{x ~> u}.
  Proof with auto.
    intros; rewrite in_subst_iff'...
  Qed.

  Corollary in_free_subst_lower : forall t (u : T LN) x y,
      y ∈ free t -> y <> x ->
      y ∈ free (t '{x ~> u}).
  Proof.
    setoid_rewrite in_free_iff. intros.
    apply in_subst_lower; now simpl_local.
  Qed.

  Corollary freeset_subst_lower : forall t (u : T LN) x,
      freeset t \\ {{ x }} ⊆ freeset (t '{x ~> u}).
  Proof.
    introv. intro a.
    rewrite AtomSet.diff_spec, AtomSet.singleton_spec.
    do 2 rewrite <- free_iff_freeset.
    intros [? ?]. now apply in_free_subst_lower.
  Qed.

  Corollary scoped_subst_eq : forall t (u : T LN) x γ1 γ2,
      scoped t γ1 ->
      scoped u γ2 ->
      scoped (t '{x ~> u}) (γ1 \\ {{x}} ∪ γ2).
  Proof.
    introv St Su. unfold scoped in *.
    etransitivity. apply freeset_subst_upper. fsetdec.
  Qed.

  (** ** Substitution of fresh variables *)
  (******************************************************************************)
  Theorem subst_fresh : forall t x u,
      ~ x ∈ free t ->
      t '{x ~> u} = t.
  Proof.
    intros. apply subst_id. intros.
    assert (Fr x <> l). eapply (@ninf_in_neq T); eauto.
    now simpl_local.
  Qed.

  Corollary subst_fresh_set : forall t x u,
      ~ x ∈@ freeset t ->
      t '{x ~> u} = t.
  Proof.
    setoid_rewrite <- free_iff_freeset. apply subst_fresh.
  Qed.

  (** ** Composing substitutions *)
  (******************************************************************************)
  Lemma subst_subst_local : forall (u1 u2 : T LN) x1 x2,
      ~ x1 ∈ free u2 ->
      x1 <> x2 ->
      subst x2 u2 ∘ subst_loc x1 u1 =
      subst x1 (subst x2 u2 u1) ∘ subst_loc x2 u2.
  Proof with auto.
    intros. ext l. unfold compose. compare l to atom x1.
    - rewrite subst_loc_eq, subst_loc_neq,
      subst_in_ret, subst_loc_eq...
    - rewrite subst_loc_neq...
      compare values x2 and a.
      + rewrite subst_in_ret, subst_loc_eq, subst_fresh...
      + rewrite subst_loc_neq, 2(subst_in_ret), 2(subst_loc_neq)...
    - rewrite 2(subst_loc_b), 2(subst_in_ret), 2(subst_loc_b)...
  Qed.

  Theorem subst_subst : forall u1 u2 t (x1 x2 : atom),
      ~ x1 ∈ free u2 ->
      x1 <> x2 ->
      t '{x1 ~> u1} '{x2 ~> u2} =
      t '{x2 ~> u2} '{x1 ~> u1 '{x2 ~> u2} }.
  Proof.
    intros. unfold subst.
    compose near t.
    rewrite 2(kmon_bind2).
    fequal. now apply subst_subst_local.
  Qed.

  (** ** Commuting two substitutions *)
  (******************************************************************************)
  Corollary subst_subst_comm : forall u1 u2 t (x1 x2 : atom),
      x1 <> x2 ->
      ~ x1 ∈ free u2 ->
      ~ x2 ∈ free u1 ->
      t '{x1 ~> u1} '{x2 ~> u2} =
      t '{x2 ~> u2} '{x1 ~> u1}.
  Proof.
    intros. rewrite subst_subst; auto.
    rewrite (subst_fresh u1 x2 u2); auto.
  Qed.

  (** ** Local closure is preserved by substitution *)
  (******************************************************************************)
  Theorem subst_lc : forall u t x,
      locally_closed t ->
      locally_closed u ->
      locally_closed (subst x u t).
  Proof.
    unfold locally_closed. introv lct lcu hin.
    rewrite ind_subst_iff' in hin.
    destruct hin as [[? ?] | [n1 [n2 [h1 [h2 h3]]]]].
    - auto.
    - subst. specialize (lcu n2 l h2).
      unfold is_bound_or_free in *.
      destruct l; auto. unfold_monoid. lia.
  Qed.

  (** ** Decompose substitution into closing/opening *)
  (******************************************************************************)
  Lemma subst_spec_local : forall (u : T LN) w l x,
      subst_loc x u l =
      open_loc u (cobind (close_loc x) (w, l)).
  Proof.
    introv. compare l to atom x; autorewrite* with tea_local.
    - cbn. compare values x and x. unfold id.
      compare naturals w and w.
    - cbn. compare values x and a. (* todo fix fragile names *)
    - cbn. unfold id. compare naturals n and w.
      now compare naturals (S w) and w.
      now compare naturals (S n) and w.
  Qed.

  Theorem subst_spec : forall x u t,
      t '{x ~> u} = ('[x] t) '(u).
  Proof.
    intros. compose near t on right.
    unfold open, close, subst.
    rewrite (bindd_mapd).
    rewrite (bind_to_bindd).
    fequal. ext [w l].
    unfold compose; cbn.
    now erewrite subst_spec_local.
  Qed.

  (** ** Substitution when <<u>> is a LN **)
  (******************************************************************************)
  Definition subst_loc_LN x (u : LN) : LN -> LN :=
    fun l => match l with
          | Fr y => if x == y then u else Fr y
          | Bd n => Bd n
          end.

  Theorem subst_by_LN_spec : forall x l,
      subst x (ret l) = map (subst_loc_LN x l).
  Proof.
    intros. unfold subst. ext t.
    apply (bind_respectful_map).
    intros l' l'in. destruct l'.
    - cbn. compare values x and a.
    - reflexivity.
  Qed.

  (** ** Substitution by the same variable is the identity *)
  (******************************************************************************)
  Theorem subst_same : forall t x,
      t '{x ~> ret (Fr x)} = t.
  Proof.
    intros. apply subst_id.
    intros. compare l to atom x; now simpl_local.
  Qed.

  (** ** Free variables after variable closing *)
  (******************************************************************************)
  Lemma in_free_close_iff_loc1 : forall w l t x  y,
      (w, l) ∈d t ->
      close_loc x (w, l) = Fr y ->
      Fr y ∈ t /\ x <> y.
  Proof.
    introv lin heq. destruct l as [la | ln].
    - cbn in heq. destruct_eq_args x la.
      inverts heq.
      apply ind_implies_in in lin. tauto.
    - cbn in heq. compare_nats_args ln w; discriminate.
  Qed.

  Lemma in_free_close_iff_loc2 : forall t x y,
      x <> y ->
      Fr y ∈ t ->
      exists w l, (w, l) ∈d t /\ close_loc x (w, l) = Fr y.
  Proof.
    introv neq yin.
    rewrite (ind_iff_in) in yin. destruct yin as [w yin].
    exists w. exists (Fr y). cbn. compare values x and y.
  Qed.

  Theorem in_free_close_iff : forall t x y,
      y ∈ free ('[x] t) <-> y ∈ free t /\ x <> y.
  Proof.
    introv. rewrite (free_close_iff).
    rewrite (in_free_iff). split.
    - introv [? [? [? ?] ] ]. eauto using in_free_close_iff_loc1.
    - intros [? ?]. eauto using in_free_close_iff_loc2.
  Qed.

  Corollary in_free_close_iff1 : forall t x y,
      y <> x ->
      y ∈ free ('[x] t) <-> y ∈ free t.
  Proof.
    intros. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary freeset_close : forall t x,
      freeset ('[x] t) [=] freeset t \\ {{ x }}.
  Proof.
    introv. intro a. rewrite AtomSet.diff_spec.
    rewrite <- 2(free_iff_freeset). rewrite in_free_close_iff.
    rewrite AtomSet.singleton_spec. intuition.
  Qed.

  Corollary nin_free_close : forall t x,
      ~ (x ∈ free ('[x] t)).
  Proof.
    introv. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary nin_freeset_close : forall t x,
      ~ (x ∈@ freeset ('[x] t)).
  Proof.
    introv. rewrite <- free_iff_freeset. apply nin_free_close.
  Qed.

  (** ** Variable closing and local closure *)
  (******************************************************************************)
  Theorem close_lc_eq : forall t x,
      locally_closed t ->
      locally_closed_gap 1 (close x t).
  Proof.
    unfold locally_closed. introv lct hin.
    rewrite ind_close_iff in hin.
    destruct hin as [l1 [? ?]]. compare l1 to atom x; subst.
    - cbn. compare values x and x. unfold_lia.
    - cbn. compare values x and a.
    - cbn. compare naturals n and w.
      + unfold_lia.
      + (* contradiction *)
        specialize (lct w (Bd w) ltac:(assumption)).
        cbn in lct. now unfold_lia.
      + specialize (lct w (Bd n) ltac:(assumption)).
        cbn in lct. now unfold_lia.
  Qed.

  (** ** Upper and lower bounds on free variables after opening *)
  (******************************************************************************)
  Lemma free_open_upper_local : forall t (u : T LN) w l x,
      l ∈ t ->
      x ∈ free (open_loc u (w, l)) ->
      (l = Fr x /\ x ∈ free t) \/
      x ∈ free u.
  Proof with auto.
    introv lin xin. rewrite in_free_iff in xin.
    rewrite 2(in_free_iff). destruct l as [y | n].
    - left. autorewrite with tea_local in xin. inverts xin...
    - right. cbn in xin. compare naturals n and w.
      { contradict xin. simpl_local. easy. }
      { assumption. }
      { contradict xin. simpl_local. easy. }
  Qed.

  Theorem free_open_upper : forall t (u : T LN) x,
      x ∈ free (t '(u)) ->
      x ∈ free t \/ x ∈ free u.
  Proof.
    introv xin.
    rewrite free_open_iff in xin.
    destruct xin as [w [l [hin ?]]].
    apply (ind_implies_in) in hin.
    enough ((l = Fr x /\ x ∈ free t) \/ x ∈ free u) by intuition.
    eauto using free_open_upper_local.
  Qed.

  Corollary freeset_open_upper : forall t (u : T LN),
      freeset (t '(u)) ⊆ freeset t ∪ freeset u.
  Proof.
    intros. intro a. rewrite AtomSet.union_spec.
    repeat rewrite <- (free_iff_freeset).
    auto using free_open_upper.
  Qed.

  Theorem free_open_lower : forall t u x,
      x ∈ free t ->
      x ∈ free (t '(u)).
  Proof.
    introv xin.
    rewrite (in_free_iff) in xin.
    rewrite (ind_iff_in) in xin.
    destruct xin as [w xin].
    rewrite (free_open_iff).
    setoid_rewrite (in_free_iff).
    exists w (Fr x). now autorewrite with tea_local.
  Qed.

  Corollary freeset_open_lower : forall t u,
      freeset t ⊆ freeset (t '(u)).
  Proof.
    intros. intro a. rewrite <- 2(free_iff_freeset).
    apply free_open_lower.
  Qed.

  (** ** Opening a locally closed term is the identity *)
  (**************************************************************************)
  Lemma open_lc_local : forall (u : T LN) w l,
      is_bound_or_free 0 (w, l) ->
      open_loc u (w, l) = ret l.
  Proof.
    introv hyp. destruct l as [a | n].
    - reflexivity.
    - cbn in *. compare naturals n and w; unfold_lia.
  Qed.

  Theorem open_lc : forall t u,
      locally_closed t ->
      t '(u) = t.
  Proof.
    introv lc. apply open_id. introv lin.
    specialize (lc _ _ lin).
    destruct l; auto using open_lc_local.
  Qed.

  (** ** Opening followed by substitution *)
  (**************************************************************************)
  Lemma subst_open_local : forall u1 u2 x,
      locally_closed u2 ->
      subst x u2 ∘ open_loc u1 =
      open_loc (u1 '{x ~> u2}) ⋆5 (subst_loc x u2 ∘ extract).
  Proof.
    introv lcu2. ext [w l]. unfold kc5.
    unfold preincr, compose; cbn. compare l to atom x.
    - rewrite subst_in_ret. cbn.
      compare values x and x. symmetry.
      apply (bindd_respectful_id).
      intros. destruct a.
      + reflexivity.
      + unfold locally_closed, locally_closed_gap, is_bound_or_free in lcu2. cbn.
        compare naturals n and (w ● w0).
        { specialize (lcu2 _ _ ltac:(eauto)). cbn in lcu2. unfold_lia. }
        { specialize (lcu2 _ _ ltac:(eauto)). cbn in lcu2. unfold_lia. }
    - rewrite subst_in_ret. cbn. compare values x and a.
      compose near (Fr a).
      now rewrite (kmond_bindd0).
    - compare naturals n and w; cbn.
      + rewrite subst_in_ret. compose near (Bd n) on right.
        rewrite (kmond_bindd0); unfold compose. cbn.
        rewrite monoid_id_l. compare naturals n and w.
      + compose near (Bd w) on right.
        rewrite (kmond_bindd0). unfold compose. cbn.
        rewrite monoid_id_l. compare naturals w and w.
      + rewrite subst_in_ret.
        compose near (Bd n) on right.
        rewrite (kmond_bindd0). unfold compose. cbn.
        rewrite monoid_id_l. compare naturals n and w.
  Qed.

  Theorem subst_open :  forall u1 u2 t x,
      locally_closed u2 ->
      t '(u1) '{x ~> u2} =
      t '{x ~> u2} '(u1 '{x ~> u2}).
  Proof.
    introv lc.
    compose near t.
    unfold open, subst at 1 3.
    rewrite (bind_bindd).
    rewrite (bindd_bind).
    fequal.
    change_left (subst x u2 ∘ open_loc u1).
    #[local] Set Keyed Unification.
    rewrite subst_open_local; [|auto].
    #[local] Unset Keyed Unification.
    now ext [w t'].
  Qed.

  (** ** Decompose opening into variable opening followed by substitution *)
  (**************************************************************************)
  Lemma open_spec_local : forall u x w l,
      l <> Fr x ->
      (subst x u ∘ open_loc (ret (Fr x))) (w, l) =
      open_loc u (w, l).
  Proof.
    introv neq. unfold compose. compare l to atom x.
    - contradiction.
    - autorewrite with tea_local. rewrite subst_in_ret.
      now rewrite subst_loc_neq.
    - cbn. compare naturals n and w.
      now rewrite subst_in_ret.
      now rewrite subst_in_ret, subst_loc_eq.
      now rewrite subst_in_ret, subst_loc_b.
  Qed.

  (* This theorem would be easy to prove with [subst_open_eq], but
   applying that theorem would introduce a local closure hypothesis
   for <<u>> that is not actually required for our purposes. *)
  Theorem open_spec_eq : forall u t x,
      ~ x ∈@ freeset t ->
      t '(u) = t '(ret (Fr x)) '{x ~> u}.
  Proof.
    introv fresh. compose near t on right.
    unfold subst, open.
    rewrite (bind_bindd).
    apply (bindd_respectful). introv hin.
    assert (a <> Fr x).
    { apply (ind_implies_in) in hin.
      rewrite <- free_iff_freeset in fresh.
      eapply ninf_in_neq in fresh; eauto. }
    now rewrite <- (open_spec_local u x).
  Qed.

  (** ** Opening by a variable, followed by non-equal substitution *)
  (**************************************************************************)
  Lemma subst_open_var_loc : forall u x y,
      x <> y ->
      locally_closed u ->
      subst x u ∘ open_loc (ret (Fr y)) =
      open_loc (ret (Fr y)) ⋆5 (subst_loc x u ∘ extract).
  Proof with auto.
    introv neq lc. rewrite subst_open_local...
    rewrite subst_in_ret. cbn. compare values x and y.
  Qed.

  Theorem subst_open_var : forall u t x y,
      x <> y ->
      locally_closed u ->
      t '(ret (Fr y)) '{x ~> u} =
      t '{x ~> u} '(ret (Fr y)).
  Proof.
    introv neq lc. compose near t.
    unfold open, subst.
    rewrite (bind_bindd), (bindd_bind).
    fequal.
    change_left (subst x u ∘ open_loc (ret (Fr y))).
    #[local] Set Keyed Unification.
    rewrite subst_open_var_loc; auto.
    #[local] Unset Keyed Unification.
    now ext [w t'].
  Qed.

  (** ** Closing, followed by opening *)
  (**************************************************************************)
  Lemma open_close_local : forall x w l,
      (open_loc (ret (Fr x)) ⋆4 close_loc x)
      (w, l) = ret l.
  Proof.
    intros. cbn. unfold id. compare l to atom x.
    - compare values x and x. compare naturals w and w.
    - compare values x and a.
    - compare naturals n and w.
      compare naturals (S w) and w.
      compare naturals (S n) and w.
  Qed.

  Theorem open_close : forall x t,
      ('[x] t) '(ret (Fr x)) = t.
  Proof.
    intros. compose near t on left.
    unfold open, close.
    rewrite (bindd_mapd).
    apply (bindd_respectful_id); intros.
    auto using open_close_local.
  Qed.

  (** ** Opening by a LN reduces to an [mapkr] *)
  Definition open_LN_loc (u : LN) : nat * LN -> LN :=
    fun wl => match wl with
           | (w, l) =>
             match l with
             | Fr x => Fr x
             | Bd n =>
               match Nat.compare n w with
               | Gt => Bd (n - 1)
               | Eq => u
               | Lt => Bd n
               end
             end
           end.

  Lemma open_by_LN_spec : forall l,
      open (ret l) = mapd (open_LN_loc l).
  Proof.
    intros. unfold open. ext t.
    apply (bindd_respectful_mapd).
    intros w l' l'in. destruct l'.
    - reflexivity.
    - cbn. compare naturals n and w.
  Qed.

  (** ** Opening, followed by closing *)
  (**************************************************************************)
  Lemma close_open_local : forall x w l,
      l <> Fr x ->
      (close_loc x ⋆4 open_LN_loc (Fr x)) (w, l) = l.
  Proof.
    introv neq. cbn. unfold id. compare l to atom x.
    - contradiction.
    - unfold compose; cbn. now compare values x and a.
    - unfold compose; cbn.
      compare naturals n and w. compare values x and x.
      compare naturals (n - 1) and w.
  Qed.

  Theorem close_open : forall x t,
      ~ x ∈ free t ->
      '[x] (t '(ret (Fr x))) = t.
  Proof.
    introv fresh. compose near t on left.
    rewrite open_by_LN_spec. unfold close.
    rewrite (dfun_mapd2).
    apply (mapd_respectful_id).
    intros w l lin.
    assert (l <> Fr x).
    { rewrite neq_symmetry. apply (ind_implies_in) in lin.
      eauto using (ninf_in_neq (T := T)). }
    now apply close_open_local.
  Qed.

  (** ** Opening and local closure *)
  (**************************************************************************)
  Lemma open_lc_gap_eq_1 : forall n t u,
      locally_closed u ->
      locally_closed_gap n t ->
      locally_closed_gap (n - 1) (t '(u)).
  Proof.
    unfold locally_closed_gap.
    introv lcu lct Hin. rewrite ind_open_iff in Hin.
    destruct Hin as [n1 [n2 [l1 [h1 [h2 h3]]]]].
    destruct l1.
    - cbn in h2. rewrite (ind_ret_iff) in h2.
      destruct h2; subst. cbn. trivial.
    - specialize (lct _ _ h1). cbn in h2. compare naturals n0 and n1.
      + rewrite (ind_ret_iff) in h2; destruct h2; subst.
        cbn. unfold_monoid. lia.
      + specialize (lcu n2 l h2). unfold is_bound_or_free in *.
        destruct l; [trivial|]. unfold_monoid. lia.
      + rewrite (ind_ret_iff) in h2. destruct h2; subst.
        unfold is_bound_or_free in *. unfold_lia.
  Qed.

  Lemma open_lc_gap_eq_2 : forall n t u,
      n > 0 ->
      locally_closed u ->
      locally_closed_gap (n - 1) (t '(u)) ->
      locally_closed_gap n t.
  Proof.
    unfold locally_closed_gap.
    introv ngt lcu lct Hin. setoid_rewrite (ind_open_iff) in lct.
    destruct l.
    - cbv. trivial.
    - compare naturals n0 and w.
      + specialize (lct w (Bd n0)).
        lapply lct.
        { cbn; unfold_lia. }
        { exists w (Ƶ : nat) (Bd n0).
          split; auto. cbn. compare naturals n0 and w.
          rewrite (ind_ret_iff). now simpl_monoid. }
      + cbn. unfold_lia.
      + cbn. specialize (lct w (Bd (n0 - 1))).
        lapply lct.
        { cbn; unfold_lia. }
        { exists w (Ƶ : nat) (Bd n0).
          split; auto. cbn. compare naturals n0 and w.
          rewrite (ind_ret_iff). now simpl_monoid. }
  Qed.

  Theorem open_lc_gap_eq_iff : forall n t u,
      n > 0 ->
      locally_closed u ->
      locally_closed_gap n t <->
      locally_closed_gap (n - 1) (t '(u)).
  Proof.
    intros; intuition (eauto using open_lc_gap_eq_1, open_lc_gap_eq_2).
  Qed.

  Corollary open_lc_gap_eq_var : forall n t x,
      n > 0 ->
      locally_closed_gap n t <->
      locally_closed_gap (n - 1) (t '(ret (Fr x))).
  Proof.
    intros. apply open_lc_gap_eq_iff. auto.
    intros w l hin. rewrite (ind_ret_iff) in hin.
    destruct hin; subst. cbv. trivial.
  Qed.

  Corollary open_lc_gap_eq_iff_1 : forall t u,
      locally_closed u ->
      locally_closed_gap 1 t <->
      locally_closed (t '(u)).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_iff; auto.
    reflexivity.
  Qed.

  Corollary open_lc_gap_eq_var_1 : forall t x,
      locally_closed_gap 1 t <->
      locally_closed (t '(ret (Fr x))).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_var; auto.
    reflexivity.
  Qed.

End locally_nameless_metatheory.
