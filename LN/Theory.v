(** This files contains metatheorems for the locally nameless variables
 that closely parallel those of LNgen. *)
From Tealeaves Require Import
  LN.Leaf LN.Atom LN.AtomSet LN.Operations
  Data.Natural
  Theory.List.Kleisli
  Theory.Kleisli.DT.Monad.

Import DT.Monad.DerivedInstances.Operations.
Import DT.Monad.DerivedInstances.Instances.

Import Comonad.Notations.
Import LN.AtomSet.Notations.
Import Operations.Notations.
Import Setlike.Functor.Notations.
Import DT.Monad.Notations.
Import Monoid.Notations.
#[local] Open Scope set_scope.

#[local] Generalizable Variable T.

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

  Context
    `{DT.Monad.Monad nat T
     (unit := Monoid_unit_zero)
     (op := Monoid_op_plus)}.

  Implicit Types (l : leaf) (n : nat) (t : T leaf) (x : atom).

  (** ** Reasoning principles for proving equalities *)
  (******************************************************************************)

  (** *** <<open>> *)
  (******************************************************************************)
  Lemma open_eq : forall t u1 u2,
      (forall w l, (w, l) ∈d t -> open_loc u1 (w, l) = open_loc u2 (w, l)) ->
      t '(u1) = t '(u2).
  Proof.
    intros. unfold open.
    now apply (bindd_respectful T).
  Qed.

  Lemma open_id : forall t u,
      (forall w l, (w, l) ∈d t -> open_loc u (w, l) = ret T l) ->
      t '(u) = t.
  Proof.
    intros. unfold open.
    now apply (bindd_respectful_id T).
  Qed.

  (** *** <<close>> *)
  (******************************************************************************)
  Lemma close_eq : forall t x y,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = close_loc y (w, l)) ->
      '[x] t = '[y] t.
  Proof.
    intros. unfold close.
    now apply (fmapd_respectful T).
  Qed.

  Lemma close_id : forall t x,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = l) ->
      '[x] t = t.
  Proof.
     intros. unfold close.
    now apply (fmapd_respectful_id T).
  Qed.

  (** *** <<subst>> *)
  (******************************************************************************)
  Lemma subst_eq : forall t x y u1 u2,
      (forall l, l ∈ t -> subst_loc x u1 l = subst_loc y u2 l) ->
      t '{x ~> u1} = t '{y ~> u2}.
  Proof.
    intros. unfold subst.
    now apply (bind_respectful T).
  Qed.

  Lemma subst_id : forall t x u,
      (forall l, l ∈ t -> subst_loc x u l = ret T l) ->
      t '{x ~> u} = t.
  Proof.
    intros. unfold subst.
    now apply (bind_respectful_id T).
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
    now rewrite (ind_bindd_iff T).
  Qed.

  Lemma in_open_iff : forall l u t,
      l ∈ t '(u) <-> exists n1 l1,
        (n1, l1) ∈d t /\ l ∈ open_loc u (n1, l1).
  Proof.
    intros. unfold open.
    now rewrite (in_bindd_iff T).
  Qed.

  (** *** <<close>> *)
  (******************************************************************************)
  Lemma ind_close_iff : forall l n x t,
      (n, l) ∈d '[x] t <-> exists l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite (ind_fmapd_iff T).
  Qed.

  Lemma in_close_iff : forall l x t,
      l ∈ '[x] t <-> exists n l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite (in_fmapd_iff T).
  Qed.

  (** *** <<subst>> *)
  (******************************************************************************)
  Lemma ind_subst_iff : forall n l u t x,
      (n, l) ∈d t '{x ~> u} <-> exists n1 n2 l1,
        (n1, l1) ∈d t /\ (n2, l) ∈d subst_loc x u l1 /\ n = n1 ● n2.
  Proof.
    intros. unfold subst.
    now rewrite (ind_bind_iff T).
  Qed.

  Lemma in_subst_iff : forall l u t x,
      l ∈ t '{x ~> u} <-> exists l1,
       l1 ∈ t /\ l ∈ subst_loc x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (in_bind_iff T).
  Qed.

  (** ** Free variables *)
  (******************************************************************************)

  (** *** Specifications for [free] and [freeset] *)
  (******************************************************************************)
  Theorem in_free_iff : forall (t : T leaf) (x : atom),
      x ∈ free T t <-> Fr x ∈ t.
  Proof.
    intros. unfold free.
    (*
    rewrite (in_bind_iff list).
    split.
    - intros [l ?]. destruct l.
      + rewrite in_iff_in_list. cbn in *.
        cut (a = x). now intro; subst. tauto.
      + cbn in *. tauto.
    - exists (Fr x). rewrite <- (in_iff_in_list).
      cbn. tauto.
  Qed.
     *)
  Admitted.

  Theorem free_iff_freeset : forall (t : T leaf) (x : atom),
      x ∈ free T t <-> x ∈@ freeset T t.
  Proof.
    intros. unfold freeset. rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  (** *** Opening *)
  (******************************************************************************)
  Lemma free_open_iff : forall u t x,
      x ∈ free T (t '(u)) <-> exists w l1,
        (w, l1) ∈d t /\ x ∈ free T (open_loc u (w, l1)).
  Proof.
    intros. rewrite in_free_iff. setoid_rewrite (in_free_iff).
    now rewrite in_open_iff.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma free_close_iff : forall t x y,
      y ∈ free T ('[x] t) <-> exists w l1,
        (w, l1) ∈d t /\ close_loc x (w, l1) = Fr y.
  Proof.
    intros. rewrite in_free_iff.
    now rewrite in_close_iff.
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma free_subst_iff : forall u t x y,
      y ∈ free T (t '{x ~> u}) <-> exists l1,
        l1 ∈ t /\ y ∈ free T (subst_loc x u l1).
  Proof.
    intros. rewrite (in_free_iff). setoid_rewrite (in_free_iff).
    now rewrite (in_subst_iff).
  Qed.

End locally_nameless_basic_principles.

(** * Utilities for reasoning at the leaves *)
(******************************************************************************)
Section locally_nameless_utilities.

  Context
    `{DT.Monad.Monad nat T
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
  Lemma subst_loc_eq : forall (u : T leaf) x,
      subst_loc x u (Fr x) = u.
  Proof. intros. cbn. now compare values x and x. Qed.

  Lemma subst_loc_neq : forall (u : T leaf) x y,
      y <> x -> subst_loc x u (Fr y) = ret T (Fr y).
  Proof. intros. cbn. now compare values x and y. Qed.

  Lemma subst_loc_b : forall u x n,
      subst_loc x u (Bd n) = ret T (Bd n).
  Proof. reflexivity. Qed.

  Lemma subst_loc_fr_neq : forall (u : T leaf) l x,
      Fr x <> l -> subst_loc x u l = ret T l.
  Proof.
    introv neq. unfold subst_loc.
    destruct l as [a|?]; [compare values x and a | reflexivity ].
  Qed.

  (** ** [open_loc] *)
  (******************************************************************************)
  Lemma open_loc_lt : forall (u : T leaf) w n,
      n < w -> open_loc u (w, Bd n) = ret T (Bd n).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and w.
  Qed.

  Lemma open_loc_gt : forall (u : T leaf) n w,
      n > w -> open_loc u (w, Bd n) = ret T (Bd (n - 1)).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and w.
  Qed.

  Lemma open_loc_eq : forall w (u : T leaf),
      open_loc u (w, Bd w) = u.
  Proof.
    introv. unfold open_loc. compare naturals w and w.
  Qed.

  Lemma open_loc_atom : forall (u : T leaf) w x,
      open_loc u (w, Fr x) = ret T (Fr x).
  Proof.
    reflexivity.
  Qed.

  (** ** [Miscellaneous utilities] *)
  (******************************************************************************)
  Lemma ninf_in_neq : forall x l (t : T leaf),
      ~ x ∈ free T t ->
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
    `{DT.Monad.Monad nat T
     (unit := Monoid_unit_zero)
     (op := Monoid_op_plus)}.

  Import Kleisli.DT.Monad.ToFunctor.Operation.
  Import Kleisli.DT.Monad.ToFunctor.Instance.
  Import Kleisli.DT.Monad.DerivedInstances.Instances.

  Lemma subst_in_ret : forall x l (u : T leaf),
      (ret T l) '{x ~> u} = subst_loc x u l.
  Proof.
    intros. unfold subst. compose near l on left.
    change_left ((bind T (subst_loc x u) ∘ ret T) l).
    now rewrite (kmon_bind0 T).
  Qed.

  Implicit Types
           (l : leaf) (p : leaf)
           (x : atom) (t : T leaf)
           (w : nat) (n : nat).

  (** ** Leaf analysis: substitution with contexts *)
  (******************************************************************************)
  Lemma ind_subst_loc_iff : forall l w p (u : T leaf) x,
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

  (** ** Leaf analysis: substitution without contexts *)
  (******************************************************************************)
  Lemma in_subst_loc_iff : forall l p (u : T leaf) x,
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
      y ∈ free T (t '{x ~> u}) <->
      y ∈ free T t /\ y <> x \/ x ∈ free T t /\ y ∈ free T u.
  Proof.
    intros. repeat rewrite (in_free_iff).
    rewrite in_subst_iff'. now simpl_local.
  Qed.

  Corollary in_freeset_subst_iff : forall t u x y,
      y ∈@ freeset T (t '{x ~> u}) <->
      y ∈@ freeset T t /\ y <> x \/
      x ∈@ freeset T t /\ y ∈@ freeset T u.
  Proof.
    intros. repeat rewrite <- (free_iff_freeset).
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
      y ∈ free T (t '{x ~> u}) ->
      (y ∈ free T t /\ y <> x) \/ y ∈ free T u.
  Proof.
    introv. rewrite ?(in_free_iff). rewrite in_subst_iff'.
    rewrite Fr_injective_not_iff. tauto.
  Qed.

  Corollary freeset_subst_upper : forall t u x,
      freeset T (t '{x ~> u}) ⊆
              (freeset T t \\ {{x}} ∪ freeset T u).
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

  Corollary in_free_subst_lower : forall t (u : T leaf) x y,
      y ∈ free T t -> y <> x ->
      y ∈ free T (t '{x ~> u}).
  Proof.
    setoid_rewrite in_free_iff. intros.
    apply in_subst_lower; now simpl_local.
  Qed.

  Corollary freeset_subst_lower : forall t (u : T leaf) x,
      freeset T t \\ {{ x }} ⊆ freeset T (t '{x ~> u}).
  Proof.
    introv. intro a.
    rewrite AtomSet.diff_spec, AtomSet.singleton_spec.
    do 2 rewrite <- (free_iff_freeset).
    intros [? ?]. now apply in_free_subst_lower.
  Qed.

  Corollary scoped_subst_eq : forall t (u : T leaf) x γ1 γ2,
      scoped T t γ1 ->
      scoped T u γ2 ->
      scoped T (t '{x ~> u}) (γ1 \\ {{x}} ∪ γ2).
  Proof.
    introv St Su. unfold scoped in *.
    etransitivity. apply freeset_subst_upper. fsetdec.
  Qed.

  (** ** Substitution of fresh variables *)
  (******************************************************************************)
  Theorem subst_fresh : forall t x u,
      ~ x ∈ free T t ->
      t '{x ~> u} = t.
  Proof.
    intros. apply subst_id. intros.
    assert (Fr x <> l). eapply (@ninf_in_neq T); eauto.
    now simpl_local.
  Qed.

  Corollary subst_fresh_set : forall t x u,
      ~ x ∈@ freeset T t ->
      t '{x ~> u} = t.
  Proof.
    setoid_rewrite <- free_iff_freeset. apply subst_fresh.
  Qed.

  (** ** Composing substitutions *)
  (******************************************************************************)
  Lemma subst_subst_local : forall (u1 u2 : T leaf) x1 x2,
      ~ x1 ∈ free T u2 ->
      x1 <> x2 ->
      subst T x2 u2 ∘ subst_loc x1 u1 =
      subst T x1 (subst T x2 u2 u1) ∘ subst_loc x2 u2.
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
      ~ x1 ∈ free T u2 ->
      x1 <> x2 ->
      t '{x1 ~> u1} '{x2 ~> u2} =
      t '{x2 ~> u2} '{x1 ~> u1 '{x2 ~> u2} }.
  Proof.
    intros. unfold subst.
    compose near t.
    rewrite 2(kmon_bind2 T).
    fequal. now apply subst_subst_local.
  Qed.

  (** ** Commuting two substitutions *)
  (******************************************************************************)
  Corollary subst_subst_comm : forall u1 u2 t (x1 x2 : atom),
      x1 <> x2 ->
      ~ x1 ∈ free T u2 ->
      ~ x2 ∈ free T u1 ->
      t '{x1 ~> u1} '{x2 ~> u2} =
      t '{x2 ~> u2} '{x1 ~> u1}.
  Proof.
    intros. rewrite subst_subst; auto.
    rewrite (subst_fresh u1 x2 u2); auto.
  Qed.

  (** ** Local closure is preserved by substitution *)
  (******************************************************************************)
  Theorem subst_lc : forall u t x,
      locally_closed T t ->
      locally_closed T u ->
      locally_closed T (subst T x u t).
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
  Lemma subst_spec_local : forall (u : T leaf) w l x,
      subst_loc x u l =
      open_loc u (cobind (prod nat) (close_loc x) (w, l)).
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
    (*
    rewrite (bindd_fmapd T).
    symmetry. apply (subd_respectful_sub F).
    symmetry. apply subst_spec_local.
  Qed.
     *)
  Admitted.

  (** ** Substitution when <<u>> is a leaf **)
  (******************************************************************************)
  Definition subst_loc_leaf x (u : leaf) : leaf -> leaf :=
    fun l => match l with
          | Fr y => if x == y then u else Fr y
          | Bd n => Bd n
          end.

  Theorem subst_by_leaf_spec : forall x l,
      subst T x (ret T l) = fmap T (subst_loc_leaf x l).
  Proof.
    intros. unfold subst. ext t.
    apply (bind_respectful_fmap T).
    intros l' l'in. destruct l'.
    - cbn. compare values x and a.
    - reflexivity.
  Qed.

  (** ** Substitution by the same variable is the identity *)
  (******************************************************************************)
  Theorem subst_same : forall t x,
      t '{x ~> ret T (Fr x)} = t.
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
      inverts heq. apply (ind_implies_in T) in lin. tauto.
    - cbn in heq. compare_nats_args ln w; discriminate.
  Qed.

  Lemma in_free_close_iff_loc2 : forall t x y,
      x <> y ->
      Fr y ∈ t ->
      exists w l, (w, l) ∈d t /\ close_loc x (w, l) = Fr y.
  Proof.
    introv neq yin.
    rewrite (ind_iff_in T) in yin. destruct yin as [w yin].
    exists w. exists (Fr y). cbn. compare values x and y.
  Qed.

  Theorem in_free_close_iff : forall t x y,
      y ∈ free T ('[x] t) <-> y ∈ free T t /\ x <> y.
  Proof.
    introv. rewrite (free_close_iff).
    rewrite (in_free_iff). split.
    - introv [? [? [? ?] ] ]. eauto using in_free_close_iff_loc1.
    - intros [? ?]. eauto using in_free_close_iff_loc2.
  Qed.

  Corollary in_free_close_iff1 : forall t x y,
      y <> x ->
      y ∈ free T ('[x] t) <-> y ∈ free T t.
  Proof.
    intros. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary freeset_close : forall t x,
      freeset T ('[x] t) [=] freeset T t \\ {{ x }}.
  Proof.
    introv. intro a. rewrite AtomSet.diff_spec.
    rewrite <- 2(free_iff_freeset). rewrite in_free_close_iff.
    rewrite AtomSet.singleton_spec. intuition.
  Qed.

  Corollary nin_free_close : forall t x,
      ~ (x ∈ free T ('[x] t)).
  Proof.
    introv. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary nin_freeset_close : forall t x,
      ~ (x ∈@ freeset T ('[x] t)).
  Proof.
    introv. rewrite <- free_iff_freeset. apply nin_free_close.
  Qed.

  (** ** Variable closing and local closure *)
  (******************************************************************************)
  Theorem close_lc_eq : forall t x,
      locally_closed T t ->
      locally_closed_gap T 1 (close T x t).
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
  Lemma free_open_upper_local : forall t (u : T leaf) w l x,
      l ∈ t ->
      x ∈ free T (open_loc u (w, l)) ->
      (l = Fr x /\ x ∈ free T t) \/
      x ∈ free T u.
  Proof with auto.
    introv lin xin. rewrite in_free_iff in xin.
    rewrite 2(in_free_iff). destruct l as [y | n].
    - left. autorewrite with tea_local in xin. inverts xin...
    - right. cbn in xin. compare naturals n and w.
      { contradict xin. simpl_local. easy. }
      { assumption. }
      { contradict xin. simpl_local. easy. }
  Qed.

  Theorem free_open_upper : forall t (u : T leaf) x,
      x ∈ free T (t '(u)) ->
      x ∈ free T t \/ x ∈ free T u.
  Proof.
    introv xin.
    rewrite free_open_iff in xin.
    destruct xin as [w [l [hin ?]]].
    apply (ind_implies_in T) in hin.
    enough ((l = Fr x /\ x ∈ free T t) \/ x ∈ free T u) by intuition.
    eauto using free_open_upper_local.
  Qed.

  Corollary freeset_open_upper : forall t (u : T leaf),
      freeset T (t '(u)) ⊆ freeset T t ∪ freeset T u.
  Proof.
    intros. intro a. rewrite AtomSet.union_spec.
    repeat rewrite <- (free_iff_freeset).
    auto using free_open_upper.
  Qed.

  Theorem free_open_lower : forall t u x,
      x ∈ free T t ->
      x ∈ free T (t '(u)).
  Proof.
    introv xin.
    rewrite (in_free_iff) in xin.
    rewrite (ind_iff_in T) in xin.
    destruct xin as [w xin].
    rewrite (free_open_iff).
    setoid_rewrite (in_free_iff).
    exists w (Fr x). now autorewrite with tea_local.
  Qed.

  Corollary freeset_open_lower : forall t u,
      freeset T t ⊆ freeset T (t '(u)).
  Proof.
    intros. intro a. rewrite <- 2(free_iff_freeset).
    apply free_open_lower.
  Qed.

  (** ** Opening a locally closed term is the identity *)
  (**************************************************************************)
  Lemma open_lc_local : forall (u : T leaf) w l,
      is_bound_or_free 0 (w, l) ->
      open_loc u (w, l) = ret T l.
  Proof.
    introv hyp. destruct l as [a | n].
    - reflexivity.
    - cbn in *. compare naturals n and w; unfold_lia.
  Qed.

  Theorem open_lc : forall t u,
      locally_closed T t ->
      t '(u) = t.
  Proof.
    introv lc. apply open_id. introv lin.
    specialize (lc _ _ lin).
    destruct l; auto using open_lc_local.
  Qed.

  Import Decorated.Monad.Notations.

  (** ** Opening followed by substitution *)
  (**************************************************************************)
  Lemma subst_open_local : forall u1 u2 x,
      locally_closed T u2 ->
      subst T x u2 ∘ open_loc u1 =
      open_loc (u1 '{x ~> u2}) ⋆dm (subst_loc x u2 ∘ extract (prod nat)).
  Proof.
    introv lcu2. ext [w l]. unfold kcompose_dm.
    unfold prepromote, compose; cbn. compare l to atom x.
    - rewrite subst_in_ret. cbn.
      compare values x and x. symmetry.
      apply (bindd_respectful_id T).
      intros. destruct a.
      + reflexivity.
      + unfold locally_closed, locally_closed_gap, is_bound_or_free in lcu2. cbn.
        compare naturals n and (w ● w0).
        { specialize (lcu2 _ _ ltac:(eauto)). cbn in lcu2. unfold_lia. }
        { specialize (lcu2 _ _ ltac:(eauto)). cbn in lcu2. unfold_lia. }
    - rewrite subst_in_ret. cbn. compare values x and a.
      compose near (Fr a). now rewrite (kmond_bindd0 T).
    - compare naturals n and w; cbn.
      + rewrite subst_in_ret. compose near (Bd n) on right.
        rewrite (kmond_bindd0 T); unfold compose. cbn.
        rewrite monoid_id_l. compare naturals n and w.
      + compose near (Bd w) on right.
        rewrite (kmond_bindd0 T). unfold compose. cbn.
        rewrite monoid_id_l. compare naturals w and w.
      + rewrite subst_in_ret.
        compose near (Bd n) on right.
        rewrite (kmond_bindd0 T). unfold compose. cbn.
        rewrite monoid_id_l. compare naturals n and w.
  Qed.

  Theorem subst_open :  forall u1 u2 t x,
      locally_closed T u2 ->
      t '(u1) '{x ~> u2} =
      t '{x ~> u2} '(u1 '{x ~> u2}).
  Proof.
    introv lc. compose near t.
    unfold open, subst at 1 3.
    rewrite (bind_bindd T).
    rewrite (bindd_bind T).
    fequal.
    #[local] Set Keyed Unification.
    rewrite subst_open_local; auto.
    #[local] Unset Keyed Unification.
  Qed.

  (** ** Decompose opening into variable opening followed by substitution *)
  (**************************************************************************)
  Lemma open_spec_local : forall u x w l,
      l <> Fr x ->
      (subst T x u ∘ open_loc (ret T (Fr x))) (w, l) =
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
      ~ x ∈@ freeset T t ->
      t '(u) = t '(ret T (Fr x)) '{x ~> u}.
  Proof.
    introv fresh. compose near t on right.
    unfold subst, open.
    rewrite (bind_bindd T).
    apply (bindd_respectful T). introv hin.
    assert (a <> Fr x).
    { apply (ind_implies_in T) in hin.
      rewrite <- free_iff_freeset in fresh.
      eapply ninf_in_neq in fresh; eauto. }
    now rewrite <- (open_spec_local u x).
  Qed.

  (** ** Opening by a variable, followed by non-equal substitution *)
  (**************************************************************************)
  Lemma subst_open_var_loc : forall u x y,
      x <> y ->
      locally_closed T u ->
      subst T x u ∘ open_loc (ret T (Fr y)) =
      open_loc (ret T (Fr y)) ⋆dm (subst_loc x u ∘ extract (prod nat)).
  Proof with auto.
    introv neq lc. rewrite subst_open_local...
    rewrite subst_in_ret. cbn. compare values x and y.
  Qed.

  Theorem subst_open_var : forall u t x y,
      x <> y ->
      locally_closed T u ->
      t '(ret T (Fr y)) '{x ~> u} =
      t '{x ~> u} '(ret T (Fr y)).
  Proof.
    introv neq lc. compose near t.
    unfold open, subst.
    rewrite (bind_bindd T), (bindd_bind T).
    fequal.
    change_left (subst T x u ∘ open_loc (ret T (Fr y))).
    #[local] Set Keyed Unification.
    rewrite subst_open_var_loc; auto.
    #[local] Unset Keyed Unification.
  Qed.

  (** ** Closing, followed by opening *)
  (**************************************************************************)
  Lemma open_close_local : forall x w l,
      (open_loc (ret T (Fr x)) co⋆ close_loc x)
      (w, l) = ret T l.
  Proof.
    intros. cbn. unfold id. compare l to atom x.
    - compare values x and x. compare naturals w and w.
    - compare values x and a.
    - compare naturals n and w.
      compare naturals (S w) and w.
      compare naturals (S n) and w.
  Qed.

  Theorem open_close : forall x t,
      ('[x] t) '(ret T (Fr x)) = t.
  Proof.
    intros. compose near t on left.
    unfold open, close.
    rewrite (bindd_fmapd T).
    apply (bindd_respectful_id T); intros.
    auto using open_close_local.
  Qed.

  (** ** Opening by a leaf reduces to an [fmapkr] *)
  Definition open_leaf_loc (u : leaf) : nat * leaf -> leaf :=
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

  Lemma open_by_leaf_spec : forall l,
      open T (ret T l) = fmapd T (open_leaf_loc l).
  Proof.
    intros. unfold open. ext t.
    apply (bindd_respectful_fmapd T).
    intros w l' l'in. destruct l'.
    - reflexivity.
    - cbn. compare naturals n and w.
  Qed.

  (** ** Opening, followed by closing *)
  (**************************************************************************)
  Lemma close_open_local : forall x w l,
      l <> Fr x ->
      (close_loc x co⋆ open_leaf_loc (Fr x)) (w, l) = l.
  Proof.
    introv neq. cbn. unfold id. compare l to atom x.
    - contradiction.
    - unfold compose; cbn. now compare values x and a.
    - unfold compose; cbn.
      compare naturals n and w. compare values x and x.
      compare naturals (n - 1) and w.
  Qed.

  Theorem close_open : forall x t,
      ~ x ∈ free T t ->
      '[x] (t '(ret T (Fr x))) = t.
  Proof.
    introv fresh. compose near t on left.
    rewrite open_by_leaf_spec. unfold close.
    rewrite (dfun_fmapd2 _ T).
    apply (fmapd_respectful_id T).
    intros w l lin.
    assert (l <> Fr x).
    { rewrite neq_symmetry. apply (ind_implies_in T) in lin.
      eauto using (ninf_in_neq (T := T)). }
    now apply close_open_local.
  Qed.

  (** ** Opening and local closure *)
  (**************************************************************************)
  Lemma open_lc_gap_eq_1 : forall n t u,
      locally_closed T u ->
      locally_closed_gap T n t ->
      locally_closed_gap T (n - 1) (t '(u)).
  Proof.
    unfold locally_closed_gap.
    introv lcu lct Hin. rewrite ind_open_iff in Hin.
    destruct Hin as [n1 [n2 [l1 [h1 [h2 h3]]]]].
    destruct l1.
    - cbn in h2. rewrite (ind_ret_iff T) in h2.
      destruct h2; subst. cbn. trivial.
    - specialize (lct _ _ h1). cbn in h2. compare naturals n0 and n1.
      + rewrite (ind_ret_iff T) in h2; destruct h2; subst.
        cbn. unfold_monoid. lia.
      + specialize (lcu n2 l h2). unfold is_bound_or_free in *.
        destruct l; [trivial|]. unfold_monoid. lia.
      + rewrite (ind_ret_iff T) in h2. destruct h2; subst.
        unfold is_bound_or_free in *. unfold_lia.
  Qed.

  Lemma open_lc_gap_eq_2 : forall n t u,
      n > 0 ->
      locally_closed T u ->
      locally_closed_gap T (n - 1) (t '(u)) ->
      locally_closed_gap T n t.
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
          rewrite (ind_ret_iff T). now simpl_monoid. }
      + cbn. unfold_lia.
      + cbn. specialize (lct w (Bd (n0 - 1))).
        lapply lct.
        { cbn; unfold_lia. }
        { exists w (Ƶ : nat) (Bd n0).
          split; auto. cbn. compare naturals n0 and w.
          rewrite (ind_ret_iff T). now simpl_monoid. }
  Qed.

  Theorem open_lc_gap_eq_iff : forall n t u,
      n > 0 ->
      locally_closed T u ->
      locally_closed_gap T n t <->
      locally_closed_gap T (n - 1) (t '(u)).
  Proof.
    intros; intuition (eauto using open_lc_gap_eq_1, open_lc_gap_eq_2).
  Qed.

  Corollary open_lc_gap_eq_var : forall n t x,
      n > 0 ->
      locally_closed_gap T n t <->
      locally_closed_gap T (n - 1) (t '(ret T (Fr x))).
  Proof.
    intros. apply open_lc_gap_eq_iff. auto.
    intros w l hin. rewrite (ind_ret_iff T) in hin.
    destruct hin; subst. cbv. trivial.
  Qed.

  Corollary open_lc_gap_eq_iff_1 : forall t u,
      locally_closed T u ->
      locally_closed_gap T 1 t <->
      locally_closed T (t '(u)).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_iff; auto.
    reflexivity.
  Qed.

  Corollary open_lc_gap_eq_var_1 : forall t x,
      locally_closed_gap T 1 t <->
      locally_closed T (t '(ret T (Fr x))).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_var; auto.
    reflexivity.
  Qed.

End locally_nameless_metatheory.
