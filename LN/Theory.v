(** This files contains metatheorems for the locally nameless variables
 that closely parallel those of LNgen. *)
From Tealeaves Require Import
     LN.Leaf LN.Atom LN.AtomSet LN.Operations
     Classes.DecoratedTraversableModule.

Import LN.AtomSet.Notations.
Import Operations.Notations.
Import DecoratedTraversableMonad.Notations.
#[local] Open Scope set_scope.
#[local] Open Scope tealeaves_scope.


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
    `{DecoratedTraversableModule nat F T
                                 (unit := Monoid_unit_zero)
                                 (op := Monoid_op_plus)}.

  Implicit Types (l : leaf) (n : nat) (t : F leaf) (x : atom).

  (** ** Reasoning principles for proving equalities *)
  (******************************************************************************)

  (** *** <<open>> *)
  (******************************************************************************)
  Lemma open_eq : forall t u1 u2,
      (forall w l, (w, l) ∈d t -> open_loc u1 (w, l) = open_loc u2 (w, l)) ->
      t '(u1) = t '(u2).
  Proof.
    intros. unfold open.
    now apply (SetlikeModule.subd_respectful F).
  Qed.

  Lemma open_id : forall t u,
      (forall w l, (w, l) ∈d t -> open_loc u (w, l) = ret T l) ->
      t '(u) = t.
  Proof.
    intros. unfold open.
    now apply (SetlikeModule.subd_respectful_id F).
  Qed.

  (** *** <<close>> *)
  (******************************************************************************)
  Lemma close_eq : forall t x y,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = close_loc y (w, l)) ->
      '[x] t = '[y] t.
  Proof.
    intros. unfold close.
    now apply (fmapd_respectful F).
  Qed.

  Lemma close_id : forall t x,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = l) ->
      '[x] t = t.
  Proof.
    intros. unfold close.
    now apply (fmapd_respectful_id F).
  Qed.

  (** *** <<subst>> *)
  (******************************************************************************)
  Lemma subst_eq : forall t x y u1 u2,
      (forall l, l ∈ t -> subst_loc x u1 l = subst_loc y u2 l) ->
      t '{x ~> u1} = t '{y ~> u2}.
  Proof.
    intros. unfold subst.
    now apply (SetlikeModule.sub_respectful F T).
  Qed.

  Lemma subst_id : forall t x u,
      (forall l, l ∈ t -> subst_loc x u l = ret T l) ->
      t '{x ~> u} = t.
  Proof.
    intros. unfold subst.
    now apply (SetlikeModule.sub_respectful_id F T).
  Qed.

  (** ** Occurrence analysis lemmas *)
  (******************************************************************************)

  (** *** <<open>> *)
  (******************************************************************************)
  Lemma ind_open_iff : forall l n u t,
      (n, l) ∈d t '(u) <-> exists l1 n1 n2,
        (n1, l1) ∈d t /\ (n2, l) ∈d open_loc u (n1, l1) /\ n = n1 ● n2.
  Proof.
    intros. unfold open.
    now rewrite (SetlikeModule.ind_subd_iff F).
  Qed.

  Lemma in_open_iff : forall l u t,
      l ∈ t '(u) <-> exists l1 n1,
        (n1, l1) ∈d t /\ l ∈ open_loc u (n1, l1).
  Proof.
    intros. unfold open.
    now rewrite (SetlikeModule.in_subd_iff F).
  Qed.

  (** *** <<close>> *)
  (******************************************************************************)
  Lemma ind_close_iff : forall l n x t,
      (n, l) ∈d '[x] t <-> exists l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite (ind_fmapd_iff F).
  Qed.

  Lemma in_close_iff : forall l x t,
      l ∈ '[x] t <-> exists n l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite (in_fmapd_iff F).
  Qed.

  (** *** <<subst>> *)
  (******************************************************************************)
  Lemma ind_subst_iff : forall n l u t x,
      (n, l) ∈d t '{x ~> u} <-> exists l1 n1 n2,
        (n1, l1) ∈d t /\ (n2, l) ∈d subst_loc x u l1 /\ n = n1 ● n2.
  Proof.
    intros. unfold subst.
    now rewrite (SetlikeModule.ind_sub_iff F).
  Qed.

  Lemma in_subst_iff : forall l u t x,
      l ∈ t '{x ~> u} <-> exists l1,
       l1 ∈ t /\ l ∈ subst_loc x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (SetlikeModule.in_sub_iff F T).
  Qed.

  (** ** Free variables *)
  (******************************************************************************)

  (** *** Specifications for [free] and [freeset] *)
  (******************************************************************************)
  Theorem in_free_iff : forall (t : F leaf) (x : atom),
      x ∈ free F t <-> Fr x ∈ t.
  Proof.
    intros. unfold free. rewrite (in_bind_iff list). split.
    - intros [l ?]. destruct l.
      + rewrite in_iff_in_list. cbn in *.
        cut (a = x). now intro; subst. tauto.
      + cbn in *. tauto.
    - exists (Fr x). rewrite <- (in_iff_in_list).
      cbn. tauto.
  Qed.

  Theorem in_free_iff_T : forall (t : T leaf) (x : atom),
      x ∈ free T t <-> Fr x ∈ t.
  Proof.
    intros. unfold free. rewrite (in_bind_iff list). split.
    - intros [l ?]. destruct l.
      + rewrite in_iff_in_list. cbn in *.
        cut (a = x). now intro; subst. tauto.
      + cbn in *. tauto.
    - exists (Fr x). rewrite <- (in_iff_in_list).
      cbn. tauto.
  Qed.

  Theorem free_iff_freeset : forall (t : F leaf) (x : atom),
      x ∈ free F t <-> x ∈@ freeset F t.
  Proof.
    intros. unfold freeset. rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  (** *** Opening *)
  (******************************************************************************)
  Lemma free_open_iff : forall u t x,
      x ∈ free F (t '(u)) <-> exists l1 w,
        (w, l1) ∈d t /\ x ∈ free T (open_loc u (w, l1)).
  Proof.
    intros. rewrite in_free_iff. setoid_rewrite (in_free_iff_T).
    now rewrite in_open_iff.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma free_close_iff : forall t x y,
      y ∈ free F ('[x] t) <-> exists w l1,
        (w, l1) ∈d t /\ close_loc x (w, l1) = Fr y.
  Proof.
    intros. rewrite in_free_iff.
    now rewrite in_close_iff.
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma free_subst_iff : forall u t x y,
      y ∈ free F (t '{x ~> u}) <-> exists l1,
        l1 ∈ t /\ y ∈ free T (subst_loc x u l1).
  Proof.
    intros. rewrite (in_free_iff). setoid_rewrite (in_free_iff_T).
    now rewrite (in_subst_iff).
  Qed.

End locally_nameless_basic_principles.

(** * Utilities for reasoning at the leaves *)
(******************************************************************************)
Section locally_nameless_utilities.

  Context
    `{DecoratedTraversableModule nat (unit := Monoid_unit_zero) (op := Monoid_op_plus) F T}.

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
  Lemma ninf_in_neq : forall x l (t : F leaf),
      ~ x ∈ free F t ->
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

Hint Rewrite @in_ret_iff @ind_ret_iff
     using typeclasses eauto : tea_local.

Hint Rewrite Fr_injective Fr_injective_not_iff Bd_neq_Fr : tea_local.
#[export] Hint Resolve Fr_injective_not : tea_local.

Hint Rewrite
     @subst_loc_eq (*@subst_in_ret*)
     using typeclasses eauto : tea_local.
Hint Rewrite
     @subst_loc_neq @subst_loc_b @subst_loc_fr_neq (*@subst_in_ret_neq*)
     using first [ typeclasses eauto | auto ] : tea_local.
Hint Rewrite
     @open_loc_lt @open_loc_gt
     using first [ typeclasses eauto | auto ] : tea_local.
Hint Rewrite
     @open_loc_eq @open_loc_atom
     using typeclasses eauto : tea_local.

Tactic Notation "simpl_local" := (autorewrite* with tea_local).

(** * Locally nameless metatheory *)
(******************************************************************************)
Section locally_nameless_metatheory.

  Context
    `{DecoratedTraversableModule nat (op:=plus) (unit := 0) F T}.

  (** Sometimes we need to specialize lemmas to the case <<F = T>>, so
      we register <<T>> as a module over itself. *)
  Existing Instance RightAction_Join.
  Instance: DecoratedTraversableModule nat (op:=plus) (unit := 0) T T.
  Proof.
    apply DecoratedTraversableModule_Monad.
    apply (dtmod_monad _ _ _).
  Qed.

  Lemma subst_in_ret : forall x l (u : T leaf),
      (ret T l) '{x ~> u} = subst_loc x u l.
  Proof.
    intros. unfold subst. compose near l on left.
    change_left ((bind T (subst_loc x u) ∘ η T) l).
    now rewrite (bind_comp_ret T).
  Qed.

  Implicit Types
           (l : leaf) (p : leaf)
           (x : atom) (t : F leaf)
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
      + exists l w (Ƶ : nat). rewrite monoid_id_l. splits; auto.
      + exists (Fr x) n1 n2. splits; auto.
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
      y ∈ free F (t '{x ~> u}) <->
      y ∈ free F t /\ y <> x \/ x ∈ free F t /\ y ∈ free T u.
  Proof.
    intros. repeat rewrite (in_free_iff).
    rewrite in_subst_iff'. now simpl_local.
  Qed.

  Corollary in_freeset_subst_iff : forall t u x y,
      y ∈@ freeset F (t '{x ~> u}) <->
      y ∈@ freeset F t /\ y <> x \/
      x ∈@ freeset F t /\ y ∈@ freeset T u.
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
      y ∈ free F (t '{x ~> u}) ->
      (y ∈ free F t /\ y <> x) \/ y ∈ free T u.
  Proof.
    introv. rewrite ?(in_free_iff). rewrite in_subst_iff'.
    rewrite Fr_injective_not_iff. tauto.
  Qed.

  Corollary freeset_subst_upper : forall t u x,
      freeset F (t '{x ~> u}) ⊆
              (freeset F t \\ {{x}} ∪ freeset T u).
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
      y ∈ free F t -> y <> x ->
      y ∈ free F (t '{x ~> u}).
  Proof.
    setoid_rewrite in_free_iff. intros.
    apply in_subst_lower; now simpl_local.
  Qed.

  Corollary freeset_subst_lower : forall t (u : T leaf) x,
      freeset F t \\ {{ x }} ⊆ freeset F (t '{x ~> u}).
  Proof.
    introv. intro a.
    rewrite AtomSet.diff_spec, AtomSet.singleton_spec.
    do 2 rewrite <- (free_iff_freeset).
    intros [? ?]. now apply in_free_subst_lower.
  Qed.

  Corollary scoped_subst_eq : forall t (u : T leaf) x γ1 γ2,
      scoped F t γ1 ->
      scoped T u γ2 ->
      scoped F (t '{x ~> u}) (γ1 \\ {{x}} ∪ γ2).
  Proof.
    introv St Su. unfold scoped in *.
    etransitivity. apply freeset_subst_upper. fsetdec.
  Qed.

  (** ** Substitution of fresh variables *)
  (******************************************************************************)
  Theorem subst_fresh : forall t x u,
      ~ x ∈ free F t ->
      t '{x ~> u} = t.
  Proof.
    intros. apply subst_id. intros.
    assert (Fr x <> l). eapply (@ninf_in_neq F); eauto.
    now simpl_local.
  Qed.

  Corollary subst_fresh_set : forall t x u,
      ~ x ∈@ freeset F t ->
      t '{x ~> u} = t.
  Proof.
    setoid_rewrite <- free_iff_freeset. apply subst_fresh.
  Qed.

  Theorem subst_fresh_t : forall (t : T leaf) x u,
      ~ x ∈ free T t ->
      t '{x ~> u} = t.
  Proof.
    intros. apply subst_id. intros.
    assert (Fr x <> l) by eauto using (@ninf_in_neq T).
    now simpl_local.
  Qed.

  Corollary subst_fresh_set_t : forall (t : T leaf) x u,
      ~ x ∈@ freeset T t ->
      t '{x ~> u} = t.
  Proof.
    setoid_rewrite <- free_iff_freeset. apply subst_fresh_t.
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
      + rewrite subst_in_ret, subst_loc_eq, subst_fresh_t...
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
    rewrite 2(sub_sub F T).
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
    rewrite subst_fresh_t; auto.
  Qed.

  (** ** Local closure is preserved by substitution *)
  (******************************************************************************)
  Theorem subst_lc : forall u t x,
      locally_closed F t ->
      locally_closed T u ->
      locally_closed F (subst F x u t).
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
    rewrite (subd_fmapd F).
    symmetry. apply (subd_respectful_sub F).
    symmetry. apply subst_spec_local.
  Qed.

  (** ** Substitution when <<u>> is a leaf **)
  (******************************************************************************)
  Definition subst_loc_leaf x (u : leaf) : leaf -> leaf :=
    fun l => match l with
          | Fr y => if x == y then u else Fr y
          | Bd n => Bd n
          end.

  Theorem subst_by_leaf_spec : forall x l,
      subst F x (ret T l) = fmap F (subst_loc_leaf x l).
  Proof.
    intros. unfold subst. ext t.
    apply (sub_respectful_fmap F T).
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
      inverts heq. apply (in_of_ind F) in lin. tauto.
    - cbn in heq. compare_nats_args ln w; discriminate.
  Qed.

  Lemma in_free_close_iff_loc2 : forall t x y,
      x <> y ->
      Fr y ∈ t ->
      exists w l, (w, l) ∈d t /\ close_loc x (w, l) = Fr y.
  Proof.
    introv neq yin. rewrite (ind_of_in F) in yin. destruct yin as [w yin].
    exists w. exists (Fr y). cbn. compare values x and y.
  Qed.

  Theorem in_free_close_iff : forall t x y,
      y ∈ free F ('[x] t) <-> y ∈ free F t /\ x <> y.
  Proof.
    introv. rewrite (free_close_iff).
    rewrite (in_free_iff). split.
    - introv [? [? [? ?] ] ]. eauto using in_free_close_iff_loc1.
    - intros [? ?]. eauto using in_free_close_iff_loc2.
  Qed.

  Corollary in_free_close_iff1 : forall t x y,
      y <> x ->
      y ∈ free F ('[x] t) <-> y ∈ free F t.
  Proof.
    intros. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary freeset_close : forall t x,
      freeset F ('[x] t) [=] freeset F t \\ {{ x }}.
  Proof.
    introv. intro a. rewrite AtomSet.diff_spec.
    rewrite <- 2(free_iff_freeset). rewrite in_free_close_iff.
    rewrite AtomSet.singleton_spec. intuition.
  Qed.

  Corollary nin_free_close : forall t x,
      ~ (x ∈ free F ('[x] t)).
  Proof.
    introv. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary nin_freeset_close : forall t x,
      ~ (x ∈@ freeset F ('[x] t)).
  Proof.
    introv. rewrite <- free_iff_freeset. apply nin_free_close.
  Qed.

  (** ** Variable closing and local closure *)
  (******************************************************************************)
  Theorem close_lc_eq : forall t x,
      locally_closed F t ->
      locally_closed_gap F 1 (close F x t).
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
      (l = Fr x /\ x ∈ free F t) \/
      x ∈ free T u.
  Proof with auto.
    introv lin xin. rewrite in_free_iff_T in xin.
    rewrite 2(in_free_iff). destruct l as [y | n].
    - left. autorewrite with tea_local in xin. inverts xin...
    - right. cbn in xin. compare naturals n and w.
      { contradict xin. simpl_local. intuition. }
      { assumption. }
      { contradict xin. simpl_local. intuition. }
  Qed.

  Theorem free_open_upper : forall t (u : T leaf) x,
      x ∈ free F (t '(u)) ->
      x ∈ free F t \/ x ∈ free T u.
  Proof.
    introv xin.
    rewrite free_open_iff in xin.
    destruct xin as [l [w [hin ?]]].
    apply (in_of_ind F) in hin.
    enough ((l = Fr x /\ x ∈ free F t) \/ x ∈ free T u) by intuition.
    eauto using free_open_upper_local.
  Qed.

  Corollary freeset_open_upper : forall t (u : T leaf),
      freeset F (t '(u)) ⊆ freeset F t ∪ freeset T u.
  Proof.
    intros. intro a. rewrite AtomSet.union_spec.
    repeat rewrite <- (free_iff_freeset).
    auto using free_open_upper.
  Qed.

  Theorem free_open_lower : forall t u x,
      x ∈ free F t ->
      x ∈ free F (t '(u)).
  Proof.
    introv xin.
    rewrite (in_free_iff) in xin.
    rewrite (ind_of_in F) in xin.
    destruct xin as [w xin].
    rewrite (free_open_iff).
    setoid_rewrite (in_free_iff).
    exists (Fr x) w. now autorewrite with tea_local.
  Qed.

  Corollary freeset_open_lower : forall t u,
      freeset F t ⊆ freeset F (t '(u)).
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
      locally_closed F t ->
      t '(u) = t.
  Proof.
    introv lc. apply open_id. introv lin.
    specialize (lc _ _ lin).
    destruct l; auto using open_lc_local.
  Qed.

  (** ** Opening followed by substitution *)
  (**************************************************************************)
  Lemma subst_open_local : forall u1 u2 x,
      locally_closed T u2 ->
      subst T x u2 ∘ open_loc u1 =
      open_loc (u1 '{x ~> u2}) ⋆d (subst_loc x u2 ∘ extract (prod nat)).
  Proof.
    introv lcu2. ext [w l]. rewrite <- (kcomposed_equiv). unfold kcomposed_alt.
    unfold prepromote, compose; cbn. compare l to atom x.
    - rewrite subst_in_ret. cbn.
      compare values x and x. symmetry.
      apply (bindd_respectful_id T).
      intros. destruct a.
      + reflexivity.
      + unfold locally_closed, locally_closed_gap, is_bound_or_free in lcu2.
        compare naturals n and (w ● w0).
        { specialize (lcu2 _ _ H9). cbn in lcu2. unfold_lia. }
        { specialize (lcu2 _ _ H9). cbn in lcu2. unfold_lia. }
    - rewrite subst_in_ret. cbn. compare values x and a.
      compose near (Fr a). now rewrite (bindd_comp_ret T).
    - compare naturals n and w; cbn.
      + rewrite subst_in_ret. compose near (Bd n) on right.
        rewrite (bindd_comp_ret T); unfold compose.
        rewrite monoid_id_l. compare naturals n and w.
      + compose near (Bd w) on right.
        rewrite (bindd_comp_ret T). unfold compose.
        rewrite monoid_id_l. compare naturals w and w.
      + rewrite subst_in_ret.
        compose near (Bd n) on right.
        rewrite (bindd_comp_ret T). unfold compose.
        rewrite monoid_id_l. compare naturals n and w.
  Qed.

  Theorem subst_open :  forall u1 u2 t x,
      locally_closed T u2 ->
      t '(u1) '{x ~> u2} =
      t '{x ~> u2} '(u1 '{x ~> u2}).
  Proof.
    introv lc. compose near t.
    unfold open, subst at 1 3.
    rewrite (sub_subd F).
    rewrite (subd_sub F).
    fequal. unfold kcompose.
    #[local] Set Keyed Unification.
    rewrite subst_open_local; auto.
    #[local] Unset Keyed Unification.
    unfold kcomposed.
    reassociate <- near (dec T).
    now rewrite <- (fmap_to_cobind (prod nat)).
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
      ~ x ∈@ freeset F t ->
      t '(u) = t '(ret T (Fr x)) '{x ~> u}.
  Proof.
    introv fresh. compose near t on right.
    unfold subst, open.
    rewrite (sub_subd F).
    apply (subd_respectful F). introv hin.
    assert (a <> Fr x).
    { apply (in_of_ind F) in hin.
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
      open_loc (ret T (Fr y)) ⋆d (subst_loc x u ∘ extract (prod nat)).
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
    rewrite (sub_subd F), (subd_sub F).
    fequal.
    change_left (subst T x u ∘ open_loc (ret T (Fr y))).
    #[local] Set Keyed Unification.
    rewrite subst_open_var_loc; auto.
    #[local] Unset Keyed Unification.
    unfold kcomposed.
    reassociate <- near (dec T).
    now rewrite <- (fmap_to_cobind (prod nat)).
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
    rewrite (subd_fmapd F).
    apply (subd_respectful_id F); intros.
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
      open F (ret T l) = fmapd F (open_leaf_loc l).
  Proof.
    intros. unfold open. ext t.
    apply (subd_respectful_fmapd F).
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
      ~ x ∈ free F t ->
      '[x] (t '(ret T (Fr x))) = t.
  Proof.
    introv fresh. compose near t on left.
    rewrite open_by_leaf_spec. unfold close.
    rewrite (fmapd_fmapd F).
    apply (fmapd_respectful_id F).
    intros w l lin.
    assert (l <> Fr x).
    { rewrite neq_symmetry. apply (in_of_ind F) in lin.
      eauto using (ninf_in_neq (F := F)). }
    auto using close_open_local.
  Qed.

  (** ** Opening and local closure *)
  (**************************************************************************)
  Lemma open_lc_gap_eq_1 : forall n t u,
      locally_closed T u ->
      locally_closed_gap F n t ->
      locally_closed_gap F(n - 1) (t '(u)).
  Proof.
    unfold locally_closed_gap.
    introv lcu lct Hin. rewrite ind_open_iff in Hin.
    destruct Hin as [l1 [n1 [n2 [h1 [h2 h3]]]]].
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
      locally_closed_gap F (n - 1) (t '(u)) ->
      locally_closed_gap F n t.
  Proof.
    unfold locally_closed_gap.
    introv ngt lcu lct Hin. setoid_rewrite (ind_open_iff) in lct.
    destruct l.
    - cbv. trivial.
    - compare naturals n0 and w.
      + specialize (lct w (Bd n0)).
        lapply lct.
        { cbn; unfold_lia. }
        { exists (Bd n0) w (Ƶ : nat).
          split; auto. cbn. compare naturals n0 and w.
          rewrite (ind_ret_iff T). now simpl_monoid. }
      + cbn. unfold_lia.
      + cbn. specialize (lct w (Bd (n0 - 1))).
        lapply lct.
        { cbn; unfold_lia. }
        { exists (Bd n0) w (Ƶ : nat).
          split; auto. cbn. compare naturals n0 and w.
          rewrite (ind_ret_iff T). now simpl_monoid. }
  Qed.

  Theorem open_lc_gap_eq_iff : forall n t u,
      n > 0 ->
      locally_closed T u ->
      locally_closed_gap F n t <->
      locally_closed_gap F (n - 1) (t '(u)).
  Proof.
    intros; intuition (eauto using open_lc_gap_eq_1, open_lc_gap_eq_2).
  Qed.

  Corollary open_lc_gap_eq_var : forall n t x,
      n > 0 ->
      locally_closed_gap F n t <->
      locally_closed_gap F (n - 1) (t '(ret T (Fr x))).
  Proof.
    intros. apply open_lc_gap_eq_iff. auto.
    intros w l hin. rewrite (ind_ret_iff T) in hin.
    destruct hin; subst. cbv. trivial.
  Qed.

  Corollary open_lc_gap_eq_iff_1 : forall t u,
      locally_closed T u ->
      locally_closed_gap F 1 t <->
      locally_closed F (t '(u)).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_iff; auto.
    reflexivity.
  Qed.

  Corollary open_lc_gap_eq_var_1 : forall t x,
      locally_closed_gap F 1 t <->
      locally_closed F (t '(ret T (Fr x))).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_var; auto.
    reflexivity.
  Qed.

End locally_nameless_metatheory.
