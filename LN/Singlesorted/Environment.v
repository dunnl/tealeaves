From Tealeaves Require Import
     Singlesorted.Classes.DecoratedTraversableModule
     LN.Atom LN.Leaf LN.AtomSet LN.AssocList.
     (*
LN.Singlesorted.Operations
LN.Singlesorted.Theory.
*)

Require Import Coq.Sorting.Permutation.

Import List.Notations.
Import LN.AtomSet.Notations.
Import LN.AssocList.Notations.
Import Applicative.Notations.
Import Sets.Notations.
Import DecoratedTraversableMonad.Notations.
Open Scope list_scope.
Open Scope set_scope.
Open Scope tealeaves_scope.

(** * D-T functor instance for <<alist>> *)
(******************************************************************************)
Section DecoratedTraversableFunctor_alist.

  Context
    `{Monoid W}.

  (** ** Traversable instance *)
  #[global] Instance Dist_alist : Dist (fun A => alist A)
    := Dist_compose.

  #[global] Instance Traversable_alist : TraversableFunctor (fun A => alist A)
    := Traversable_compose.

  (** ** Decorated instance *)
  #[global] Instance Decorate_alist :
    Decorate W (fun A => alist A)
    := Decorate_zero.

  #[global] Instance DecoratedFunctor_alist :
    DecoratedFunctor W (fun A => alist A)
    := DecoratedFunctor_zero.

  (** ** DTM instance *)
  #[global] Instance DecoratedTraversableFunctor_alist :
    DecoratedTraversableFunctor W (fun A => alist A).
  Proof.
    constructor.
    typeclasses eauto.
    typeclasses eauto.
    intros. ext l. induction l. unfold compose; cbn.
    - now rewrite (app_pure_natural G).
    - change (fun A => alist A) with (list ∘ prod atom).
      unfold compose.
      change (fun A => alist A) with (list ∘ prod atom).
      unfold_ops @Dist_alist @Dist_compose.
      unfold_ops @Fmap_alist @Fmap_compose.
      unfold_ops @Decorate_alist @Decorate_zero.
  Admitted.

End DecoratedTraversableFunctor_alist.

(** * DTM instance for <<alist>>-based environments *)
(******************************************************************************)
Section DecoratedTraversableMonad_env.

  Context
    `{DecoratedTraversableModule W F T}.

  Instance: Monoid W.
  inversion H. inversion dtmod_dec.
  inversion drmod_functor. auto.
  Qed.

  Local Notation "'env' A" := (alist (F A)) (at level 50, no associativity).

  Instance: DecoratedTraversableModule W ((list ∘ prod atom) ∘ F) T :=
    DecoratedTraversableModule_compose.

End DecoratedTraversableMonad_env.

(** * Rewriting principles *)
(******************************************************************************)

(** ** Rewriting principles for <<tolist>> *)
(******************************************************************************)
Section env_rewriting_tolist.

  Context
    `{DecoratedTraversableModule W F T}.

  Local Notation "'env' A" := (alist (F A)) (at level 50).

  Lemma tolist_env_nil : forall A,
      tolist (fun A => env A) (nil : env A) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma tolist_env_cons : forall (x : atom) A (t : F A) (e : env A),
      tolist (fun A => env A) ((x, t) :: e) =
      tolist F t ++ tolist ((list ∘ prod atom) ∘ F) e.
  Proof.
    intros. unfold_ops @Tolist_Traversable.
    unfold compose. unfold_ops @Fmap_compose.
    rewrite fmap_list_cons.
    unfold_ops @Dist_compose @Dist_alist.
    unfold compose; rewrite fmap_list_cons.
    rewrite dist_list_cons. cbn.
    unfold Dist_compose. unfold monoid_op, Monoid_op_app.
    compose near e on left. rewrite (fun_fmap_fmap list).
    unfold_ops @Fmap_alist @Fmap_compose.
  Admitted.

  Lemma tolist_env_one : forall (x : atom) A (t : F A),
      (tolist (fun A => env A) (x ~ t)) = tolist F t.
  Proof.
    intros. cbn. now rewrite (monoid_id_l).
  Qed.

  Lemma tolist_env_app : forall A (e1 e2 : env A),
      tolist (fun A => env A) (e1 ++ e2) =
      tolist (fun A => env A) e1 ++ tolist (fun A => env A) e2.
  Proof.
    intros. unfold_ops @Tolist_Traversable. unfold compose.
    unfold_ops @Fmap_compose.
  Admitted.

End env_rewriting_tolist.

(** ** Rewriting principles for LN operations *)
(******************************************************************************)
Section env_rewriting_ln.

  Context
    `{DecoratedTraversableModule nat (op := plus) (unit0 := 0) F T}.

  Local Notation "'env' A" := (alist (F A)) (at level 50).

  Import LN.Singlesorted.Operations.Notations.

  (** *** Rewriting lemmas for <<subst>> *)
  Lemma subst_nil : forall (x : atom) (t : T leaf),
      subst (fun A => env A) x t (nil : env leaf) = nil.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma subst_cons : forall (k : K) (x : atom) (t1 : F leaf) (t2 : T k leaf) (e : env leaf),
      ((x, t1) :: e) '{k | x ~> t2} = (x, t1 '{k | x ~> t2}) :: (e '{k | x ~> t2}).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_one : forall (k : K) (x y : atom) (t1 : F leaf) (t2 : T k leaf),
      (x ~ t1) '{k | y ~> t2} = x ~ t1 '{k | y ~> t2}.
  Proof.
    reflexivity.
  Qed.

  Lemma subst_app : forall (k : K) (x : atom) (t : T k leaf) (e1 e2 : env leaf),
      (e1 ++ e2) '{k | x ~> t} = (e1 '{k | x ~> t}) ++ (e2 '{k | x ~> t}).
  Proof.
    intros. unfold subst, bindk, mbind, Mbind_env.
    now rewrite envmap_app.
  Qed.

  Lemma subst_app_one_l : forall (k : K) (x : atom) (t1 : F leaf) (t2 : T k leaf) (e : env leaf),
      (x ~ t1 ++ e) '{k | x ~> t2} = x ~ t1 '{k | x ~> t2} ++ (e '{k | x ~> t2}).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_app_one_2 : forall (k : K) (x : atom) (t1 : F leaf) (t2 : T k leaf) (e : env leaf),
      (e ++ x ~ t1) '{k | x ~> t2} = (e '{k | x ~> t2}) ++ x ~ t1 '{k | x ~> t2}.
  Proof.
    intros. now rewrite subst_app.
  Qed.

  (** *** Rewriting lemmas for <<free>> *)
  Lemma free_nil : forall (k : K) (x : atom) (t : T k leaf),
      free (fun A => env A) k (nil : env leaf) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma free_one : forall (k : K) (x : atom) (t : F leaf),
      free (fun A => env A) k (x ~ t) = free F k t.
  Proof.
    intros. unfold free, tolistk, compose.
    now rewrite tolist_env_one.
  Qed.

  Lemma free_cons : forall (k : K) (x : atom) (t : F leaf) (e : env leaf),
      free (fun A => env A) k ((x, t) :: e) = free F k t ++ free (fun A => env A) k e.
  Proof.
    intros. unfold free. unfold tolistk, compose, tolist, Tolist_env.
    now rewrite List.bind_list_cons, filterk_app, List.bind_list_app.
  Qed.

  Lemma free_app : forall (k : K) (e1 e2 : env leaf),
      free (fun A => env A) k (e1 ++ e2) =
      free (fun A => env A) k e1 ++ free (fun A => env A) k e2.
  Proof.
    intros. unfold free, tolistk, tolist, Tolist_env, compose.
    now rewrite List.bind_list_app, filterk_app, List.bind_list_app.
  Qed.

  Theorem in_free_iff :
    forall (k : K) (Γ : env leaf) (x : atom),
      x ∈ free (fun A => env A) k Γ  <-> exists (t : F leaf), t ∈ range Γ /\ x ∈ free F k t.
  Proof.
    intros. rewrite (in_free_iff).
    setoid_rewrite (in_free_iff).
    rewrite (inm_env_iff).
    setoid_rewrite in_range_iff. split.
    - intros [y [t [? ?]]]. eauto.
    - intros [t [[y] ?]]. eauto.
  Qed.

  Theorem nin_free_iff :
    forall (k : K) (Γ : env leaf) (x : atom),
      ~ x ∈ free (fun A => env A) k Γ <-> forall (t : F leaf), t ∈ range Γ -> ~ x ∈ free F k t.
  Proof.
    intros. alist induction Γ.
    - cbn. split; auto.
    - rewrite free_app. rewrite List.in_list_app.
      rewrite free_one. setoid_rewrite range_app. setoid_rewrite range_one.
      setoid_rewrite List.in_list_app. setoid_rewrite List.in_list_one. split.
      + introv not_or. apply Decidable.not_or in not_or.
        destruct not_or as [not1 not2]. intros t [hyp | hyp].
        { subst. auto. }
        { apply IHΓ; auto. }
      + introv hyp. introv [contra | contra].
        contradict contra. apply hyp. now left.
        contradict contra. rewrite IHΓ. auto.
  Qed.

  (** *** Rewriting lemmas for <<freeset>> *)
  Open Scope set_scope.

  Lemma freeset_nil : forall (k : K) (x : atom) (t : T k leaf),
      freeset (fun A => env A) k (nil : env leaf) = ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma freeset_one : forall (k : K) (x : atom) (t : F leaf),
      freeset (fun A => env A) k (x ~ t) = freeset F k t.
  Proof.
    intros. unfold freeset. now rewrite free_one.
  Qed.

  Lemma freeset_cons : forall (k : K) (x : atom) (t : F leaf) (e : env leaf),
      freeset (fun A => env A) k ((x, t) :: e) [=]
              freeset F k t ∪ freeset (fun A => env A) k e.
  Proof.
    intros. unfold freeset. now rewrite free_cons, atoms_app.
  Qed.

  Lemma freeset_app : forall (k : K) (e1 e2 : env leaf),
      freeset (fun A => env A) k (e1 ++ e2) [=]
              freeset (fun A => env A) k e1 ∪ freeset (fun A => env A) k e2.
  Proof.
    intros. unfold freeset. now rewrite free_app, atoms_app.
  Qed.

End env_rewriting_lemmas.

(** ** Reasoning principles for environments *)
(******************************************************************************)
Section env_theorems.

  Context
    `{SyntaxModule W F T}.

  Local Notation "'env' A" := (alist (F A)) (at level 50).

  Local Open Scope set_scope.

  Theorem domset_subst : forall (e : env leaf) k x t,
      domset e [=] domset (e '{ k | x ~> t}).
  Proof.
    intros. induction e.
    - reflexivity.
    - destruct a as [y u]. rewrite (domset_cons).
      rewrite IHe. change_right ({{y}} ∪ domset (e '{ k | x ~> t})).
      reflexivity.
  Qed.

  Theorem uniq_subst : forall k (e : env leaf) x t,
      uniq e <-> uniq (e '{ k | x ~> t}).
  Proof.
    intros. unfold subst. unfold bindk, mbind, Mbind_env.
    now autorewrite with tea_rw_uniq.
  Qed.

  Theorem binds_subst_env : forall k (e : env leaf) x t y u,
      (y, u) ∈ (e '{k | x ~> t} : alist (F leaf)) <->
      exists u_inv : F leaf,
        (y, u_inv) ∈ (e : alist (F leaf))
        /\ u_inv '{k | x ~> t} = u.
  Proof.
    intros. cbn. unfold subst, bindk, mbind, Mbind_env.
    now rewrite in_envmap_iff.
  Qed.

  Corollary binds_subst_env_mono : forall k (e : env leaf) x t (y : atom) (u : F leaf),
      (y, u) ∈ (e : alist (F leaf)) ->
      (y, u '{k | x ~> t}) ∈ (e '{k | x ~> t} : list (atom * F leaf)).
  Proof.
    intros. rewrite binds_subst_env. eauto.
  Qed.

  Theorem in_range_subst : forall k (e : env leaf) x t (u : F leaf),
      u ∈ range (e '{k | x ~> t}) <->
      exists u_inv : F leaf,
        u_inv ∈ range (e : alist (F leaf))
        /\ u_inv '{k |  x ~> t} = u.
  Proof.
    intros. cbn. unfold subst, bindk, mbind, Mbind_env.
    rewrite in_range_iff. setoid_rewrite in_range_iff.
    setoid_rewrite in_envmap_iff. firstorder.
  Qed.

  Theorem in_freeset_iff : forall (k : K) (Γ : env leaf) (x : atom),
      x ∈@ freeset (fun A => env A) k Γ  <->
      exists (t : F leaf), t ∈ range Γ /\ x ∈@ freeset F k t.
  Proof.
    intros. rewrite <- free_iff_freeset.
    setoid_rewrite <- free_iff_freeset.
    apply in_free_iff.
  Qed.

  Theorem nin_freeset_iff :
    forall (k : K) (Γ : env leaf) (x : atom),
      ~ x ∈@ freeset (fun A => env A) k Γ  <-> forall (t : F leaf), t ∈ range Γ -> ~ x ∈@ freeset F k t.
  Proof.
    intros. setoid_rewrite <- free_iff_freeset.
    apply nin_free_iff.
  Qed.

End env_theorems.

(** ** Reasoning about <<scope>> *)
(******************************************************************************)
Definition scoped_env `{H : Index} F `{Tolist F} {A} :
  K -> F leaf -> alist A -> Prop := fun k t γ => scoped F k t (domset γ).

Section env_scope_theorems.

  (** TODO : This choice of <<nat>> is unnecessarily specific but required for
      using <<freeset_subst_upper_eq.>> *)

  Context
    `{SyntaxModule nat (monoid_op := plus) (monoid_unit := 0) F T}.

  Theorem perm_scoped : forall A (t : F leaf) (γ1 γ2 : alist A) (k : K),
      Permutation γ1 γ2 ->
      scoped_env F k t γ1 ->
      scoped_env F k t γ2.
  Proof.
    introv Hperm. unfold scoped_env, scoped. rewrite (perm_domset); eauto.
  Qed.

  Theorem perm_scoped_iff : forall A (γ1 γ2 : alist A) (k : K) (t : F leaf),
      Permutation γ1 γ2 ->
      scoped_env F k t γ1 <->
      scoped_env F k t γ2.
  Proof.
    intros. assert (Permutation γ2 γ1) by now symmetry.
    split; eauto using perm_scoped.
  Qed.

  Lemma weak_scoped_app_l : forall A k (t : F leaf) (γ1 γ2 : alist A),
      scoped_env F k t γ1 ->
      scoped_env F k t (γ1 ++ γ2).
  Proof.
    intros. unfold scoped_env, scoped in *.
    autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma weak_scoped_app_r : forall A k (t : F leaf) (γ1 γ2 : alist A),
      scoped_env F k t γ2 ->
      scoped_env F k t (γ1 ++ γ2).
  Proof.
    intros. unfold scoped_env, scoped in *.
    autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma stren_scoped : forall γ1 γ2 x t k,
      scoped_env F k t (γ1 ++ x ~ tt ++ γ2) ->
      ~ x ∈@ (freeset F k t) ->
      scoped_env F k t (γ1 ++ γ2).
  Proof.
    introv hyp hnotin. unfold scoped_env in *.
    (* todo : investigate why <<scoped>> needs to unfolded. *)
    unfold scoped in *. autorewrite with tea_rw_dom in *. fsetdec.
  Qed.

  Lemma sub_scoped : forall γ1 γ2 x (t1 : F leaf) k (t2 : T k leaf) ,
      scoped_env F k t1 (γ1 ++ x ~ tt ++ γ2) ->
      scoped_env (T k) k t2 (γ1 ++ γ2) ->
      scoped_env F k (subst F k x t2 t1) (γ1 ++ γ2).
  Proof.
    introv hyp1 hyp2. unfold scoped_env, scoped in *. autorewrite with tea_rw_dom in *.
    etransitivity. apply freeset_subst_upper_eq. fsetdec.
  Qed.

  Lemma sub_scoped_1 : forall γ x (t1 : F leaf) k (t2 : T k leaf) ,
      scoped_env F k t1 (γ ++ x ~ tt) ->
      scoped_env (T k) k t2 γ ->
      scoped_env F k (subst F k x t2 t1) γ.
  Proof.
    introv hyp1 hyp2. change_alist (γ ++ x ~ tt ++ []) in hyp1.
    change_alist (γ ++ []) in hyp2.
    change_alist (γ ++ []).
    eauto using sub_scoped.
  Qed.

End env_scope_theorems.
