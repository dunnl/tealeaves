From Tealeaves Require Import
  Theory.Algebraic.DT.Monad
  Traversable.Functor.Instances
  LN.Atom LN.Leaf LN.AtomSet LN.AssocList
  LN.Operations LN.Theory.

Require Import Coq.Sorting.Permutation.

Import List.ListNotations.
Import LN.AtomSet.Notations.
Import LN.AssocList.Notations.
Import Applicative.Notations.
Import Sets.Notations.
Import Applicative.Notations.
Open Scope list_scope.
Open Scope set_scope.
Open Scope tealeaves_scope.

About scoped.

(*
Definition scoped_env F `{Fmap F} `{Dist F} {A} :
  F leaf -> alist A -> Prop := fun t γ => scoped F t (domset γ).
*)

#[local] Generalizable Variables W.

(** * DTM instance for <<alist>>-based environments *)
(******************************************************************************)
Section DecoratedTraversableMonad_env.

  Context
    `{DecoratedTraversableModule W F T}
    `{! Monoid W}.

  Instance: DecoratedTraversableModule W ((list ∘ prod atom) ∘ F) T :=
    DecoratedTraversableModule_compose.

End DecoratedTraversableMonad_env.

(** * Rewriting principles *)
(******************************************************************************)

Section env_rewriting_tolist.

  Context
    `{DecoratedTraversableModule nat (op := plus) (unit := 0) F T}.

  Definition env := ((list ∘ prod atom) ∘ F).

  Instance: DecoratedTraversableModule nat env T :=
    DecoratedTraversableModule_compose.

  (** ** Rewriting principles for <<dist>> *)
  (******************************************************************************)
  Section dist_laws.

    Context `{Applicative G}.

    Lemma dist_env_spec : forall A (e : env (G A)),
        dist env G e = dist list G (fmap list (dist (prod atom ∘ F) G) e).
    Proof.
      intros. unfold dist at 1, Dist_compose.
      unfold dist at 1, Dist_alist, Dist_compose.
      reassociate -> on left.
      Set Keyed Unification.
      now rewrite (fun_fmap_fmap list).
      Unset Keyed Unification.
    Qed.

    Lemma dist_env_nil : forall A,
        dist env G (nil : env (G A)) = pure G nil.
    Proof.
      reflexivity.
    Qed.

    Lemma dist_env_cons : forall A (x : atom) (t : F (G A)) (xs : env (G A)),
        dist env G ((x, t) :: xs) =
        pure G cons <⋆> (δ (prod atom ∘ F) G (x, t)) <⋆> (dist env G xs).
    Proof.
      reflexivity.
    Qed.

    Lemma dist_env_one : forall A (x : atom) (t : F (G A)),
        dist env G (x ~ t) = pure G (η list) <⋆> dist (prod atom) G (x, dist F G t).
    Proof.
      intros. change (x ~ t) with ((x, t) :: nil).
      rewrite dist_env_cons. rewrite dist_env_nil.
      do 2 rewrite <- fmap_to_ap.
      rewrite ap3. rewrite ap5.
      reflexivity.
    Qed.

    Lemma dist_env_app : forall A (xs ys : env (G A)),
        dist env G (xs ++ ys) =
        pure G (app (A := atom * F A)) <⋆> dist env G xs <⋆> dist env G ys.
    Proof.
      intros. repeat rewrite dist_env_spec.
      now simpl_list.
    Qed.

  End dist_laws.

  (** ** Rewriting principles for <<fmap>> *)
  (******************************************************************************)
  Lemma fmap_env_nil : forall `(f : A -> B),
      fmap env f (nil : env A) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_env_cons : forall `(f : A -> B) (x : atom) (t : F A) (xs : env A),
      fmap env f ((x, t) :: xs) = (x, fmap F f t) :: fmap env f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_env_one : forall `(f : A -> B) (x : atom) (t : F A),
      fmap env f (x ~ t) = (x ~ fmap F f t).
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_env_app : forall `(f : A -> B) (xs ys : env A),
      fmap env f (xs ++ ys) = fmap env f xs ++ fmap env f ys.
  Proof.
    intros. change (fmap env f) with (fmap list (fmap (prod atom ∘ F) f)).
    now simpl_list.
  Qed.

  (** ** Rewriting principles for <<sub>> *)
  (******************************************************************************)
  Lemma sub_env_spec : forall `(f : A -> T B) (e : env A),
      sub env f e = fmap list (fmap (prod atom) (sub F f)) e.
  Proof.
    intros. unfold sub at 1, Sub_RightAction.
    change (fmap env f) with (fmap list (fmap (prod atom ∘ F) f)).
    Set Keyed Unification.
    rewrite (fun_fmap_fmap list).
    rewrite (fun_fmap_fmap (prod atom)).
    reflexivity.
    Unset Keyed Unification.
  Qed.

  Lemma sub_env_nil : forall `(f : A -> T B),
      sub env f (nil : env A) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma sub_env_cons : forall `(f : A -> T B) (x : atom) (t : F A) (xs : env A),
      sub env f ((x, t) :: xs) = (x, sub F f t) :: sub env f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma sub_env_one : forall `(f : A -> T B) (x : atom) (t : F A),
      sub env f (x ~ t) = (x ~ sub F f t).
  Proof.
    reflexivity.
  Qed.

  Lemma sub_env_app : forall `(f : A -> T B) (xs ys : env A),
      sub env f (xs ++ ys) = sub env f xs ++ sub env f ys.
  Proof.
    intros. rewrite 3(sub_env_spec).
    now simpl_list.
  Qed.

  (** ** Rewriting principles for <<tolist>> *)
  (******************************************************************************)
  Lemma tolist_env_nil : forall A,
      tolist env (nil : env A) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma tolist_env_cons : forall (x : atom) A (t : F A) (e : env A),
      tolist env ((x, t) :: e) =
      tolist F t ++ tolist env e.
  Proof.
    intros. unfold_ops @Tolist_Traversable.
    change (fmap env ?f) with (fmap list (fmap (prod atom ∘ F) f)).
    unfold compose. now rewrite fmap_list_cons.
  Qed.

  Lemma tolist_env_one : forall (x : atom) A (t : F A),
      (tolist env (x ~ t)) = tolist F t.
  Proof.
    intros. cbn. now rewrite (monoid_id_l).
  Qed.

  Lemma tolist_env_app : forall A (e1 e2 : env A),
      tolist env (e1 ++ e2) =
      tolist env e1 ++ tolist env e2.
  Proof.
    intros. unfold_ops @Tolist_Traversable. unfold compose.
    rewrite fmap_env_app.
    now rewrite (dist_env_app).
  Qed.

  Lemma tolist_env_spec : forall A (e : env A),
      tolist env e = join list (fmap list (tolist F ∘ snd) e).
  Proof.
    intros. induction e.
    - reflexivity.
    - simpl_list. rewrite <- IHe.
      destruct a.
      now rewrite tolist_env_cons.
  Qed.

  (** ** Rewriting principles for <<∈>> *)
  (******************************************************************************)
  Lemma in_env_nil : forall A (a : A),
      a ∈ (nil : env A) = False.
  Proof.
    reflexivity.
  Qed.

  Lemma in_env_cons : forall A (a : A) (x : atom) (t : F A) (e : env A),
      a ∈ ((x, t) :: e : env A) <->
      a ∈ t \/ a ∈ e.
  Proof.
    intros. unfold toset, Toset_Tolist.
    unfold compose. rewrite tolist_env_cons.
    simpl_list; simpl_set. easy.
  Qed.

  Lemma in_env_one : forall (x : atom) A (a : A) (t : F A),
      a ∈ (x ~ t : env A) = a ∈ t.
  Proof.
    intros. cbn. now rewrite (monoid_id_l).
  Qed.

  Lemma in_env_app : forall A (a : A) (e1 e2 : env A),
      a ∈ (e1 ++ e2 : env A) <->
      a ∈ e1 \/ a ∈ e2.
  Proof.
    intros. unfold toset, Toset_Tolist.
    unfold compose. rewrite tolist_env_app.
    now simpl_list; simpl_set.
  Qed.

  Lemma in_env_spec : forall A (a : A) (e : env A),
      a ∈ (e : env A) <-> exists (x : atom) (t : F A), (x, t) ∈ (e : list (prod atom (F A))) /\ a ∈ t.
  Proof.
    intros. unfold toset at 1, Toset_Tolist.
    split.
    - unfold compose. induction e.
      + intro hyp. inversion hyp.
      + intro hyp. destruct a0 as [x t]. rewrite tolist_env_cons in hyp.
        rewrite in_list_app in hyp. destruct hyp as [hyp | hyp].
        { exists x, t. split. now left. auto. }
        { specialize (IHe hyp). destruct IHe as [x' [t' rest]].
          exists x', t'. split. now right. easy. }
    - intros [x [t [hyp1 hyp2]]]. unfold compose.
      rewrite <- in_iff_in_list. induction e.
      + inversion hyp1.
      + rewrite in_list_cons in hyp1. destruct hyp1 as [hyp1|hyp1].
        { subst. rewrite in_env_cons. auto. }
        { destruct a0 as [x' t'].
          rewrite in_env_cons. right. auto. }
  Qed.

  Import LN.Operations.Notations.

  (** *** Rewriting lemmas for <<subst>> *)
  (******************************************************************************)
  Lemma subst_env_nil : forall (x : atom) (t : T leaf),
       ([] : env leaf) '{x ~> t} = [].
  Proof.
    intros. reflexivity.
  Qed.

  Lemma subst_env_cons : forall (x y : atom) (t1 : F leaf) (t2 : T leaf) (e : env leaf),
      ((x, t1) :: e : env leaf) '{y ~> t2} =
      (x, t1 '{y ~> t2}) :: e '{y ~> t2}.
  Proof.
    reflexivity.
  Qed.

  Lemma subst_env_one : forall (x y : atom) (t1 : F leaf) (t2 : T leaf),
      (x ~ t1 : env leaf) '{y ~> t2} = (x ~ t1 '{y ~> t2}).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_env_app : forall (x : atom) (t : T leaf) (e1 e2 : env leaf),
      (e1 ++ e2 : env leaf) '{x ~> t} =
      e1 '{x ~> t} ++ e2 '{x ~> t}.
  Proof.
    intros. unfold subst. now rewrite sub_env_app.
  Qed.

  (** *** Rewriting lemmas for <<free>> *)
  (******************************************************************************)
  Lemma free_nil : forall (x : atom) (t : T leaf),
      free env (nil : env leaf) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma free_one : forall (x : atom) (t : F leaf),
      free env (x ~ t) = free F t.
  Proof.
    intros. unfold free. now rewrite tolist_env_one.
  Qed.

  Lemma free_cons : forall (x : atom) (t : F leaf) (e : env leaf),
      free env ((x, t) :: e) = free F t ++ free env e.
  Proof.
    intros. unfold free. rewrite tolist_env_cons.
    now simpl_list.
  Qed.

  Lemma free_app : forall (e1 e2 : env leaf),
      free env (e1 ++ e2) =
      free env e1 ++ free env e2.
  Proof.
    intros. unfold free. rewrite tolist_env_app.
    now simpl_list.
  Qed.

  (** *** Rewriting lemmas for <<∈ free>> *)
  (******************************************************************************)
  Theorem in_free_iff :
    forall (Γ : env leaf) (x : atom),
      x ∈ free env Γ  <-> exists (t : F leaf), t ∈ range Γ /\ x ∈ free F t.
  Proof.
    intros. rewrite (in_free_iff).
    setoid_rewrite (in_free_iff).
    rewrite (in_env_spec).
    setoid_rewrite in_range_iff. split.
    - intros [y [t [? ?]]]. eauto.
    - intros [t [[y] ?]]. eauto.
  Qed.

  Theorem nin_free_iff :
    forall (Γ : env leaf) (x : atom),
      ~ x ∈ free env Γ <-> forall (t : F leaf), t ∈ range Γ -> ~ x ∈ free F t.
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

  Theorem domset_subst : forall (e : env leaf) x t,
      domset e [=] domset (e '{x ~> t}).
  Proof.
    intros. induction e.
    - reflexivity.
    - destruct a as [y u]. rewrite (domset_cons).
      rewrite IHe. rewrite (subst_env_cons).
      rewrite domset_cons.
      reflexivity.
  Qed.

  Theorem uniq_subst : forall (e : env leaf) x t,
      uniq e <-> uniq (e '{x ~> t}).
  Proof.
    intros. unfold subst.
    rewrite sub_env_spec.
    change (fmap list (fmap (prod atom) ?f)) with (fmap (list ∘ prod atom) f).
    now rewrite uniq_fmap_iff.
  Qed.

  Theorem binds_subst_env : forall (e : env leaf) x t y u,
      (y, u) ∈ (e '{x ~> t} : list (atom * F leaf)) <->
      exists u_inv : F leaf,
        (y, u_inv) ∈ (e : list (atom * F leaf))
        /\ u_inv '{x ~> t} = u.
  Proof.
    intros. cbn. unfold subst.
    rewrite sub_env_spec.
    change (fmap list (fmap (prod atom) ?f)) with (fmap (list ∘ prod atom) f).
    now (rewrite in_envmap_iff).
  Qed.

  Corollary binds_subst_env_mono : forall (e : env leaf) x t (y : atom) (u : F leaf),
      (y, u) ∈ (e : list (atom * F leaf)) ->
      (y, u '{x ~> t}) ∈ (e '{x ~> t} : list (atom * F leaf)).
  Proof.
    intros. rewrite binds_subst_env. eauto.
  Qed.

  Theorem in_range_subst : forall (e : env leaf) x t (u : F leaf),
      u ∈ range (e '{x ~> t}) <->
      exists u_inv : F leaf,
        u_inv ∈ range (e : list (atom * F leaf))
        /\ u_inv '{x ~> t} = u.
  Proof.
    intros. cbn. unfold subst. rewrite sub_env_spec.
    rewrite in_range_iff. setoid_rewrite in_range_iff.
    setoid_rewrite in_envmap_iff. split.
    - intros. preprocess. eauto.
    - intros. preprocess. eauto.
  Qed.

  Theorem in_freeset_iff : forall (Γ : env leaf) (x : atom),
      x ∈@ freeset env Γ  <->
      exists (t : F leaf), t ∈ range Γ /\ x ∈@ freeset F t.
  Proof.
    intros. rewrite <- free_iff_freeset.
    setoid_rewrite <- free_iff_freeset.
    apply in_free_iff.
  Qed.

  Theorem nin_freeset_iff :
    forall (Γ : env leaf) (x : atom),
      ~ x ∈@ freeset env Γ  <-> forall (t : F leaf), t ∈ range Γ -> ~ x ∈@ freeset F t.
  Proof.
    intros. setoid_rewrite <- free_iff_freeset.
    apply nin_free_iff.
  Qed.

  Theorem perm_scoped : forall A (t : F leaf) (γ1 γ2 : alist A),
      Permutation γ1 γ2 ->
      scoped_env F t γ1 ->
      scoped_env F t γ2.
  Proof.
    introv Hperm. unfold scoped_env, scoped. rewrite (perm_domset); eauto.
  Qed.

  Theorem perm_scoped_iff : forall A (γ1 γ2 : alist A) (t : F leaf),
      Permutation γ1 γ2 ->
      scoped_env F t γ1 <->
      scoped_env F t γ2.
  Proof.
    intros. assert (Permutation γ2 γ1) by now symmetry.
    split; eauto using perm_scoped.
  Qed.

  Lemma weak_scoped_app_l : forall A (t : F leaf) (γ1 γ2 : alist A),
      scoped_env F t γ1 ->
      scoped_env F t (γ1 ++ γ2).
  Proof.
    intros. unfold scoped_env, scoped in *.
    autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma weak_scoped_app_r : forall A (t : F leaf) (γ1 γ2 : alist A),
      scoped_env F t γ2 ->
      scoped_env F t (γ1 ++ γ2).
  Proof.
    intros. unfold scoped_env, scoped in *.
    autorewrite with tea_rw_dom. fsetdec.
  Qed.

  Lemma stren_scoped : forall γ1 γ2 x t,
      scoped_env F t (γ1 ++ x ~ tt ++ γ2) ->
      ~ x ∈@ (freeset F t) ->
      scoped_env F t (γ1 ++ γ2).
  Proof.
    introv hyp hnotin. unfold scoped_env in *.
    (* todo : investigate why <<scoped>> needs to unfolded. *)
    unfold scoped in *. autorewrite with tea_rw_dom in *. fsetdec.
  Qed.

  Lemma sub_scoped : forall γ1 γ2 x (t1 : F leaf) (t2 : T leaf) ,
      scoped_env F t1 (γ1 ++ x ~ tt ++ γ2) ->
      scoped_env T t2 (γ1 ++ γ2) ->
      scoped_env F (subst F x t2 t1) (γ1 ++ γ2).
  Proof.
    introv hyp1 hyp2. unfold scoped_env, scoped in *. autorewrite with tea_rw_dom in *.
    etransitivity. apply freeset_subst_upper. fsetdec.
  Qed.

  Lemma sub_scoped_1 : forall γ x (t1 : F leaf) (t2 : T leaf) ,
      scoped_env F t1 (γ ++ x ~ tt) ->
      scoped_env T t2 γ ->
      scoped_env F (subst F x t2 t1) γ.
  Proof.
    introv hyp1 hyp2. change_alist (γ ++ x ~ tt ++ []) in hyp1.
    change_alist (γ ++ []) in hyp2.
    change_alist (γ ++ []).
    eauto using sub_scoped.
  Qed.

End env_rewriting_tolist.
