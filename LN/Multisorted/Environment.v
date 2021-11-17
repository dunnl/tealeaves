From Tealeaves Require Import
     LN.Atom LN.AtomSet LN.AssocList
     LN.Multisorted.Operations
     LN.Multisorted.Theory.

Require Import Tealeaves.Syntax.
Require Import Tealeaves.Multisorted.Syntax.
Require Import Tealeaves.Multisorted.Listable.

Require Import Coq.Sorting.Permutation.

Import LN.AtomSet.Notations.
Open Scope set_scope.
Import Tealeaves.Syntax.Notations.
Open Scope tealeaves_scope.
Import Multisorted.Syntax.Notations.
Open Scope tealeaves_multi_scope.
Import LN.Multisorted.Operations.Notations.
Import LN.AssocList.Notations.

(** * Syntax module instance for environments *)
Section env_syntaxmodule.

  Context
    `{SyntaxModule W F T}.

  Local Notation "'env' A" := (alist (F A)) (at level 50, no associativity).

  (** ** Module instance *)
  #[global] Instance Mbind_env : Mbind (fun A => env A) T :=
    fun A B f => envmap (mbind F f).

  Theorem mbind_id_env : forall A,
      mbind (fun A => env A) (mret T) = @id (env A).
  Proof.
    intro. unfold_ops Mbind_env.
    rewrite (rmod_mret F T).
    now unfold envmap; rewrite (fun_fmap_id _).
  Qed.

  Theorem mbind_mbind_env : forall (A B C : Type) (f : A ~k~> T B) (g : B ~k~> T C),
      mbind _ g ∘ mbind _ f = mbind _ (fun k : K => mbind (T k) g ∘ f k).
  Proof.
    intros. unfold_ops @Mbind_env.
    unfold envmap.
    rewrite (fun_fmap_fmap (fun A => alist A)).
    now rewrite (rmod_mbind_mbind F T).
  Qed.

  #[global] Instance Module_env : RightModule (fun A => env A) T :=
    {| rmod_mret := mbind_id_env;
       rmod_mbind_mbind := mbind_mbind_env;
    |}.

  (** ** Listable instance *)
  #[global] Instance Tomlist_env : Tomlist (fun A => alist (F A)) :=
    fun A => bind list (T:=list) (tomlist F ∘ snd).

  Theorem lrmod_mbind_env : forall {A B} (f : forall k, A -> T k B),
      tomlist _ ∘ mbind _ f =
      mbind mlist (fun k => tomlist (T k) ∘ f k) ∘ tomlist _.
  Proof.
    intros. unfold_ops @Tomlist_env.
    change (@snd atom (F B)) with (@extract (prod atom) _ (F B)).
    unfold_ops @Mbind_env @Mbind_mlist @Mbind_T_Tag.
    unfold envmap; unfold_ops @Fmap_alist.
    unfold mlist; rewrite (bind_fmap list list).
    reassociate -> on left.
    unfold_compose_in_compose.
    rewrite <- (Functors.natural (G := fun A => A));
      unfold_ops @Fmap_one.
    rewrite (bind_bind list list).
    fequal. ext [a t]. unfold compose; cbn. compose near t on left.
    now rewrite (lrmod_mbind F T).
  Qed.

  #[global] Instance Lrmod_env : ListableRightModule (fun A => alist (F A)) T :=
    {| lrmod_mbind := @lrmod_mbind_env;
    |}.

  (** *** Decorated instance *)
  #[global] Instance Decorate_env : Decorate (Row W) (fun A => alist (F A)) :=
    fun A => fmap (fun A => alist A) (decorate F).

  Theorem drmod_read_read_env : forall {A},
      decorate _ ∘ decorate _ (A:=A) =
      mfmap _ (fun k => dup_left) ∘ decorate _.
  Proof.
    intros. unfold decorate, Decorate_env.
    unfold mfmap at 1, Mfmap_rmod, mbind, Mbind_env, envmap.
    rewrite 2(fun_fmap_fmap (fun A => alist A)).
    fequal. now rewrite (decf_read_read (Row W)).
  Qed.

  Theorem drmod_read_proj_env : forall {A},
      mfmap (fun A => env A) (const snd) ∘ decorate _ = @id (env A).
  Proof.
    intros. unfold decorate, Decorate_env.
    unfold mfmap at 1, Mfmap_rmod, mbind, Mbind_env, envmap.
    rewrite (fun_fmap_fmap (fun A => alist A)).
    change (mbind F (mret T ◻ const snd))with
        (mfmap F (A:=Row W*A)(B:=A) (const snd)).
    rewrite (decf_read_proj (Row W)).
    rewrite (fun_fmap_id (fun A => alist A)).
    reflexivity.
  Qed.

  #[global] Instance drmod_natural_env :
    Natural (@decorate _ (fun A => alist (F A)) _).
  Proof.
    intros A B f. unfold decorate, Decorate_env.
    unfold mfmap at 1, Mfmap_rmod, Mfmap_comp_Fmap.
    unfold mfmap, mbind, Mbind_env, envmap.
    rewrite 2(fun_fmap_fmap (fun A => alist A)).
    fequal. change (mbind F (mret T ◻ f)) with (mfmap F f).
    now rewrite <- (naturality (η := @decorate (Row W) F _)).
  Qed.

  Theorem drmod_mbind_env : forall {A B} (f : forall k, A -> T k B),
      decorate _ ∘ mbind _ f =
      mbind _ (fun k => shift ∘ map_snd (decorate (T k) ∘ f k)) ∘ decorate _.
  Proof.
    intros. unfold decorate at 1 3, Decorate_env. unfold mbind, Mbind_env.
    unfold envmap. unfold fmap at 1 2 3 4, Fmap_alist. rewrite 2(fun_fmap_fmap list).
    rewrite 2(fun_fmap_fmap (prod atom)). rewrite (drmod_mbind (Row W) F T).
    reflexivity.
  Qed.

  #[global] Instance DecoratedModule_env :
    DecoratedModule (Row W) (fun A => alist (F A)) T :=
    {| drmod_read_read := @drmod_read_read_env;
       drmod_read_proj := @drmod_read_proj_env;
       drmod_mbind := @drmod_mbind_env;
    |}.

  (** *** Properness *)
  Theorem inm_env_iff : forall A (e : env A) (k : K) (a : A),
      (k, a) ∈m e <-> exists (x : atom) (t : F A), (x, t) ∈ e /\ (k, a) ∈m t.
  Proof.
    intros. unfold tomset, tomset_Listable. unfold tomlist at 1, Tomlist_env.
    unfold compose. unfold tomset, tomset_mlist. rewrite (in_bind_iff list).
    split.
    - intros [[x t] [? ?]]. eauto.
    - intros [t [x [? ?]]]. eauto.
  Qed.

  Lemma tomset_mfmap_proper_alist : forall A B (t : (list ∘ prod atom) A) (f g : A -> B),
      (forall (x : atom) (a : A), (x, a) ∈ (t : list (atom * A)) -> f a = g a) ->
      fmap (list ∘ prod atom) f t = fmap (list ∘ prod atom) g t.
  Proof.
    intros. unfold fmap, Fmap_alist.
    unfold compose at 1. (* todo: this is hidden *)
    (*
    rewrite <- List.fmap_strong_proper_list.
    intros [? ?] ?. cbn. fequal. eauto.
  Qed.
     *)
  Admitted.

  Theorem tomset_mbind_proper_env :
    forall A B (t : env A) (f g : forall k, A -> T k B),
      (forall k a, (k, a) ∈m t -> f k a = g k a) ->
      mbind _ f t = mbind _ g t.
  Proof.
    introv hyp.
    unfold mbind, Mbind_env.
    apply tomset_mfmap_proper_alist.
    intros. apply (mbind_properness F). intros.
    apply hyp. setoid_rewrite (inm_env_iff).
    exists x a. auto.
  Qed.

  (** *** <<SyntaxModule>> instance *)
  #[global] Instance SyntaxModule_env : SyntaxModule W (fun A => alist (F A)) T :=
    { synmod_proper := tomset_mbind_proper_env; }.

End env_syntaxmodule.

(** * Rewriting principles *)
Section env_rewriting_lemmas.

  Context
    `{SyntaxModule W F T}.

  Local Notation "'env' A" := (alist (F A)) (at level 50).

  (** ** Rewriting lemmas for [tomlist], [tomset] *)
  Lemma tomlist_env_nil : forall A,
      tomlist (fun A => env A) (nil : env A) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma tomlist_env_cons : forall (x : atom) A (t : F A) (e : env A),
      tomlist _ ((x, t) :: e) = tomlist F t ++ tomlist _ e.
  Proof.
    reflexivity.
  Qed.

  Lemma tomlist_env_one : forall (x : atom) A (t : F A),
      (tomlist _ (x ~ t)) = tomlist F t.
  Proof.
    intros. cbn. now simpl_alist.
  Qed.

  Lemma tomlist_env_app : forall A (e1 e2 : env A),
      tomlist (fun A => env A) (e1 ++ e2) = tomlist _ e1 ++ tomlist _ e2.
  Proof.
    intros. unfold tomlist, Tomlist_env. now (autorewrite with tea_list).
  Qed.

  Lemma tomset_env_nil : forall A,
      tomset (fun A => env A) (nil : env A) = ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma tomset_env_cons : forall (x : atom) A (t : F A) (e : env A),
      tomset (fun A => env A) ((x, t) :: e) = tomset F t ∪ tomset _ e.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now rewrite tomlist_env_cons, tomset_mlist_app.
  Qed.

  Lemma tomset_env_one : forall (x : atom) A (t : F A),
      (tomset (fun A => env A) (x ~ t)) = tomset F t.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now rewrite tomlist_env_one.
  Qed.

  Lemma tomset_env_app : forall A (e1 e2 : env A),
      tomset (fun A => env A) (e1 ++ e2) = tomset _ e1 ∪ tomset _ e2.
  Proof.
    intros. unfold tomset, tomset_Listable, compose.
    now rewrite tomlist_env_app, tomset_mlist_app.
  Qed.

  Lemma inm_env_nil : forall A k (a : A),
      (k, a) ∈m (nil : env A) <-> False.
  Proof.
    reflexivity.
  Qed.

  Lemma inm_env_cons : forall (x : atom) A (t : F A) (e : env A) (k : K) (a : A),
      (k, a) ∈m ((x, t) :: e) <-> (k, a) ∈m t \/ (k, a) ∈m e.
  Proof.
    intros. now rewrite tomset_env_cons.
  Qed.

  Lemma inm_env_one : forall (x : atom) A (t : F A) k a,
      (k, a) ∈m (x ~ t) <-> (k, a) ∈m t.
  Proof.
    intros. now rewrite tomset_env_one.
  Qed.

  Lemma inm_env_app : forall A (k : K) (a : A) (e1 e2 : env A),
      (k, a) ∈m (e1 ++ e2) <-> (k, a) ∈m e1 \/ (k, a) ∈m e2.
  Proof.
    intros. now rewrite tomset_env_app.
  Qed.

  (** ** Rewriting lemmas for <<subst>> *)
  Lemma subst_nil : forall (k : K) (x : atom) (t : T k leaf),
      (nil : env leaf) '{ k | x ~> t} = nil.
  Proof.
    reflexivity.
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

  (** ** Rewriting lemmas for [free] *)
  Lemma free_nil : forall (k : K) (x : atom) (t : T k leaf),
      free (fun A => env A) k (nil : env leaf) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma free_one : forall (k : K) (x : atom) (t : F leaf),
      free (fun A => env A) k (x ~ t) = free F k t.
  Proof.
    intros. unfold free, tolistk, compose.
    now rewrite tomlist_env_one.
  Qed.

  Lemma free_cons : forall (k : K) (x : atom) (t : F leaf) (e : env leaf),
      free (fun A => env A) k ((x, t) :: e) = free F k t ++ free (fun A => env A) k e.
  Proof.
    intros. unfold free. unfold tolistk, compose, tomlist, Tomlist_env.
    now rewrite List.bind_list_cons, filterk_app, List.bind_list_app.
  Qed.

  Lemma free_app : forall (k : K) (e1 e2 : env leaf),
      free (fun A => env A) k (e1 ++ e2) =
      free (fun A => env A) k e1 ++ free (fun A => env A) k e2.
  Proof.
    intros. unfold free, tolistk, tomlist, Tomlist_env, compose.
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

  (** ** Rewriting lemmas for [freeset] *)

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

(** ** Other reasoning principles *)
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

(** ** Scope reasoning principles *)

Definition scoped_env `{H : Index} F `{Tomlist F} {A} :
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
