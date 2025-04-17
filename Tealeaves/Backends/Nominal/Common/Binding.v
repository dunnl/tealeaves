From Tealeaves Require Export
  Classes.EqDec_eq
  Backends.Common.Names
  Functors.List.

#[local] Open Scope list_scope.
#[local] Open Scope tealeaves_scope.


Import List.ListNotations.
Import Monoid.Notations.
Import ContainerFunctor.Notations.

(** * The Logic of Variable Binding *)
(**********************************************************************)
Inductive Binding: Type :=
  Bound: list name -> name -> list name -> Binding
| Unbound: list name -> name -> Binding.

(** ** <<get_binding>> Operation *)
(**********************************************************************)
Fixpoint get_binding_rec_bound
  (looking_for: name)
  (prefix: list name)
  (postfix: list name)
  (l: list name):
  Binding :=
  match l with
  | nil => Bound prefix looking_for postfix
  | cons y ys =>
      if looking_for == y
      then get_binding_rec_bound looking_for (prefix ++ [looking_for] ++ postfix) [] ys
      else get_binding_rec_bound looking_for (prefix) (postfix ++ [y]) ys
  end.

Fixpoint get_binding_rec_unbound
  (looking_for: name)
  (prefix: list name)
  (l: list name): Binding :=
  match l with
  | nil => Unbound prefix looking_for
  | cons y ys =>
      if looking_for == y
      then get_binding_rec_bound looking_for prefix [] ys
      else get_binding_rec_unbound looking_for (prefix ++ [y]) ys
  end.

Definition get_binding (ctx: list name) (v: name) :=
  get_binding_rec_unbound v [] ctx.

(** ** <<get_binding>> Examples *)
(**********************************************************************)
Section examples.

  #[local] Notation "'l'" := [ 1 ; 3; 4; 3; 2 ].

  Compute get_binding l 1. (* [] 1 [3; 4; 3; 2] *)
  Compute get_binding l 2. (* Bound [1; 3; 4; 3] 2 [] *)
  Compute get_binding l 3. (* Bound [1; 3; 4] 3 [2] *)

  Compute get_binding nil 1.
  Compute get_binding nil 2.
  Compute get_binding [1] 1.
  Compute get_binding [2] 1.
  Compute get_binding [1] 2.
  Compute get_binding [2] 2.
  Compute get_binding [1; 2] 1.
  Compute get_binding [1; 2] 2.

  Compute get_binding [1; 2] 1.
  Compute get_binding [1; 2] 2.
  Compute get_binding [1; 2] 3.
  Compute get_binding [1; 2; 3] 1.
  Compute get_binding [1; 2; 3] 2.
  Compute get_binding [1; 2; 3] 3.

End examples.

(** ** <<get_binding>> Specification *)
(**********************************************************************)
Definition get_binding_spec: Type :=
  forall (l: list name) (v: name),
    {get_binding l v = Unbound l v /\ ~ v ∈ l} +
      {exists pre post, get_binding l v = Bound pre v post /\ l = pre ++ [v] ++ post /\ ~ v ∈ post}.

(** ** Rewriting Principles *)
(**********************************************************************)
Section rw.

  Section cons.

    Context (looking_for: name).
    Context (pre post: list name) (a: name).

    Lemma get_binding_rec_unbound_cons_neq: forall l,
        a <> looking_for ->
        get_binding_rec_unbound looking_for pre (a :: l) =
          get_binding_rec_unbound looking_for (pre ++ [a]) l.
    Proof.
      intros.
      cbn.
      destruct_eq_args looking_for a.
    Qed.

    Lemma get_binding_rec_unbound_cons_eq: forall l,
        a = looking_for ->
        get_binding_rec_unbound looking_for pre (a :: l) =
          get_binding_rec_bound looking_for pre [] l.
    Proof.
      intros.
      cbn.
      destruct_eq_args looking_for a.
    Qed.

    Lemma get_binding_rec_bound_cons_neq: forall l,
        a <> looking_for ->
        get_binding_rec_bound looking_for pre post (a :: l) =
          get_binding_rec_bound looking_for pre (post ++ [a]) l.
    Proof.
      intros.
      cbn.
      destruct_eq_args looking_for a.
    Qed.

    Lemma get_binding_rec_bound_cons_eq: forall l,
        a = looking_for ->
        get_binding_rec_bound looking_for pre post (a :: l) =
          get_binding_rec_bound looking_for (pre ++ [a] ++ post) [] l.
    Proof.
      intros.
      cbn.
      destruct_eq_args looking_for a.
    Qed.

    Lemma get_binding_eq: forall l,
        a = looking_for ->
        get_binding (a :: l) looking_for =
          get_binding_rec_bound looking_for [] [] l.
    Proof.
      intros.
      cbn.
      destruct_eq_args looking_for a.
    Qed.

    Lemma get_binding_neq: forall l,
        a <> looking_for ->
        get_binding (a :: l) looking_for =
          get_binding_rec_unbound looking_for [a] l.
    Proof.
      intros.
      cbn.
      destruct_eq_args looking_for a.
    Qed.

  End cons.

End rw.

(** ** Proof of Specification *)
(**********************************************************************)
Lemma get_binding_rec_general: forall (looking_for: name) pre' post' l,
    ~ looking_for ∈ post' ->
    exists (pre post: list name),
      get_binding_rec_bound looking_for pre' post' l =
        Bound pre looking_for post
      /\ ~ looking_for ∈ post.
Proof.
  introv Hanin.
  generalize dependent pre'.
  generalize dependent post'.
  induction l; intros.
  - exists pre' post'. cbn; auto.
  - destruct (looking_for == a).
    { rewrite get_binding_rec_bound_cons_eq; auto. }
    { rewrite get_binding_rec_bound_cons_neq; auto.
      specialize (IHl (post' ++ [a])).
      assert (Hnlf: ~ looking_for ∈ (post' ++ [a])).
      { rewrite element_of_list_app.
        rewrite element_of_list_one.
        firstorder.
      }
      specialize (IHl Hnlf).
      specialize (IHl pre').
      auto.
    }
Qed.

Lemma get_binding_bound_general: forall (looking_for: name) pre' post' l,
    ~ looking_for ∈ post' ->
    exists (pre post: list name),
      get_binding_rec_bound looking_for pre' post' l =
        Bound pre looking_for post
      /\ pre ++ [looking_for] ++ post = (pre' ++ [looking_for] ++ post' ++ l)
      /\ ~ looking_for ∈ post.
Proof.
  introv Hnin.
  generalize dependent pre'.
  generalize dependent post'.
  induction l; intros.
  - exists (pre': list name) (post':list name).
    cbn. splits.
    + auto.
    + rewrite List.app_nil_r.
      reflexivity.
    + assumption.
  - destruct_eq_args looking_for a.
    + rewrite (get_binding_rec_bound_cons_eq a); auto.
      specialize (IHl [] ltac:(firstorder) (pre' ++ [a] ++ post')).
      destruct IHl as [pre [post [rest1 [rest2 rest3]]]].
      exists pre post. splits.
      * tauto.
      * rewrite rest2. rewrite List.app_nil_l.
        repeat rewrite <- List.app_assoc.
        reflexivity.
      * assumption.
    + rewrite (get_binding_rec_bound_cons_neq); auto.
      specialize (IHl (post' ++ [a])).
      assert (Hnlf: ~ looking_for ∈ (post' ++ [a])).
      { rewrite element_of_list_app.
        rewrite element_of_list_one.
        firstorder.
      }
      specialize (IHl Hnlf).
      specialize (IHl pre').
      destruct IHl as [pre [post [rest1 [rest2 rest3]]]].
      exists pre post.
      splits.
      * assumption.
      * rewrite rest2.
        repeat rewrite <- List.app_assoc.
        reflexivity.
      * assumption.
Qed.

Lemma get_binding_spec_gen: forall l v pre',
    ~ v ∈ pre' ->
    {get_binding_rec_unbound v pre' l = Unbound (pre' ++ l) v /\ ~ v ∈ (pre' ++ l)} +
      {exists pre post: list name,
          get_binding_rec_unbound v pre' l =
            Bound pre v post /\ (pre' ++ l = pre ++ [v] ++ post) /\ ~ v ∈ post}.
Proof.
  intros.
  unfold get_binding.
  generalize dependent pre'.
  induction l; intros pre' prenin.
  - cbn.
    left.
    rewrite List.app_nil_r.
    easy.
  - destruct_eq_args v a.
    + (* v = a *)
      right.
      rewrite get_binding_rec_unbound_cons_eq; auto.
      specialize (get_binding_bound_general a pre' [] l ltac:(firstorder)).
      intros [pre [post [rest1 [rest2 rest3]]]].
      exists pre post.
      repeat rewrite List.app_nil_l in rest2.
      easy.
    + rewrite get_binding_rec_unbound_cons_neq; auto.
      specialize (IHl (pre' ++ [a])).
      rewrite <- List.app_assoc in IHl.
      destruct IHl.
      * rewrite element_of_list_app. firstorder.
      * left.
        assumption.
      * right.
        destruct e as [pre [post [rest1 [rest2 rest3]]]].
        exists pre post. splits; auto.
Qed.

Lemma get_binding_spec_proof: get_binding_spec.
Proof.
  unfold get_binding_spec.
  unfold get_binding.
  introv.
  specialize (get_binding_spec_gen l v []); intro.
  specialize (H ltac:(firstorder)).
  rewrite List.app_nil_l in H.
  auto.
Qed.


(** ** Supporting Lemmas on [list] *)
(**********************************************************************)
Lemma list_app_one_inv {A}:
  forall (prefix prefix': list A) (a a': A),
    prefix ++ [a] = prefix' ++ [a'] ->
    prefix = prefix' /\ a = a'.
Proof.
  intros.
  split.
  eapply inv_app_eq_rl.
  2: eassumption.
  reflexivity.
  enough (ListEq: [a] = [a']) by now inversion ListEq.
  eapply inv_app_eq_rr; eauto.
Qed.

Lemma list_decomp_lemma1 {A}:
  forall (prefix prefix' postfix: list A) (a a': A),
    prefix ++ [a] = prefix' ++ [a'] ++ postfix ->
    (prefix = prefix' /\ a = a' /\ postfix = []) \/
      (exists (postfix': list A), postfix = postfix' ++ [a]).
Proof.
  intros.
  { intros.
    generalize dependent prefix.
    generalize dependent prefix'.
    generalize dependent a.
    induction postfix using List.rev_ind; intros.
    + rewrite List.app_nil_r in H.
      apply list_app_one_inv in H.
      left. tauto.
    + right.
      assert (a = x).
      { do 2 rewrite List.app_assoc in H.
        apply list_app_one_inv in H.
        tauto.
      }
      subst.
      exists postfix. reflexivity.
  }
Qed.

Lemma list_decomp_lemma2 {A}:
  forall (prefix prefix' postfix: list A) (a: A),
    prefix ++ [a] = prefix' ++ [a] ++ postfix ->
    (prefix = prefix' /\ postfix = []) \/ a ∈ postfix.
Proof.
  intros.
  apply list_decomp_lemma1 in H.
  destruct H as [Case1 | Case2].
  - now left.
  - right.
    destruct Case2; subst.
    rewrite element_of_list_app.
    right.
    rewrite element_of_list_one.
    reflexivity.
Qed.

Lemma list_decomp_lemma3 {A} `{EqDec_eq A}:
  forall (l l' postfix: list A) (v x: A),
    v <> x ->
    l ++ [x] = (l' ++ [v]) ++ postfix ->
    exists postfix', postfix = postfix' ++ [x].
Proof.
  introv Hneq Hyp.
  rewrite <- List.app_assoc in Hyp.
  apply list_decomp_lemma1 in Hyp.
  destruct Hyp as [Case1 | Case2].
  - destruct Case1 as [? [Heq ?]].
    subst. contradiction.
  - assumption.
Qed.

Lemma list_element_decomposition {A}:
  forall (l: list A) (a: A),
    a ∈ l <-> exists prefix postfix,
      l = prefix ++ [a] ++ postfix.
Proof.
  intros.
  induction l.
  - split; intros [].
    destruct H as [postfix Heq].
    destruct x.
    + cbn in Heq. inversion Heq.
    + cbn in Heq. inversion Heq.
  - rewrite element_of_list_cons. split.
    { intros [Case1 | Case2].
      - subst.
        exists (@nil A).
        exists l.
        rewrite List.app_nil_l.
        reflexivity.
      - apply IHl in Case2.
        destruct Case2 as [pre [post Heq]].
        subst.
        exists (a0 :: pre). exists post.
        reflexivity.
    }
    intros [prefix [postfix Heq]].
    destruct prefix.
    { left. now inversion Heq. }
    { cbn in Heq.
      inversion Heq; subst.
      right.
      rewrite element_of_list_app.
      rewrite element_of_list_cons.
      tauto.
    }
Qed.

Lemma list_binding_inversion_prefix {A} `{EqDec_eq A}:
  forall (prefix postfix prefix' postfix': list A) (v: A)
    (Hnin: ~ v ∈ postfix)
    (Hnin': ~ v ∈ postfix'),
    prefix ++ [v] ++ postfix = prefix' ++ [v] ++ postfix' ->
    prefix = prefix' /\ postfix = postfix'.
Proof.
  introv Hyp.
  generalize dependent postfix'.
  induction postfix using List.rev_ind; intros.
  - rewrite List.app_nil_r in H0.
    specialize (list_decomp_lemma2 prefix prefix' postfix' v H0).
    destruct 1 as [[Hyp1 Hyp2] | Hyp3].
    + subst. split; auto.
    + contradiction.
  - enough (cut: exists postfix'', postfix' = postfix'' ++ [x]).
    { destruct cut as [postfix'' Heq].
      subst.
      repeat rewrite List.app_assoc in H0.
      apply list_app_one_inv in H0.
      destruct H0 as [H0 _].
      assert (~ v ∈ postfix).
      { intro contra.
        apply Hyp.
        rewrite element_of_list_app.
        now left. }
      assert (~ v ∈ postfix'').
      { intro contra.
        apply Hnin'.
        rewrite element_of_list_app.
        now left. }
      specialize (IHpostfix H1).
      specialize (IHpostfix postfix'' H2).
      do 2 rewrite <- List.app_assoc in H0.
      apply IHpostfix in H0.
      inversion H0; subst.
      auto.
    }
    clear Hnin'. clear IHpostfix.
    rewrite List.app_assoc in H0.
    rewrite List.app_assoc in H0.
    rewrite List.app_assoc in H0.
    apply list_decomp_lemma3 in H0; auto.
    intro contra; subst; apply Hyp.
    rewrite element_of_list_app.
    rewrite element_of_list_one.
    now right.
Qed.

(** ** Inverse of Specification *)
(**********************************************************************)
Lemma get_binding1: forall ctx v,
    ~ (v ∈ ctx) -> get_binding ctx v = Unbound ctx v.
Proof.
  intros. destruct (get_binding_spec_proof ctx v).
  - tauto.
  - enough (v ∈ ctx).
    contradiction.
    destruct e as [pre [post [rest1 [rest2 rest3]]]].
    rewrite rest2.
    autorewrite with tea_list. tauto.
Qed.


Lemma get_binding2: forall prefix v1 v2 postfix ctx,
    v1 = v2 ->
    ctx = prefix ++ [v1] ++ postfix ->
    ~ (v1 ∈ postfix) ->
    get_binding ctx v1 = Bound prefix v2 postfix.
Proof.
  introv HVeq Heq Hnin.
  destruct (get_binding_spec_proof (prefix ++ [v2] ++ postfix) v2)
    as [[Case1 rest] | [prefix' [postfix' [Case2 [ctxspec Hnin']]]]].
  - false. apply rest.
    rewrite element_of_list_app.
    rewrite element_of_list_app.
    rewrite element_of_list_one.
    tauto.
  - subst.
    apply list_binding_inversion_prefix in ctxspec; auto.
    destruct ctxspec; subst.
    auto.
Qed.
