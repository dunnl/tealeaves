From Tealeaves Require Export
  Classes.EqDec_eq
  Functors.List_Telescoping_General
  Backends.Common.Names
  Functors.List
  Functors.Constant
  Functors.Subset.

Import Subset.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import List.ListNotations.
Import Product.Notations.
Import ContainerFunctor.Notations.

Open Scope list_scope.

(** * The <<fold_with_history>> Operation *)
(**********************************************************************)
(* Fold over a list of A's where each A has the prefix of the list so far *)
Fixpoint fold_with_history {A B: Type}
  (f: list B * A -> B)
  (l: list A): list B :=
  match l with
  | nil => nil
  | cons a rest =>
      f ([], a) :: fold_with_history (f ⦿ [f ([], a)]) rest
  end.

(** ** Rewriting rules for <<fold_with_history>> *)
(**********************************************************************)
Section rw.

  Context {A B: Type}.

  Section basic.

    Context (f: list B * A -> B).

    Lemma fold_with_history_nil:
      fold_with_history f nil = nil.
    Proof.
      reflexivity.
    Qed.

    Lemma fold_with_history_cons {a l}:
      fold_with_history f (a :: l) =
        f ([], a) :: fold_with_history (f ⦿ [f ([], a)]) l.
    Proof.
      cbn.
      reflexivity.
    Qed.

    Lemma fold_with_history_one {a}:
      fold_with_history f ([a]) =
        [f ([], a)].
    Proof.
      cbn.
      reflexivity.
    Qed.

  End basic.

  Lemma fold_with_history_app {l1 l2: list A}:
    forall (f: list B * A -> B),
      fold_with_history f (l1 ++ l2) =
        fold_with_history f l1 ++
          fold_with_history (f ⦿ fold_with_history f l1) l2.
  Proof.
    induction l1 as [|a l1 IHl1]; intros.
    - cbn. change (f ⦿ []) with (f ⦿ Ƶ).
      now rewrite preincr_zero.
    - rewrite <- List.app_comm_cons.
      rewrite fold_with_history_cons.
      rewrite fold_with_history_cons.
      rewrite IHl1.
      rewrite <- List.app_comm_cons.
      rewrite preincr_preincr.
      reflexivity.
  Qed.

  (* Tailored for use when the list is a nominal binding context decomposition *)
  Lemma fold_with_history_decompose {l1 l2: list A} {a: A}:
    forall (f: list B * A -> B),
      fold_with_history f (l1 ++ [a] ++ l2) =
        fold_with_history f l1 ++
          [f (fold_with_history f l1, a)] ++
          fold_with_history (f ⦿ (fold_with_history f l1 ++ [f (fold_with_history f l1, a)])) l2.
  Proof.
    intros.
    rewrite fold_with_history_app.
    rewrite fold_with_history_app.
    rewrite fold_with_history_one.
    rewrite preincr_preincr.
    unfold preincr, incr, compose.
    unfold_ops @Monoid_op_list.
    rewrite List.app_nil_r.
    reflexivity.
  Qed.

End rw.

(** ** An Induction Rule for <<fold_with_history>> *)
(**********************************************************************)
Section induction.

  Import Theory.TraversableFunctor.

  Context
    {A B: Type}
    {f: list B * A -> B}
    (P: B -> Prop).

  Section Forall.

    Context
      (Hbase: forall (a: A), P (f (nil, a)))
      (Hstep: forall (a: A) (h: list B),
      Forall P h -> P (f (h, a))).

    Lemma fold_with_history_ind_Forall: forall (l: list A),
        Forall P (fold_with_history f l).
    Proof.
      intro l.
      induction l as [| a rest IHrest] using List.rev_ind.
      - reflexivity.
      - rewrite fold_with_history_app.
        rewrite TraversableFunctor.forall_iff.
        rewrite TraversableFunctor.forall_iff in IHrest.
        intro b.
        rewrite element_of_list_app.
        intros [Case1| Case2].
        + auto.
        +rewrite fold_with_history_one in Case2.
         rewrite element_of_list_one in Case2.
         subst.
         apply Hstep.
         change (@nil B) with (Ƶ: list B).
         rewrite monoid_id_l.
         rewrite TraversableFunctor.forall_iff.
         assumption.
    Qed.

  End Forall.

  Section elementwise.

    Context
      (Hbase: forall (a: A), P (f (nil, a)))
      (Hstep: forall (a: A) (h: list B),
        (forall (b: B), b ∈ h -> P b) -> P (f (h, a))).

    Lemma fold_with_history_ind: forall (l: list A),
        forall (b: B), b ∈ fold_with_history f l -> P b.
    Proof.
      intro l.
      rewrite <- TraversableFunctor.forall_iff.
      apply fold_with_history_ind_Forall.
      intros; apply Hstep.
      rewrite TraversableFunctor.forall_iff in H.
      assumption.
    Qed.

  End elementwise.

End induction.

(** ** Relating History to the Prefix: <<map_with_history>> *)
(**********************************************************************)
Section relate_history_prefix.

  Context {A B: Type} (f: list B * A -> B).

  Definition run_using_prefix: list A * A -> B :=
    fun '(prefix, a) => f (fold_with_history f prefix, a).

  Lemma run_using_prefix_app_spec: forall (l: list A) (a: A),
      fold_with_history f (l ++ [a]) =
        fold_with_history f l ++ [run_using_prefix (l, a)].
  Proof.
    intros.
    rewrite fold_with_history_app.
    fequal.
    rewrite fold_with_history_one.
    unfold preincr, incr, compose.
    change (@nil B) with (Ƶ: list B) at 1.
    rewrite monoid_id_l.
    fequal.
  Qed.

  Lemma run_using_prefix_nil: forall (a: A),
    run_using_prefix (nil, a) = f (nil, a).
  Proof.
    reflexivity.
  Qed.

  Lemma run_using_prefix_cons {a l x}:
    run_using_prefix (a :: l, x) =
      f (f ([], a) :: fold_with_history (f ⦿ [f ([], a)]) l, x).
  Proof.
    reflexivity.
  Qed.

  Lemma run_using_prefix_app {l1 l2 x}:
    run_using_prefix (l1 ++ l2, x) =
      f (fold_with_history f l1 ++ fold_with_history (f ⦿ fold_with_history f l1) l2, x).
  Proof.
    cbn.
    rewrite fold_with_history_app.
    reflexivity.
  Qed.

  Lemma run_using_prefix_one {a x}:
    run_using_prefix ([a], x) =
      f ([f ([], a)], x).
  Proof.
    cbn.
    reflexivity.
  Qed.

End relate_history_prefix.

Lemma run_using_prefix_spec {A B: Type} (f: list B * A -> B):
  mapd_list_prefix (run_using_prefix f) =
    fold_with_history f.
Proof.
  ext l.
  generalize dependent f.
  induction l; intros.
  - cbn.
    reflexivity.
  - rewrite mapd_list_prefix_rw_cons.
    rewrite fold_with_history_cons.
    rewrite run_using_prefix_nil.
    rewrite <- IHl.
    fequal.
    fequal.
    ext [w a'].
    cbn.
    reflexivity.
Qed.


(** * Folding with context AND history *)
(**********************************************************************)
Fixpoint fold_with_ctx_history_rec {A B: Type}
  (f: list B * list A * A -> B)
  (hist: list B) (ctx: list A)

  (l: list A): list B :=
  match l with
  | nil => nil
  | cons a rest =>
      f (hist, ctx, a) :: fold_with_ctx_history_rec f (hist ++ [f (hist, ctx, a)]) (ctx ++ [a]) rest
  end.

Definition fold_with_ctx_history {A B: Type}
  (f: list B * list A * A -> B)
  (l: list A): list B :=
  fold_with_ctx_history_rec f [] [] l.

Section rw.

  Context {A B: Type}.

  Section basic.

    Context (f: list B * list A * A -> B).

    Lemma fold_with_ctx_history_nil_rec: forall hist ctx,
      fold_with_ctx_history_rec f hist ctx nil = nil.
    Proof.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_cons {a l}:
      fold_with_ctx_history f (a :: l) =
        f ([], [], a) :: fold_with_ctx_history_rec f [f ([], [], a)] [a] l.
    Proof.
      cbn.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_one_rec {hist ctx a}:
      fold_with_ctx_history_rec f hist ctx ([a]) =
        [f (hist, ctx, a)].
    Proof.
      cbn.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_nil:
      fold_with_ctx_history f nil = nil.
    Proof.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_cons_rec {hist ctx a l}:
      fold_with_ctx_history_rec f hist ctx (a :: l) =
        f (hist, ctx, a) :: fold_with_ctx_history_rec f (hist ++ [f (hist, ctx, a)]) (ctx ++ [a]) l.
    Proof.
      cbn.
      reflexivity.
    Qed.

    Lemma fold_with_ctx_history_one {a}:
      fold_with_ctx_history f ([a]) =
        [f ([], [], a)].
    Proof.
      cbn.
      reflexivity.
    Qed.

  End basic.

  Lemma fold_with_ctx_history_app_rec {l1 l2: list A}:
    forall (f: list B * list A * A -> B) hist ctx,
      fold_with_ctx_history_rec f hist ctx (l1 ++ l2) =
        fold_with_ctx_history_rec f hist ctx l1 ++
          fold_with_ctx_history_rec f (hist ++ fold_with_ctx_history_rec f hist ctx l1) (ctx ++ l1) l2.
  Proof.
    induction l1 as [|a l1 IHl1]; intros.
    - cbn.
      do 2 rewrite List.app_nil_r.
      reflexivity.
    - rewrite <- List.app_comm_cons.
      rewrite fold_with_ctx_history_cons_rec.
      rewrite fold_with_ctx_history_cons_rec.
      rewrite IHl1.
      rewrite <- List.app_comm_cons.
      repeat rewrite <- List.app_assoc.
      reflexivity.
  Qed.

  Lemma fold_with_ctx_history_app {l1 l2: list A}:
    forall (f: list B * list A * A -> B),
      fold_with_ctx_history f (l1 ++ l2) =
        fold_with_ctx_history f l1 ++
          fold_with_ctx_history_rec f (fold_with_ctx_history_rec f [] [] l1) l1 l2.
  Proof.
    intros. unfold fold_with_ctx_history.
    rewrite fold_with_ctx_history_app_rec.
    rewrite List.app_nil_l.
    rewrite List.app_nil_l.
    reflexivity.
  Qed.

End rw.





(** ** The logic of binding *)
(**********************************************************************)
Inductive Binding: Type :=
  Bound: list name -> name -> list name -> Binding
| Unbound: list name -> name -> Binding.

Fixpoint get_binding_rec_bound (looking_for: name) (prefix: list name) (postfix: list name) (l: list name):
  Binding :=
  match l with
  | nil => Bound prefix looking_for postfix
  | cons y ys =>
      if looking_for == y
      then get_binding_rec_bound looking_for (prefix ++ [looking_for] ++ postfix) [] ys
      else get_binding_rec_bound looking_for (prefix) (postfix ++ [y]) ys
  end.

Fixpoint get_binding_rec_unbound (looking_for: name) (prefix: list name) (l: list name): Binding :=
  match l with
  | nil => Unbound prefix looking_for
  | cons y ys =>
      if looking_for == y
      then get_binding_rec_bound looking_for prefix [] ys
      else get_binding_rec_unbound looking_for (prefix ++ [y]) ys
  end.

Definition get_binding (ctx: list name) (v: name) :=
  get_binding_rec_unbound v [] ctx.

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
        {exists pre post: list name, get_binding_rec_unbound v pre' l =
                                  Bound pre v post /\ (pre' ++ l = pre ++ [v] ++ post) /\ ~ v ∈ post}.
  Proof.
    intros.
    unfold get_binding.
    generalize dependent pre'.
    induction l; intros pre' prenin.
    - cbn. left. rewrite List.app_nil_r.
      auto.
    - destruct_eq_args v a.
      + right.
        rewrite get_binding_rec_unbound_cons_eq; auto.
        specialize (get_binding_bound_general a pre' [] l ltac:(firstorder)).
        intros [pre [post [rest1 [rest2 rest3]]]].
        exists pre post. repeat rewrite List.app_nil_l in rest2.
        auto.
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

  Lemma get_binding_spec: forall (l: list name) (v: name),
      {get_binding l v = Unbound l v /\ ~ v ∈ l} +
        {exists pre post, get_binding l v = Bound pre v post  /\ l = pre ++ [v] ++ post /\ ~ v ∈ post}.
  Proof.
    intros.
    unfold get_binding.
    specialize (get_binding_spec_gen l v []); intro.
    specialize (H ltac:(firstorder)).
    rewrite List.app_nil_l in H.
    auto.
  Qed.


  Lemma get_binding1: forall ctx v,
      ~ (v ∈ ctx) -> get_binding ctx v = Unbound ctx v.
  Proof.
    intros. destruct (get_binding_spec ctx v).
    - tauto.
    - enough (v ∈ ctx).
      contradiction.
      destruct e as [pre [post [rest1 [rest2 rest3]]]].
      rewrite rest2.
      autorewrite with tea_list. tauto.
  Qed.


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

  Lemma list_occ_spec {A}:
    forall (prefix prefix' postfix: list A) (a a': A),
      prefix ++ [a] = prefix' ++ [a'] ++ postfix ->
        (prefix = prefix' /\ a = a' /\ postfix = []) \/ a ∈ postfix.
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
        rewrite element_of_list_app.
        rewrite element_of_list_one.
        now right.
    }
  Qed.


  Lemma list_occ_lemma {A}:
    forall (prefix prefix' postfix: list A) (a: A),
      prefix ++ [a] = prefix' ++ [a] ++ postfix ->
      (prefix = prefix' /\ postfix = []) \/ a ∈ postfix.
  Proof.
    intros.
    apply list_occ_spec in H.
    tauto.
  Qed.

  Lemma list_occ_lemma2 {A}:
    forall (prefix prefix' postfix postfix' : list A) (v a: A),
      v <> a ->
      prefix ++ [v] ++ a :: postfix = prefix' ++ [v] ++ postfix' ->
      exists postfix'', postfix' = a :: postfix''.
  Proof.
    intros.
    induction postfix.
    - exists (@nil A).
      induction postfix'.
      + specialize (list_occ_lemma prefix prefix' (@nil A) v).
        intro.
  Abort.

  Lemma list_binding_inversion_prefix {A}:
    forall (prefix postfix prefix' postfix': list A) (v: A)
      (Hnin : ~ v ∈ postfix)
      (Hnin': ~ v ∈ postfix'),
      prefix ++ [v] ++ postfix = prefix' ++ [v] ++ postfix' ->
      prefix = prefix' /\ postfix = postfix'.
  Proof.
    intros.
    generalize dependent prefix.
    generalize dependent prefix'.
    generalize dependent v.
    induction postfix; intros.
    - rewrite List.app_nil_r in H.
      specialize (list_occ_lemma _ _ _ v H).
      destruct 1 as [[Hyp1 Hyp2] | Hyp3].
      + subst. split; auto.
      + contradiction.
  Abort.



  Lemma list_binding_inversion {A}:
    forall (prefix postfix prefix' postfix': list A) (v: A)
      (Hnin : ~ v ∈ postfix)
      (Hnin': ~ v ∈ postfix'),
      prefix ++ [v] ++ postfix = prefix' ++ [v] ++ postfix' ->
      prefix = prefix' /\ postfix = postfix'.
  Proof.
    intros.
  Admitted.


  Lemma get_binding2: forall prefix v postfix ctx,
      ctx = prefix ++ [v] ++ postfix ->
      ~ (v ∈ postfix) ->
      get_binding ctx v = Bound prefix v postfix.
  Proof.
    introv Heq Hnin. subst.
    destruct (get_binding_spec (prefix ++ [v] ++ postfix) v)
      as [[Case1 rest] | [prefix' [postfix' [Case2 [ctxspec Hnin']]]]].
    - false. apply rest.
      rewrite element_of_list_app.
      rewrite element_of_list_app.
      rewrite element_of_list_one.
      tauto.
    - rewrite Case2.
      apply list_binding_inversion in ctxspec; auto.
      destruct ctxspec; subst. reflexivity.
  Qed.

End rw.


Section rw.

  #[local] Notation "'l'" := [ 1 ; 3; 4; 3; 2 ].

  Compute get_binding l 1. (* [] 1 [3; 4; 3; 2] *)
  Compute get_binding l 2. (* Bound [1; 3; 4; 3] 2 [] *)
  Compute get_binding l 3. (* Bound [1; 3; 4] 3 [2] *)

End rw.

Section examples.

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
