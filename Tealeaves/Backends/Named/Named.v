From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.List_Telescoping_General
  Backends.Named.Names
  Functors.Constant
  Functors.Subset.

Import Subset.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import List.ListNotations.
Import Product.Notations.
Import ContainerFunctor.Notations.

(** * Fully named syntax *)
(**********************************************************************)

(** ** General operations on lists *)
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

End rw.


(** ** Variable freshness *)
(**********************************************************************)
(* Given the history of output names so far, decide the name of this binder *)
Definition hf_loc: list name * name -> name :=
  fun '(history, current) =>
    if SmartAtom.name_inb current history
    then fresh history
    else current.

Definition hf: list name -> list name := fold_with_history hf_loc.
Section examples.

  Compute hf_loc ([], 1).
  Compute hf_loc ([1], 0).
  Compute hf_loc ([1], 1).
  Compute hf_loc ([1; 2], 1).
  Compute hf_loc ([0; 1; 2], 1).

  Compute hf nil = nil.
  Compute hf [0].
  Compute hf [1].
  Compute hf [1; 2].
  Compute hf [1; 2; 3].
  Compute hf [1; 2; 3; 4].
  Compute hf [0; 0].
  Compute hf [1; 0].
  Compute hf [0; 1; 0].
  Compute hf [0; 1; 0; 1].
  Compute hf [0; 1; 0; 1; 0; 1].
  Compute hf [0; 1; 3; 1; 0; 1].

(*
  Goal hf nil = nil. reflexivity. Qed.
  Goal hf [1] = [1]. cbv. reflexivity. Qed.
  Goal hf [1 ; 2] = [1 ; 2]. reflexivity. Qed.
  Goal hf [1 ; 2 ; 3] = [1 ; 2 ; 3]. reflexivity. Qed.

  Goal hf [1 ; 1 ] = [1 ; 2 ]. reflexivity. Qed.
  Goal hf [1 ; 1 ; 1 ] = [1 ; 2 ; 3 ]. reflexivity. Qed.
  Goal hf [1 ; 2 ; 1] = [1 ; 2 ; 3]. reflexivity. Qed.
  Goal hf [1 ; 3 ; 8] = [1 ; 2 ; 3]. reflexivity. Qed.
  Goal hf [1 ; 4 ; 6] = [1 ; 2 ; 3]. reflexivity. Qed.
  Goal hf [1 ; 4 ; 6 ; 4] = [1 ; 2 ; 3 ; 4]. reflexivity. Qed.
  Goal hf [1 ; 4 ; 6 ; 4 ; 9 ; 10] = [1 ; 2 ; 3 ; 4; 5; 6]. reflexivity. Qed.
  Goal hf [1 ; 4 ; 8 ; 8 ] = [1 ; 2 ; 3 ; 4 ]. reflexivity. Qed.
 *)

End examples.

(** ** The logic of binding *)
(**********************************************************************)
Inductive Binding: Type :=
  Bound: list name -> name -> list name -> Binding
| Unbound: list name -> Binding.

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
  | nil => Unbound prefix
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
      {get_binding_rec_unbound v pre' l = Unbound (pre' ++ l) /\ ~ v ∈ (pre' ++ l)} +
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
      {get_binding l v = Unbound l /\ ~ v ∈ l} +
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
      ~ (v ∈ ctx) -> get_binding ctx v = Unbound ctx.
  Proof.
    intros. destruct (get_binding_spec ctx v).
    - tauto.
    - enough (v ∈ ctx).
      contradiction.
      destruct e as [pre [post [rest1 [rest2 rest3]]]].
      rewrite rest2.
      autorewrite with tea_list. tauto.
  Qed.

End rw.


Section rw.

  #[local] Notation "'l'" := [ 1 ; 3; 4; 3; 2 ].

  Compute get_binding l 1. (* [] 1 [3; 4; 3; 2] *)
  Compute get_binding l 2. (* Bound [1; 3; 4; 3] 2 [] *)
  Compute get_binding l 3. (* Bound [1; 3; 4] 3 [2] *)

End rw.

(*
  Lemma get_binding_rec_unbound1: forall l1 l2 a,
  get_binding_rec_unbound l1 [a] l2 = Unbound (l1 + l) ->
  get_binding_rec_unbound [a] l2 = Unbound (l1 + l) ->
  get_binding_rec_unbound v [a] l
 *)


(*

  Fixpoint get_binding_rec (discarded: list name)  (l: list name) (looking_for: name): Binding :=
  match l with
  | nil => Unbound discarded
  | cons y ys =>
  if looking_for == y
  then Bound discarded y ys
  else get_binding_rec (discarded ++ [y]) ys looking_for
  end.

  Fixpoint get_binding_rec (discarded: list name)  (l: list name) (looking_for: name): Binding :=
  match l with
  | nil => Unbound discarded
  | cons y ys =>
  if looking_for == y
  then Bound discarded y ys
  else get_binding_rec (discarded ++ [y]) ys looking_for
  end.


  Definition get_binding: list name -> name -> Binding :=
  get_binding_rec [].



  Lemma get_binding_spec: forall (disc: list name) (l: list name) (v: name),
  {get_binding_rec disc l v = Unbound (disc ++ l) /\ ~ v ∈ l} +
  {exists pre post, get_binding_rec disc l v = Bound (disc ++ pre) v post  /\ l = pre ++ [v] ++ post /\ ~ v ∈ post}.
  Proof.
  intros.
  induction l.
  - cbn. left.
  rewrite List.app_nil_r; split; auto.
  - (* Lookup v in (a :: l) after discarding (disc). *)
  cbn.
  destruct_eq_args v a.
  + right. destruct (IHl).
  * exists (@nil name). exists l.
  rewrite List.app_nil_r.
  rewrite List.app_nil_l.
  split. firstorder.
  firstorder.
  * destruct e as [pre [post [IH1 [IH2 IH3]]]].
  exists (@nil name) post.
  rewrite List.app_nil_r.
  rewrite List.app_nil_l.
  split; auto.
  split; auto.
  firstorder.

  induction l.
  { exists (@nil name) (@nil name).
  rewrite List.app_nil_r.
  rewrite List.app_nil_l.
  split; auto.
  }
  { destruct
  +

  .
 *)

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

(** ** Localized operations *)
(**********************************************************************)
Section named_local_operations.

  Context
    {T: Type -> Type -> Type}
    `{forall W, Return (T W)}.

  Definition FV_loc: list name * name -> list name :=
    fun '(ctx, x) => if get_binding ctx x then @nil name else [x].

  Definition deconflict_binder_local (conflicts: list name):
    list name * name -> name :=
    hf_loc ⦿ conflicts.

  Definition subst_local
    (conflicts: list name)
    (looking_for: name)
    (u: T name name):
    list name * name -> T name name :=
    fun '(context, var) =>
      match (get_binding context var) with
      | Unbound _ =>
          if var == looking_for
          then u
          else ret (T := T name) var
      | Bound prefix _ _ =>
          ret (T := T name) (hf_loc (conflicts ++ prefix, var))
      end.

  Definition alpha_equiv_local:
    list name * name -> list name * name -> Prop :=
    fun '(ctx0, nm0) '(ctx1, nm1) =>
      match (get_binding ctx0 nm0, get_binding ctx1 nm1) with
      | (Bound prefix0 _ _, Bound prefix1 _ _) =>
          if length prefix0 == length prefix1
          then True
          else False
      | _ => False
      end.

End named_local_operations.

(** ** Localized operations *)
(**********************************************************************)
Section named_local_operations.

  Context
    (T: Type -> Type -> Type)
    `{MapdtPoly T}.

  Definition FV: T name name -> list name :=
    mapdtp
      (T := T)
      (A1 := name) (B1 := name)
      (A2 := False) (B2 := False)
      (G := const (list name))
      (const (@nil name))
      FV_loc.

  Definition alpha:
    T name name -> T name name -> Prop.
  Admitted.

  Import DecoratedTraversableMonadPoly.DerivedOperations.

  Context
    `{forall W, Return (T W)}
    `{Substitute T T}.

  Definition subst_conflicts (top_conflicts: list name)
    (x: name) (u: T name name):
    T name name -> T name name :=
    substitute (G := fun A => A) (U := T)
      (deconflict_binder_local top_conflicts)
      (subst_local top_conflicts x u).

  Definition subst (x: name) (u: T name name)
    (t: T name name): T name name :=
    subst_conflicts (FV t ++ FV u) x u t.

End named_local_operations.
