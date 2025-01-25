From Tealeaves Require Import
  Backends.Named.Names
  Functors.List
  Functors.Option
  Classes.EqDec_eq
  Classes.Categorical.ContainerFunctor
  Classes.Kleisli.DecoratedContainerFunctor.

From Tealeaves Require
  Backends.Adapters.Key.

Open Scope nat_scope.
Open Scope list_scope.

Import List.ListNotations.
Import ContainerFunctor.Notations.

Generalizable All Variables.

(** * Miscellaneous lemmas *)
(******************************************************************************)
Ltac compare_names :=
    match goal with
    | H: context[?a == ?a'] |- _ =>
        destruct_eq_args a a'
    | |- context[?a == ?a'] =>
        destruct_eq_args a a'
    end.

#[global] Tactic Notation "compare" "names" := compare_names.

(** * Definition of <<key>> and main operations *)
(******************************************************************************)
Definition key :=
  list name.

(** ** Insertion and lookup *)
(******************************************************************************)
Fixpoint key_insert_name (k: key) (a: name): key :=
  match k with
  | nil => [a]
  | cons x rest =>
      if a == x then k else
        x :: key_insert_name rest a
  end.

Fixpoint key_lookup_name (k: key) (a: name): option nat :=
  match k with
  | [] => None
  | x :: rest =>
      if a == x
      then Some 0
      else map S (key_lookup_name rest a)
  end.

Fixpoint key_lookup_index (k: key) (ix: nat): option name :=
  match k, ix with
  | nil, _ => None
  | cons a rest, 0 => Some a
  | cons a rest, S ix => key_lookup_index rest ix
  end.

Fixpoint key_lookup_name_rec (k: key) (acc: nat) (a: name): option nat :=
  match k with
  | nil => None
  | cons x rest =>
      if a == x then Some acc else key_lookup_name_rec rest (S acc) a
  end.

Definition key_lookup_name_alt: key -> name -> option nat :=
  fun k => key_lookup_name_rec k 0.

(** ** Well-formedness predicates *)
(******************************************************************************)
Fixpoint unique (l: list name): Prop :=
  match l with
  | nil => True
  | cons a rest =>
      ~ (a ∈ rest) /\ unique rest
  end.

(*
Definition wf_LN
  `{ToSubset T} (t: T LN) (k: key): Prop :=
  unique k /\ forall (x: name), Fr x ∈ t -> x ∈ k.

Definition wf_DB `{ToCtxset nat T} (t: T nat) (k: key): Prop :=
  unique k /\ exists (gap: nat), cl_at gap t /\ contains_ix_upto gap k.

*)

Definition contains_ix_upto (n: nat) (k: key): Prop :=
  n < length k.

(** * Misc *)
(******************************************************************************)
Definition key_is_name_in (k: key) (a: name):
  {a ∈ k} + {~ a ∈ k}.
Proof.
  induction k.
  - right. inversion 1.
  - pose (element_of_list_cons a a0 k).
    destruct (a == a0).
    + now (left; left).
    + destruct IHk.
      * now (left; right).
      * right. rewrite i.
        intros [contra|contra];
          contradiction.
Defined.

Definition key_is_ix_in (k: key) (ix: nat):
  {contains_ix_upto ix k} + {~ contains_ix_upto ix k}.
Proof.
  unfold contains_ix_upto.
  generalize ix.
  generalize (length k).
  intros a b.
  apply Compare_dec.le_dec.
Defined.

(** * Lemmas about <<key_insert_name>> *)
(******************************************************************************)

(** ** Rewriting *)
(******************************************************************************)
Lemma insert_cons_eq: forall a k x,
    a = x ->
    key_insert_name (a :: k) x = a :: k.
Proof.
  intros. cbn.
  destruct_eq_args x a.
Qed.

Lemma insert_cons_neq: forall a k x,
    a <> x ->
    key_insert_name (a :: k) x = a :: key_insert_name k x.
Proof.
  intros. cbn.
  destruct_eq_args x a.
Qed.

(** ** Alternative spec *)
(******************************************************************************)
Lemma key_lookup_name_rec_spec (k: key) (a: name) (n: nat):
  key_lookup_name_rec k n a = map (fun m => m + n) (key_lookup_name k a).
Proof.
  generalize dependent n.
  induction k; intro n.
  - reflexivity.
  - cbn. destruct (a == a0).
    + reflexivity.
    + rewrite (IHk (S n)).
      compose near (key_lookup_name k a) on right.
      rewrite (fun_map_map).
      fequal. ext m. cbn. lia.
Qed.

Corollary key_lookup_name_spec (k: key) (a: name):
  key_lookup_name_alt k a = key_lookup_name k a.
Proof.
  unfold key_lookup_name_alt.
  rewrite key_lookup_name_rec_spec.
  replace (fun m => m + 0) with (@id nat).
  now rewrite fun_map_id.
  ext m. unfold id. lia.
Qed.

(** ** Insertion and <<unique>> *)
(******************************************************************************)
Lemma key_nin_insert: forall k a a',
    a <> a' ->
    ~ a ∈ k ->
    ~ a ∈ key_insert_name k a'.
Proof.
  introv Hneq Hnin. induction k.
  - cbn. intros [H1|H2].
    + now subst.
    + assumption.
  - rewrite Key.nin_list_cons in Hnin.
    destruct Hnin as [? Hnin].
    specialize (IHk Hnin).
    cbn. compare names.
    + intros [contra|contra].
      now subst. contradiction.
    + intros [contra|contra].
      now subst. contradiction.
Qed.

Theorem key_insert_unique (k: key) (a: name):
  unique k ->
  unique (key_insert_name k a).
Proof.
  intros.
  induction k.
  - cbn. easy.
  - destruct H as [H1 H2].
    specialize (IHk H2).
    cbn. compare names.
    cbn. split; auto.
    apply key_nin_insert; auto.
Qed.

(** ** Insertion and <<key_lookup_name>> *)
(******************************************************************************)
Lemma key_lookup_name_not_in1:
  forall (k:  key) (a: name),
    ~ a ∈ k -> key_lookup_name k a = None.
Proof.
  intros. induction k.
  - reflexivity.
  - cbn.
    rewrite Key.nin_list_cons in H.
    compare names.
    rewrite IHk.
    + reflexivity.
    + intuition.
Qed.

Lemma key_lookup_name_not_in2:
  forall (k:  key) (a: name),
    key_lookup_name k a = None -> ~ a ∈ k.
Proof.
  intros k a hyp.
  induction k.
  - cbv. easy.
  - rewrite Key.nin_list_cons.
    cbn in hyp.
    compare names.
    split.
    + assumption.
    + apply IHk.
      destruct (key_lookup_name k a).
      * inversion hyp.
      * reflexivity.
Qed.

Theorem key_lookup_name_not_in_iff:
  forall (k:  key) (a: name),
    ~ a ∈ k <-> key_lookup_name k a = None.
Proof.
  intros. split.
  - apply key_lookup_name_not_in1.
  - apply key_lookup_name_not_in2.
Qed.

Lemma key_lookup_name_in1:
  forall (k:  key) (a: name),
    a ∈ k -> {n: nat | key_lookup_name k a = Some n}.
Proof.
  introv Hin. induction k.
  - inversion Hin.
  - rewrite element_of_list_cons in Hin.
    cbn. compare names.
    + now (exists 0).
    + assert (Hink: a ∈ k) by now inversion Hin.
      destruct (IHk Hink) as [m Hm].
      rewrite Hm.
      now (exists (S m)).
Qed.

Lemma key_lookup_name_in2:
  forall (k:  key) (a: name) (n: nat),
    key_lookup_name k a = Some n -> a ∈ k.
Proof.
  intros k a.
  induction k; intros n Heq.
  - inversion Heq.
  - rewrite element_of_list_cons.
    cbn in Heq.
    compare names.
    + now left.
    + right.
      destruct (key_lookup_name k a);
        inversion Heq.
      now eapply IHk.
Qed.

Theorem key_lookup_in_name_iff: forall k a,
    (exists n, key_lookup_name k a = Some n) <-> a ∈ k.
Proof.
  intros. split.
  - intros [n H]. eauto using key_lookup_name_in2.
  - intro Hin. apply key_lookup_name_in1 in Hin.
    firstorder.
Qed.

Theorem key_lookup_name_decide:
  forall (k: key) (a: name),
    ((a ∈ k) * {n: nat | key_lookup_name k a = Some n}) +
      {~ a ∈ k /\ key_lookup_name k a = None}.
Proof.
  intros.
  destruct (key_is_name_in k a); [left|right].
  - split.
    + assumption.
    + auto using key_lookup_name_in1.
  - split.
    + assumption.
    + auto using key_lookup_name_not_in1.
Defined.

Ltac lookup_name_in_key k a :=
  let n := fresh "n" in
  let Hin := fresh "H_in" in
  let Hnin := fresh "H_not_in" in
  destruct (key_lookup_name_decide k a) as
    [[Hin [n H_key_lookup]] | [Hnin H_key_lookup]];
  try contradiction.

Tactic Notation "lookup" "name" constr(a) "in" "key" constr(k) :=
  lookup_name_in_key k a.

Goal forall (k: key) (a: name), a ∈ k \/ ~ a ∈ k.
Proof.
  intros.
  lookup name a in key k.
  - left. intuition.
  - now right.
Qed.

Lemma key_lookup_name_cons_0: forall a a' k,
    key_lookup_name (a :: k) a' = Some 0 ->
    a = a'.
Proof.
  introv Hlookup; cbn in *.
  compare names.
  lookup name a' in key k;
    rewrite H_key_lookup in Hlookup;
    now inversion Hlookup.
Qed.

Lemma key_lookup_name_cons_S: forall a x k ix,
    key_lookup_name (x :: k) a = Some (S ix) ->
    a <> x /\ key_lookup_name k a = Some ix.
Proof.
  introv HH.
  cbn in HH.
  destruct_eq_args a x.
  split. assumption.
  eauto using (Key.map_Some_inv S).
Qed.

Theorem key_lookup_name_cons: forall a k a' ix,
    key_lookup_name (a :: k) a' = Some ix ->
    (a' = a /\ ix = 0) \/
      (a' <> a /\ exists ix', ix = S ix' /\ key_lookup_name k a' = Some ix').
Proof.
  introv Hyp. destruct ix; [left|right].
  - apply key_lookup_name_cons_0 in Hyp.
    intuition.
  - apply key_lookup_name_cons_S in Hyp.
    intuition eauto.
Qed.

(** ** Insertion and <<key_lookup_ix>> *)
(******************************************************************************)
Lemma key_lookup_ix_in:
  forall (k:  key) (ix: nat) (a: name),
    key_lookup_index k ix = Some a -> a ∈ k.
Proof.
  introv Hin.
  generalize dependent ix.
  induction k; intros ix Hin.
  - inversion Hin.
  - destruct ix.
    + cbn in *. inversion Hin. now left.
    + cbn in Hin.
      rewrite element_of_list_cons.
      right. eauto.
Qed.

Lemma key_lookup_ix_Some1:
  forall (k:  key) (ix: nat) (a: name),
    key_lookup_index k ix = Some a -> contains_ix_upto ix k.
Proof.
  introv Hin.
  unfold contains_ix_upto.
  generalize dependent ix.
  induction k; intros ix Hin.
  - false.
  - destruct ix.
    + cbn. lia.
    + cbn. cbn in Hin.
      specialize (IHk ix Hin).
      lia.
Qed.

Lemma key_lookup_ix_Some2:
  forall (k:  key) (ix: nat),
    contains_ix_upto ix k ->
    {a:name | key_lookup_index k ix = Some a}.
Proof.
  unfold contains_ix_upto.
  intros.
  generalize dependent k.
  induction ix; intros k Hlt.
  - destruct k.
    + cbn in Hlt. lia.
    + cbn. eauto.
  - destruct k.
    + false. cbn in Hlt. lia.
    + cbn in Hlt.
      cbn.
      specialize (IHix k ltac:(lia)).
      assumption.
Qed.

Lemma key_lookup_ix_Some_iff:
  forall (k:  key) (ix: nat),
    contains_ix_upto ix k <->
      exists a, key_lookup_index k ix = Some a.
Proof.
  intros. split.
  - intro H; apply key_lookup_ix_Some2 in H. firstorder.
  - intros [a H]. eapply key_lookup_ix_Some1. eauto.
Qed.

Lemma key_lookup_ix_None1:
  forall (k:  key) (ix: nat),
    key_lookup_index k ix = None -> ~ (contains_ix_upto ix k).
Proof.
  introv Hin.
  unfold contains_ix_upto.
  generalize dependent ix.
  induction k; intros ix Hin.
  - cbn. lia.
  - destruct ix.
    + false.
    + cbn. cbn in Hin.
      specialize (IHk ix Hin).
      apply PeanoNat.Nat.le_ngt.
      lia.
Qed.

Lemma key_lookup_ix_None2:
  forall (k:  key) (ix: nat),
    ~ (contains_ix_upto ix k) ->
    key_lookup_index k ix = None.
Proof.
  introv Hin.
  unfold contains_ix_upto in *.
  generalize dependent ix.
  induction k; intros ix Hin.
  - reflexivity.
  - cbn in *. destruct ix.
    + contradict Hin. lia.
    + specialize (IHk ix ltac:(lia)).
      assumption.
Qed.

Theorem key_lookup_ix_decide:
  forall (k: key) (n: nat),
    ((contains_ix_upto n k) * {a: name | key_lookup_index k n = Some a}) +
      {~ contains_ix_upto n k /\ key_lookup_index k n = None}.
Proof.
  intros.
  destruct (key_is_ix_in k n); [left|right].
  - split.
    + assumption.
    + auto using key_lookup_ix_Some2.
  - split.
    + assumption.
    + auto using key_lookup_ix_None2.
Defined.

Ltac lookup_ix_in_key k n :=
  let a := fresh "a" in
  let Hcont := fresh "Hcont" in
  let H_key_lookup := fresh "H_key_lookup" in
  destruct (key_lookup_ix_decide k n) as
    [[Hcont [a H_key_lookup]] | [Hcont H_key_lookup]];
  try contradiction.

Tactic Notation "lookup" "index" constr(ix) "in" "key" constr(k) :=
  lookup_ix_in_key k ix.

Goal forall k (ix: nat), contains_ix_upto ix k \/ ~ contains_ix_upto ix k.
Proof.
  intros.
  lookup index ix in key k.
  - left. intuition.
  - now right.
Qed.

(** ** Properties of <<key_lookup_index>> *)
(******************************************************************************)
Lemma key_lookup_zero: forall a k ix,
    ix = 0 ->
    key_lookup_index (a :: k) ix = Some a.
Proof.
  intros. subst.
  reflexivity.
Qed.

Lemma key_lookup_index_S: forall k ix a,
    key_lookup_index k ix = Some a ->
    forall a', key_lookup_index (a' :: k) (S ix) = Some a.
Proof.
  intros.
  assumption.
Qed.

Lemma key_lookup_index_cons: forall a' a k ix,
    key_lookup_index (a' :: k) ix = Some a ->
    ix = 0 /\ a = a' \/
      exists ix', ix = S ix' /\ key_lookup_index k ix' = Some a.
Proof.
  introv Hin. destruct ix.
  - cbn in Hin. inversion Hin.
    left. now split.
  - cbn in Hin. right.
    exists ix. split; auto.
Qed.

Lemma key_bijection1: forall a k ix,
    key_lookup_name k a = Some ix ->
    key_lookup_index k ix = Some a.
Proof.
  intros.
  generalize dependent ix.
  induction k; intros ix Hix.
  - cbn in *. inversion Hix.
  - apply key_lookup_name_cons in Hix.
    destruct Hix as
      [ [Heq Hix0] | [Hneq [Hix [Heq Hlookup]]] ]; subst.
    + reflexivity.
    + cbn. auto.
Qed.

Lemma key_bijection2: forall a k ix,
    unique k ->
    key_lookup_index k ix = Some a ->
    key_lookup_name k a = Some ix.
Proof.
  introv Huniq Hix.
  generalize dependent ix.
  induction k; intros ix Hix.
  - cbn in Hix. inversion Hix.
  - cbn.
    apply key_lookup_index_cons in Hix.
    destruct Hix as [[Hix_zero Heq] | [ix' [Heq Hrest]]].
    + subst. compare names.
    + destruct Huniq as [Hnin Huniq].
      specialize (IHk Huniq).
      compare names.
      * false.
        apply key_lookup_ix_in in Hrest.
        contradiction.
      * rewrite (IHk ix' Hrest).
        reflexivity.
Qed.

Lemma key_bijection: forall a k ix,
    unique k ->
    key_lookup_index k ix = Some a <->
      key_lookup_name k a = Some ix.
Proof.
  intros.
  split; auto using key_bijection1, key_bijection2.
Qed.

Class PartialBijection {A B: Type}
  (f: A -> option B)
  (g: B -> option A) :=
  { pb_fwd: forall (a: A) (b: B),
      f a = Some b -> g b = Some a;
    pb_bwd: forall (b: B) (a: A),
      g b = Some a -> f a = Some b;

  }.

Lemma pb_iff `{PartialBijection A B f g}:
  forall (a: A) (b: B),
    f a = Some b <-> g b = Some a.
Proof.
  intros. split.
  apply pb_fwd.
  apply pb_bwd.
Qed.

Lemma pb_fwd_None `{PartialBijection A B f g}:
  forall (a: A),
    f a = None -> forall b, g b = Some a -> False.
Proof.
  introv H1 H2.
  apply pb_bwd in H2.
  congruence.
Qed.


Lemma pb_bwd_None `{PartialBijection A B f g}:
  forall (b: B),
    g b = None -> forall a, f a = Some b -> False.
Proof.
  introv H1 H2.
  apply pb_fwd in H2.
  congruence.
Qed.


Lemma pb_iff_None `{PartialBijection A B f g}:
  forall (a: A),
    f a = None <-> forall (b: B), ~ (g b = Some a).
Proof.
  intros. remember (f a) as fa.
  symmetry in Heqfa.
  destruct fa.
  - apply pb_fwd in Heqfa.
    split.
    inversion 1.
    intros contra.
    specialize (contra b Heqfa).
    contradiction.
  - specialize (pb_fwd_None a Heqfa).
    split; auto.
Qed.
