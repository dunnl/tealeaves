From Tealeaves Require Import
  Backends.LN.LN
  Backends.Common.Names
  Backends.DB.DB
  Functors.List
  Functors.Option
  Classes.Categorical.ContainerFunctor
  Classes.Kleisli.DecoratedContainerFunctor
  Misc.PartialBijection.

From Coq Require Import Logic.Decidable.

Open Scope nat_scope.

Import
  List.ListNotations
  ContainerFunctor.Notations.

Generalizable All Variables.

(** * Miscellaneous lemmas *)
(******************************************************************************)
Lemma nin_list_cons:
  forall {A : Type} (a1 a2 : A) (xs : list A),
    ~ a1 ∈ (a2 :: xs) <-> a1 <> a2 /\ ~ a1 ∈ xs.
Proof.
  intros. rewrite element_of_list_cons.
  intuition.
Qed.

Lemma map_Some_inv: forall `(f: A -> B) (x: option A)  y,
    (forall a a', f a = f a' -> a = a') ->
    map f x = Some (f y) ->
    x = Some y.
Proof.
  introv Hinj Heq. destruct x.
  - inversion Heq. fequal.
    apply Hinj. assumption.
  - inversion Heq.
Qed.

Ltac compare_atoms :=
    match goal with
    | H: context[?a == ?a'] |- _ =>
        destruct_eq_args a a'
    | |- context[?a == ?a'] =>
        destruct_eq_args a a'
    end.

#[global] Tactic Notation "compare" "atoms" := compare_atoms.

(** * Definition of <<key>> and main operations *)
(******************************************************************************)
Definition key :=
  list atom.

(** ** Insertion and lookup *)
(******************************************************************************)
Fixpoint key_insert_atom (k: key) (a: atom): key :=
  match k with
  | nil => [a]
  | cons x rest =>
      if a == x then k else
        x :: key_insert_atom rest a
  end.

Fixpoint getIndex (k: key) (a: atom): option nat :=
  match k with
  | [] => None
  | x :: rest =>
      if a == x
      then Some 0
      else map S (getIndex rest a)
  end.

Fixpoint getName (k: key) (ix: nat): option atom :=
  match k, ix with
  | nil, _ => None
  | cons a rest, 0 => Some a
  | cons a rest, S ix => getName rest ix
  end.

Fixpoint getIndex_rec (k: key) (acc: nat) (a: atom): option nat :=
  match k with
  | nil => None
  | cons x rest =>
      if a == x then Some acc else getIndex_rec rest (S acc) a
  end.

Definition getIndex_alt: key -> atom -> option nat :=
  fun k => getIndex_rec k 0.

(** ** Well-formedness predicates *)
(******************************************************************************)
Fixpoint unique (l: list atom): Prop :=
  match l with
  | nil => True
  | cons a rest =>
      ~ (a ∈ rest) /\ unique rest
  end.

Definition wf_LN
  `{ToSubset T} (t: T LN) (k: key): Prop :=
  unique k /\ forall (x: atom), Fr x ∈ t -> x ∈ k.

Definition resolves_gap (gap: nat) (k: key): Prop :=
  gap <= length k.

Definition contains_ix_upto (n: nat) (k: key): Prop :=
  n < length k.

Lemma resolves_gap_spec: forall (gap: nat) (k: key),
    resolves_gap gap k <-> contains_ix_upto (gap - 1) k \/ gap = 0.
Proof.
  intros.
  unfold resolves_gap, contains_ix_upto.
  split.
  - lia.
  - lia.
Qed.

Lemma elt_decidable: forall (a: atom) (l: list atom),
    decidable (a ∈ l).
Proof.
  intros.
  induction l.
  - right.
    rewrite element_of_list_nil.
    easy.
  - destruct IHl as [Huniq | Hnuniq].
    + left. simpl_list. tauto.
    + destruct (a == a0).
      * subst. left.
        simpl_list. now left.
      * right.
        simpl_list.
        tauto.
Qed.

Lemma unique_decidable: forall (l: list atom),
    decidable (unique l).
Proof.
  intros.
  induction l.
  - left. cbn. easy.
  - destruct IHl as [Huniq | Hnuniq].
    + cbn. destruct (elt_decidable a l).
      * right. tauto.
      * left. tauto.
    + right. cbn.
      tauto.
Qed.

(*
Definition wf_DB `{ToCtxset nat T} (t: T nat) (k: key): Prop :=
  unique k /\ exists (gap: nat), cl_at gap t /\ resolves_gap gap k.
*)

(** * Misc *)
(******************************************************************************)
Definition key_is_atom_in (k: key) (a: atom):
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

(** * Lemmas about <<key_insert_atom>> *)
(******************************************************************************)

(** ** Rewriting *)
(******************************************************************************)
Lemma insert_cons_eq: forall a k x,
    a = x ->
    key_insert_atom (a :: k) x = a :: k.
Proof.
  intros. cbn.
  destruct_eq_args x a.
Qed.

Lemma insert_cons_neq: forall a k x,
    a <> x ->
    key_insert_atom (a :: k) x = a :: key_insert_atom k x.
Proof.
  intros. cbn.
  destruct_eq_args x a.
Qed.

(** ** Alternative spec *)
(******************************************************************************)
Lemma getIndex_rec_spec (k: key) (a: atom) (n: nat):
  getIndex_rec k n a = map (fun m => m + n) (getIndex k a).
Proof.
  generalize dependent n.
  induction k; intro n.
  - reflexivity.
  - cbn. destruct (a == a0).
    + reflexivity.
    + rewrite (IHk (S n)).
      compose near (getIndex k a) on right.
      rewrite (fun_map_map).
      fequal. ext m. cbn. lia.
Qed.

Corollary getIndex_spec (k: key) (a: atom):
  getIndex_alt k a = getIndex k a.
Proof.
  unfold getIndex_alt.
  rewrite getIndex_rec_spec.
  replace (fun m => m + 0) with (@id nat).
  now rewrite fun_map_id.
  ext m. unfold id. lia.
Qed.

(** ** Insertion and <<unique>> *)
(******************************************************************************)
Lemma key_nin_insert: forall k a a',
    a <> a' ->
    ~ a ∈ k ->
    ~ a ∈ key_insert_atom k a'.
Proof.
  introv Hneq Hnin. induction k.
  - cbn. intros [H1|H2].
    + now subst.
    + assumption.
  - rewrite nin_list_cons in Hnin.
    destruct Hnin as [? Hnin].
    specialize (IHk Hnin).
    cbn. compare atoms.
    + intros [contra|contra].
      now subst. contradiction.
    + intros [contra|contra].
      now subst. contradiction.
Qed.

Theorem key_insert_unique (k: key) (a: atom):
  unique k ->
  unique (key_insert_atom k a).
Proof.
  intros.
  induction k.
  - cbn. easy.
  - destruct H as [H1 H2].
    specialize (IHk H2).
    cbn. compare atoms.
    cbn. split; auto.
    apply key_nin_insert; auto.
Qed.

(** ** Insertion and <<getIndex>> *)
(******************************************************************************)
Lemma getIndex_not_in1:
  forall (k:  key) (a: atom),
    ~ a ∈ k -> getIndex k a = None.
Proof.
  intros. induction k.
  - reflexivity.
  - cbn.
    rewrite nin_list_cons in H.
    compare atoms.
    rewrite IHk.
    + reflexivity.
    + intuition.
Qed.

Lemma getIndex_not_in2:
  forall (k:  key) (a: atom),
    getIndex k a = None -> ~ a ∈ k.
Proof.
  intros k a hyp.
  induction k.
  - cbv. easy.
  - rewrite nin_list_cons.
    cbn in hyp.
    compare atoms.
    split.
    + assumption.
    + apply IHk.
      destruct (getIndex k a).
      * inversion hyp.
      * reflexivity.
Qed.

Theorem getIndex_not_in_iff:
  forall (k:  key) (a: atom),
    ~ a ∈ k <-> getIndex k a = None.
Proof.
  intros. split.
  - apply getIndex_not_in1.
  - apply getIndex_not_in2.
Qed.

Lemma getIndex_in1:
  forall (k:  key) (a: atom),
    a ∈ k -> {n: nat | getIndex k a = Some n}.
Proof.
  introv Hin. induction k.
  - inversion Hin.
  - rewrite element_of_list_cons in Hin.
    cbn. compare atoms.
    + now (exists 0).
    + assert (Hink: a ∈ k) by now inversion Hin.
      destruct (IHk Hink) as [m Hm].
      rewrite Hm.
      now (exists (S m)).
Qed.

Lemma getIndex_in2:
  forall (k:  key) (a: atom) (n: nat),
    getIndex k a = Some n -> a ∈ k.
Proof.
  intros k a.
  induction k; intros n Heq.
  - inversion Heq.
  - rewrite element_of_list_cons.
    cbn in Heq.
    compare atoms.
    + now left.
    + right.
      destruct (getIndex k a);
        inversion Heq.
      now eapply IHk.
Qed.

Theorem key_lookup_in_atom_iff: forall k a,
    (exists n, getIndex k a = Some n) <-> a ∈ k.
Proof.
  intros. split.
  - intros [n H]. eauto using getIndex_in2.
  - intro Hin. apply getIndex_in1 in Hin.
    firstorder.
Qed.

Theorem getIndex_decide:
  forall (k: key) (a: atom),
    ((a ∈ k) * {n: nat | getIndex k a = Some n}) +
      {~ a ∈ k /\ getIndex k a = None}.
Proof.
  intros.
  destruct (key_is_atom_in k a); [left|right].
  - split.
    + assumption.
    + auto using getIndex_in1.
  - split.
    + assumption.
    + auto using getIndex_not_in1.
Defined.

Ltac lookup_atom_in_key k a :=
  let n := fresh "n" in
  let Hin := fresh "H_in" in
  let Hnin := fresh "H_not_in" in
  destruct (getIndex_decide k a) as
    [[Hin [n H_key_lookup]] | [Hnin H_key_lookup]];
  try contradiction.

Tactic Notation "lookup" "atom" constr(a) "in" "key" constr(k) :=
  lookup_atom_in_key k a.

Goal forall (k: key) (a: atom), a ∈ k \/ ~ a ∈ k.
Proof.
  intros.
  lookup atom a in key k.
  - left. intuition.
  - now right.
Qed.

Lemma getIndex_cons_0: forall a a' k,
    getIndex (a :: k) a' = Some 0 ->
    a = a'.
Proof.
  introv Hlookup; cbn in *.
  compare atoms.
  lookup atom a' in key k;
    rewrite H_key_lookup in Hlookup;
    now inversion Hlookup.
Qed.

Lemma getIndex_cons_S: forall a x k ix,
    getIndex (x :: k) a = Some (S ix) ->
    a <> x /\ getIndex k a = Some ix.
Proof.
  introv HH.
  cbn in HH.
  destruct_eq_args a x.
  split. assumption.
  eauto using (map_Some_inv S).
Qed.

Theorem getIndex_cons: forall a k a' ix,
    getIndex (a :: k) a' = Some ix ->
    (a' = a /\ ix = 0) \/
      (a' <> a /\ exists ix', ix = S ix' /\ getIndex k a' = Some ix').
Proof.
  introv Hyp. destruct ix; [left|right].
  - apply getIndex_cons_0 in Hyp.
    intuition.
  - apply getIndex_cons_S in Hyp.
    intuition eauto.
Qed.

(** ** Insertion and <<key_lookup_ix>> *)
(******************************************************************************)
Lemma key_lookup_ix_in:
  forall (k:  key) (ix: nat) (a: atom),
    getName k ix = Some a -> a ∈ k.
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
  forall (k:  key) (ix: nat) (a: atom),
    getName k ix = Some a -> contains_ix_upto ix k.
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
    {a:atom | getName k ix = Some a}.
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
      exists a, getName k ix = Some a.
Proof.
  intros. split.
  - intro H; apply key_lookup_ix_Some2 in H. firstorder.
  - intros [a H]. eapply key_lookup_ix_Some1. eauto.
Qed.

Lemma key_lookup_ix_None1:
  forall (k:  key) (ix: nat),
    getName k ix = None -> ~ (contains_ix_upto ix k).
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
    getName k ix = None.
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

Lemma key_lookup_ix_None_iff:
  forall (k:  key) (ix: nat),
    ~ (contains_ix_upto ix k) <->
    getName k ix = None.
Proof.
  intros; split;
    auto using key_lookup_ix_None1, key_lookup_ix_None2.
Qed.

Theorem key_lookup_ix_decide:
  forall (k: key) (n: nat),
    ((contains_ix_upto n k) * {a: atom | getName k n = Some a}) +
      {~ contains_ix_upto n k /\ getName k n = None}.
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

(** ** Properties of <<getName>> *)
(******************************************************************************)
Lemma key_lookup_zero: forall a k ix,
    ix = 0 ->
    getName (a :: k) ix = Some a.
Proof.
  intros. subst.
  reflexivity.
Qed.

Lemma getName_S: forall k ix a,
    getName k ix = Some a ->
    forall a', getName (a' :: k) (S ix) = Some a.
Proof.
  intros.
  assumption.
Qed.

Lemma getName_cons: forall a' a k ix,
    getName (a' :: k) ix = Some a ->
    ix = 0 /\ a = a' \/
      exists ix', ix = S ix' /\ getName k ix' = Some a.
Proof.
  introv Hin. destruct ix.
  - cbn in Hin. inversion Hin.
    left. now split.
  - cbn in Hin. right.
    exists ix. split; auto.
Qed.

Lemma key_bijection1: forall a k ix,
    getIndex k a = Some ix ->
    getName k ix = Some a.
Proof.
  intros.
  generalize dependent ix.
  induction k; intros ix Hix.
  - cbn in *. inversion Hix.
  - apply getIndex_cons in Hix.
    destruct Hix as
      [ [Heq Hix0] | [Hneq [Hix [Heq Hlookup]]] ]; subst.
    + reflexivity.
    + cbn. auto.
Qed.

Lemma key_bijection2: forall a k ix,
    unique k ->
    getName k ix = Some a ->
    getIndex k a = Some ix.
Proof.
  introv Huniq Hix.
  generalize dependent ix.
  induction k; intros ix Hix.
  - cbn in Hix. inversion Hix.
  - cbn.
    apply getName_cons in Hix.
    destruct Hix as [[Hix_zero Heq] | [ix' [Heq Hrest]]].
    + subst. compare atoms.
    + destruct Huniq as [Hnin Huniq].
      specialize (IHk Huniq).
      compare atoms.
      * false.
        apply key_lookup_ix_in in Hrest.
        contradiction.
      * rewrite (IHk ix' Hrest).
        reflexivity.
Qed.

Lemma key_bijection: forall a k ix,
    unique k ->
    getName k ix = Some a <->
      getIndex k a = Some ix.
Proof.
  intros.
  split; auto using key_bijection1, key_bijection2.
Qed.
