From Tealeaves Require Import
  Backends.LN.LN
  Backends.LN.Atom
  Backends.DB.DB
  Functors.List
  Functors.Option
  Classes.Categorical.ContainerFunctor
  Classes.Kleisli.DecoratedContainerFunctor.

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

Lemma map_some: forall `(f: A -> B) (x: option A)  y,
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

Fixpoint key_lookup_atom (k: key) (a: atom): option nat :=
  match k with
  | [] => None
  | x :: rest =>
      if a == x
      then Some 0
      else map S (key_lookup_atom rest a)
  end.

Fixpoint key_lookup_index (k: key) (ix: nat): option atom :=
  match k, ix with
  | nil, _ => None
  | cons a rest, 0 => Some a
  | cons a rest, S ix => key_lookup_index rest ix
  end.

Fixpoint key_lookup_atom_rec (k: key) (acc: nat) (a: atom): option nat :=
  match k with
  | nil => None
  | cons x rest =>
      if a == x then Some acc else key_lookup_atom_rec rest (S acc) a
  end.

Definition key_lookup_atom_alt: key -> atom -> option nat :=
  fun k => key_lookup_atom_rec k 0.

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

Definition contains_ix_upto (n: nat) (k: key): Prop :=
  n < length k.

Definition wf_DB `{ToCtxset nat T} (t: T nat) (k: key): Prop :=
  unique k /\ exists (gap: nat), closed_gap gap t /\ contains_ix_upto gap k.

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
Lemma key_lookup_atom_rec_spec (k: key) (a: atom) (n: nat):
  key_lookup_atom_rec k n a = map (fun m => m + n) (key_lookup_atom k a).
Proof.
  generalize dependent n.
  induction k; intro n.
  - reflexivity.
  - cbn. destruct (a == a0).
    + reflexivity.
    + rewrite (IHk (S n)).
      compose near (key_lookup_atom k a) on right.
      rewrite (fun_map_map).
      fequal. ext m. cbn. lia.
Qed.

Corollary key_lookup_atom_spec (k: key) (a: atom):
  key_lookup_atom_alt k a = key_lookup_atom k a.
Proof.
  unfold key_lookup_atom_alt.
  rewrite key_lookup_atom_rec_spec.
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

(** ** Insertion and <<key_lookup_atom>> *)
(******************************************************************************)
Lemma key_lookup_atom_not_in1:
  forall (k:  key) (a: atom),
    ~ a ∈ k -> key_lookup_atom k a = None.
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

Lemma key_lookup_atom_not_in2:
  forall (k:  key) (a: atom),
    key_lookup_atom k a = None -> ~ a ∈ k.
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
      destruct (key_lookup_atom k a).
      * inversion hyp.
      * reflexivity.
Qed.

Theorem key_lookup_atom_not_in_iff:
  forall (k:  key) (a: atom),
    ~ a ∈ k <-> key_lookup_atom k a = None.
Proof.
  intros. split.
  - apply key_lookup_atom_not_in1.
  - apply key_lookup_atom_not_in2.
Qed.

Lemma key_lookup_atom_in1:
  forall (k:  key) (a: atom),
    a ∈ k -> {n: nat | key_lookup_atom k a = Some n}.
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

Lemma key_lookup_atom_in2:
  forall (k:  key) (a: atom) (n: nat),
    key_lookup_atom k a = Some n -> a ∈ k.
Proof.
  intros k a.
  induction k; intros n Heq.
  - inversion Heq.
  - rewrite element_of_list_cons.
    cbn in Heq.
    compare atoms.
    + now left.
    + right.
      destruct (key_lookup_atom k a);
        inversion Heq.
      now eapply IHk.
Qed.

Theorem key_lookup_in_atom_iff: forall k a,
    (exists n, key_lookup_atom k a = Some n) <-> a ∈ k.
Proof.
  intros. split.
  - intros [n H]. eauto using key_lookup_atom_in2.
  - intro Hin. apply key_lookup_atom_in1 in Hin.
    firstorder.
Qed.

Theorem key_lookup_atom_decide:
  forall (k: key) (a: atom),
    ((a ∈ k) * {n: nat | key_lookup_atom k a = Some n}) +
      {~ a ∈ k /\ key_lookup_atom k a = None}.
Proof.
  intros.
  destruct (key_is_atom_in k a); [left|right].
  - split.
    + assumption.
    + auto using key_lookup_atom_in1.
  - split.
    + assumption.
    + auto using key_lookup_atom_not_in1.
Defined.

Ltac lookup_atom_in_key k a :=
  let n := fresh "n" in
  let Hin := fresh "H_in" in
  let Hnin := fresh "H_not_in" in
  destruct (key_lookup_atom_decide k a) as
    [[Hin [n H_key_lookup]] | [Hnin H_key_lookup]];
  try contradiction.

Tactic Notation "lookup" "atom" constr(a) "in" "key" constr(k) :=
  lookup_atom_in_key k a.

Goal forall k (a: atom), a ∈ k \/ ~ a ∈ k.
Proof.
  intros.
  lookup atom a in key k.
  - left. intuition.
  - now right.
Qed.

Lemma key_lookup_atom_cons_0: forall a a' k,
    key_lookup_atom (a :: k) a' = Some 0 ->
    a = a'.
Proof.
  introv Hlookup; cbn in *.
  compare atoms.
  lookup atom a' in key k;
    rewrite H_key_lookup in Hlookup;
    now inversion Hlookup.
Qed.

Lemma key_lookup_atom_cons_S: forall a x k ix,
    key_lookup_atom (x :: k) a = Some (S ix) ->
    a <> x /\ key_lookup_atom k a = Some ix.
Proof.
  introv HH.
  cbn in HH.
  destruct_eq_args a x.
  split. assumption.
  eauto using (map_some S).
Qed.

Theorem key_lookup_atom_cons: forall a k a' ix,
    key_lookup_atom (a :: k) a' = Some ix ->
    (a' = a /\ ix = 0) \/
      (a' <> a /\ exists ix', ix = S ix' /\ key_lookup_atom k a' = Some ix').
Proof.
  introv Hyp. destruct ix; [left|right].
  - apply key_lookup_atom_cons_0 in Hyp.
    intuition.
  - apply key_lookup_atom_cons_S in Hyp.
    intuition eauto.
Qed.

(** ** Insertion and <<key_lookup_ix>> *)
(******************************************************************************)
Lemma key_lookup_ix_in:
  forall (k:  key) (ix: nat) (a: atom),
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
  forall (k:  key) (ix: nat) (a: atom),
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
    {a:atom | key_lookup_index k ix = Some a}.
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
    ((contains_ix_upto n k) * {a: atom | key_lookup_index k n = Some a}) +
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

(** ** Properties of <<get_index>> *)
(******************************************************************************)
(*
Lemma get_index_rec_S (acc: nat) (a: atom) (k: key):
  get_index_rec (S acc) a k = map S (get_index_rec acc a k).
Proof.
  generalize dependent acc.
  induction k; intro.
  - cbn. reflexivity.
  - cbn. destruct_eq_args a a0.
Qed.

Lemma get_index_rec_plus (acc acc': nat) (a: atom) (k: key):
  get_index_rec (acc + acc') a k =
    map (fun acc => acc + acc') (get_index_rec acc a k).
Proof.
  generalize dependent acc.
  induction k; intro.
  - cbn. reflexivity.
  - cbn. destruct_eq_args a a0.
    rewrite get_index_rec_S.
    rewrite IHk.
    rewrite get_index_rec_S.
    compose near (get_index_rec acc a k).
    rewrite (fun_map_map).
    rewrite (fun_map_map).
    reflexivity.
Qed.

Lemma get_index_rec_plus_Some1 (acc acc': nat) (a: atom) (k: key) (ix: nat):
  get_index_rec acc a k = Some ix ->
    get_index_rec (acc + acc') a k = Some (ix + acc').
Proof.
  introv hyp.
  rewrite get_index_rec_plus.
  rewrite hyp.
  reflexivity.
Qed.

Lemma get_index_rec_plus_Some2 (acc acc': nat) (a: atom) (k: key) (ix: nat):
  get_index_rec (acc + acc') a k = Some (ix + acc') ->
  get_index_rec acc a k = Some ix.
Proof.
  rewrite get_index_rec_plus.
  apply (map_some (fun x => x + acc')).
  intros n m. lia.
Qed.
 *)

(** *** Keys known to contain a particular element *)
(******************************************************************************)
(*
Lemma get_index_rec_in (acc: nat) (x: atom) (k: key):
  x ∈ k -> exists ix, get_index_rec acc x k = Some ix.
Proof.
  intros.
  induction k.
  - false.
  - cbn. destruct_eq_args x a.
    + eauto.
    + autorewrite with tea_list in H.
      destruct H; [false|].
      specialize (IHk H).
      rewrite get_index_rec_S.
      destruct IHk as [ix hyp].
      exists (S ix).
      rewrite hyp.
      reflexivity.
Qed.

Corollary get_index_in (x: atom) (k: key):
  x ∈ k -> exists ix, get_index x k = Some ix.
Proof.
  unfold get_index.
  apply get_index_rec_in.
Qed.

Lemma get_index_rec_insert1 (acc: nat) (a: atom) (k: key) (x: atom):
  a = x ->
  exists (m: nat), get_index_rec acc a (key_insert_atom k x) = Some m.
Proof.
  intro Heq.
  subst.
  generalize dependent acc.
  induction k; intro acc.
  - cbn. destruct_eq_args x x. exists acc. reflexivity.
  - destruct (x == a).
    + subst. rewrite (insert_cons_eq a _ a Logic.eq_refl).
      cbn. destruct_eq_args a a. eauto.
    + rewrite insert_cons_neq. cbn.
      destruct_eq_args x a. eauto.
Qed.

Corollary get_index_insert1 (a: atom) (k: key) (x: atom):
  a = x ->
  exists (m: nat), get_index a (insert k x) = Some m.
Proof.
  apply get_index_rec_insert1.
Qed.


Lemma get_atom_rw2: forall a k ix,
    key_lookup_atom_rec (a :: k) (S ix) =
      key_lookup_atom_rec k ix.
Proof.
  intros.
  cbn.
  reflexivity.
Qed.

Lemma get_index_rec_neqS: forall a k n,
    n > 0 ->
    get_index_rec n a k <> Some 0.
Proof.
  intros.
  generalize dependent n.
  induction k; introv hyp.
  - cbn. easy.
  - cbn.
    specialize (IHk (S n) ltac:(lia)).
    destruct (a == a0).
    + inversion 1. lia.
    + assumption.
Qed.

Lemma get_index_Some_0: forall a x k,
    get_index a (x :: k) = Some 0 <->
      a = x.
Proof.
  introv.
  cbn.
  destruct_eq_args a x.
  split.
  - intro contra.
    apply get_index_rec_neqS in contra.
    false. lia.
  - inversion 1. false.
Qed.

*)

(** ** Properties of <<key_lookup_index>> *)
(******************************************************************************)
Lemma key_lookup_zero: forall a k ix,
    ix = 0 ->
    key_lookup_index (a :: k) ix = Some a.
Proof.
  intros. subst.
  reflexivity.
Qed.

(*
Lemma map_key_lookup_atom_Z: forall k a,
    map S (key_lookup_atom_alt k a) = Some 0 -> False.
Proof.
  intros.
  destruct (key_lookup_atom_alt k a).
  - cbn in H. inversion H.
  - inversion H.
Qed.
 *)

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
    key_lookup_atom k a = Some ix ->
    key_lookup_index k ix = Some a.
Proof.
  intros.
  generalize dependent ix.
  induction k; intros ix Hix.
  - cbn in *. inversion Hix.
  - apply key_lookup_atom_cons in Hix.
    destruct Hix as
      [ [Heq Hix0] | [Hneq [Hix [Heq Hlookup]]] ]; subst.
    + reflexivity.
    + cbn. auto.
Qed.

Lemma key_bijection2: forall a k ix,
    unique k ->
    key_lookup_index k ix = Some a ->
    key_lookup_atom k a = Some ix.
Proof.
  introv Huniq Hix.
  generalize dependent ix.
  induction k; intros ix Hix.
  - cbn in Hix. inversion Hix.
  - cbn.
    apply key_lookup_index_cons in Hix.
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
    key_lookup_index k ix = Some a <->
      key_lookup_atom k a = Some ix.
Proof.
  intros.
  split; auto using key_bijection1, key_bijection2.
Qed.
