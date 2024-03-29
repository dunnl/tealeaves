From Tealeaves Require Import
  Backends.LN.Atom
  Functors.List
  Functors.Option.

Open Scope nat_scope.

Import
  List.ListNotations
  ContainerFunctor.Notations.

Generalizable All Variables.

Lemma nin_list_cons:
  forall {A : Type} (a1 a2 : A) (xs : list A),
    ~ a1 ∈ (a2 :: xs) <-> a1 <> a2 /\ ~ a1 ∈ xs.
Proof.
  intros. rewrite in_list_cons.
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

Definition key :=
  list atom.

Fixpoint unique (l: list atom): Prop :=
  match l with
  | nil => True
  | cons a rest =>
      ~ (a ∈ rest) /\ unique rest
  end.

Definition key_is_atom_in (k: key) (a: atom):
  {a ∈ k} + {~ a ∈ k}.
Proof.
  induction k.
  - right. inversion 1.
  - pose (in_list_cons a a0 k).
    destruct (a == a0).
    + now (left; left).
    + destruct IHk.
      * now (left; right).
      * right. rewrite i.
        intros [contra|contra];
          contradiction.
Defined.

Ltac compare_atoms :=
    match goal with
    | H: context[?a == ?a'] |- _ =>
        destruct_eq_args a a'
    | |- context[?a == ?a'] =>
        destruct_eq_args a a'
    end.

Tactic Notation "compare" "atoms" := compare_atoms.

Fixpoint key_insert_atom (k: key) (a: atom): key :=
  match k with
  | nil => [a]
  | cons x rest =>
      if a == x then k else
        x :: key_insert_atom rest a
  end.

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

Lemma key_insert_unique (k: key) (a: atom):
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

Fixpoint key_lookup_atom_rec (k: key) (acc: nat) (a: atom): option nat :=
  match k with
  | nil => None
  | cons x rest =>
      if a == x then Some acc else key_lookup_atom_rec rest (S acc) a
  end.

Definition key_lookup_atom_alt: key -> atom -> option nat :=
  fun k => key_lookup_atom_rec k 0.

Fixpoint key_lookup_atom (k: key) (a: atom): option nat :=
  match k with
  | [] => None
  | x :: rest =>
      if a == x
      then Some 0
      else map S (key_lookup_atom rest a)
  end.

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

Lemma key_lookup_atom_spec (k: key) (a: atom):
  key_lookup_atom_alt k a = key_lookup_atom k a.
Proof.
  unfold key_lookup_atom_alt.
  rewrite key_lookup_atom_rec_spec.
  replace (fun m => m + 0) with (@id nat).
  now rewrite fun_map_id.
  ext m. unfold id. lia.
Qed.

Fixpoint key_lookup_index (k: key) (ix: nat): option atom :=
  match k, ix with
  | nil, _ => None
  | cons a rest, 0 => Some a
  | cons a rest, S ix => key_lookup_index rest ix
  end.

Lemma key_lookup_not_in1:
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

Lemma key_lookup_not_in2:
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

Lemma key_lookup_not_in_iff:
  forall (k:  key) (a: atom),
    ~ a ∈ k <-> key_lookup_atom k a = None.
Proof.
  intros. split.
  - apply key_lookup_not_in1.
  - apply key_lookup_not_in2.
Qed.

Lemma key_lookup_ix:
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
      rewrite in_list_cons.
      right. eauto.
Qed.

Lemma key_lookup_ix_length:
  forall (k:  key) (ix: nat),
    key_lookup_index k ix = None -> length k <= ix.
Proof.
  introv Hin.
  generalize dependent ix.
  induction k; intros ix Hin.
  - cbn in *. lia.
  - destruct ix.
    + inversion Hin.
    + cbn in *.
      specialize (IHk _ Hin).
      lia.
Qed.

Lemma key_lookup_in1:
  forall (k:  key) (a: atom),
    a ∈ k -> {n: nat | key_lookup_atom k a = Some n}.
Proof.
  introv Hin. induction k.
  - inversion Hin.
  - rewrite in_list_cons in Hin.
    cbn. compare atoms.
    + now (exists 0).
    + assert (Hink: a ∈ k) by now inversion Hin.
      destruct (IHk Hink) as [m Hm].
      rewrite Hm.
      now (exists (S m)).
Qed.

Lemma key_lookup_in2:
  forall (k:  key) (a: atom) (n: nat),
    key_lookup_atom k a = Some n -> a ∈ k.
Proof.
  intros k a.
  induction k; intros n Heq.
  - inversion Heq.
  - rewrite in_list_cons.
    cbn in Heq.
    compare atoms.
    + now left.
    + right.
      destruct (key_lookup_atom k a);
        inversion Heq.
      now eapply IHk.
Qed.

Lemma key_lookup:
  forall (k: key) (a: atom),
    {n: nat | key_lookup_atom k a = Some n /\ a ∈ k} +
      {~ a ∈ k /\ key_lookup_atom k a = None}.
Proof.
  intros.
  destruct (key_is_atom_in k a).
  - left. destruct (key_lookup_in1 k a e) as [m Hm].
    exists m. auto.
  - right. split. assumption.
    now apply key_lookup_not_in1.
Defined.

Ltac key_lookup k a :=
  let n := fresh "n" in
  let Hin := fresh "H_in" in
  let Hnin := fresh "H_not_in" in
  destruct (key_lookup k a) as
    [[n [H_key_lookup Hin]] | [Hnin H_key_lookup]].

Tactic Notation "lookup" constr(a) "in" "key" constr(k) := key_lookup k a.

Goal forall k (a: atom), a ∈ k \/ ~ a ∈ k.
Proof.
  intros.
  lookup a in key k.
  - now left.
  - now right.
Qed.


(** ** Properties of <<insert>> *)
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

Lemma get_index_Some_S:
  forall (a x : atom) (k : list atom) (n : nat),
    get_index a (x :: k) = Some (S n) -> a <> x.
Proof.
  introv.
  cbn.
  destruct_eq_args a x.
Qed.
*)

(** ** Properties of <<get_atom>> *)
(******************************************************************************)
Lemma key_lookup_zero: forall a k ix,
    ix = 0 ->
    key_lookup_index (a :: k) ix = Some a.
Proof.
  intros. subst.
  reflexivity.
Qed.

Lemma key_lookup_hd: forall a a' k,
    key_lookup_atom (a :: k) a' = Some 0 ->
    a = a'.
Proof.
  introv Hlookup; cbn in *.
  compare atoms.
  lookup a' in key k;
    rewrite H_key_lookup in Hlookup;
    now inversion Hlookup.
Qed.

(*
Lemma key_lookup_index_cons: forall a x k ix,
    key_lookup_index a (x :: k) = Some (S ix) ->
    get_index a k = Some ix.
Proof.
  introv HH.
  assert (Hneq: a <> x) by eauto using get_index_Some_S.
  cbn in *.
  destruct_eq_args a x.
  rewrite get_index_rec_S in HH.
  unfold get_index.
  apply (map_some S).
  lia.
  assumption.
Qed.
*)

Lemma map_key_lookup_atom_S: forall k a ix,
    map S (key_lookup_atom k a) = Some (S ix) ->
    key_lookup_atom k a = Some ix.
Proof.
  intros.
  destruct (key_lookup_atom k a).
  - cbn in H. inversion H. reflexivity.
  - inversion H.
Qed.

Lemma map_key_lookup_atom_Z: forall k a,
    map S (key_lookup_atom_alt k a) = Some 0 -> False.
Proof.
  intros.
  destruct (key_lookup_atom_alt k a).
  - cbn in H. inversion H.
  - inversion H.
Qed.

Lemma map_key_lookup_cons: forall a k a' ix,
    key_lookup_atom (a :: k) a' = Some ix ->
    (ix = 0 /\ a = a') \/
      exists ix', ix = S ix' /\ key_lookup_atom k a' = Some ix'.
Proof.
  introv Hyp. cbn in Hyp.
  compare atoms.
  - left. inversion Hyp. intuition.
  - right. destruct ix.
    + false. destruct (key_lookup_atom k a').
      * inversion Hyp.
      * inversion Hyp.
    + apply (map_key_lookup_atom_S k a' ix) in Hyp.
      exists ix. split.  reflexivity. assumption.
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
    key_lookup_atom k a = Some ix ->
    key_lookup_index k ix = Some a.
Proof.
  intros.
  generalize dependent ix.
  induction k; intros ix Hix.
  - cbn in *. inversion Hix.
  - apply map_key_lookup_cons in Hix.
    destruct Hix as
      [ [Hix1 Hix2] | [ix' [Heq Hlookup] ] ]; subst.
    + subst. reflexivity.
    + subst.
      specialize (IHk _ Hlookup).
      now apply key_lookup_index_S.
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
      * false. apply key_lookup_ix in Hrest. contradiction.
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
