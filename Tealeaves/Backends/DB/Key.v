From Tealeaves Require Import
  Backends.LN.Atom
  Functors.List
  Functors.Option.

Open Scope nat_scope.
Import
  List.ListNotations
  ContainerFunctor.Notations.

Generalizable All Variables.

Definition key :=
  list atom.

Fixpoint insert (k: key) (a: atom): key :=
  match k with
  | nil => [a]
  | cons x rest =>
      if a == x then k else x :: (insert rest a)
                              (* (k ++ [a]) *)
  end.

Fixpoint get_index_rec (acc: nat) (a: atom) (k: key): option nat :=
  match k with
  | nil => None
  | cons x rest =>
      if a == x then Some acc else get_index_rec (S acc) a rest
  end.

Definition get_index: atom -> key -> option nat :=
  get_index_rec 0.

Fixpoint get_atom (k: key) (ix: nat): option atom :=
  match k, ix with
  | nil, _ => None
  | cons a rest, 0 => Some a
  | cons a rest, S ix => get_atom rest ix
  end.

(** ** Properties of <<insert>> *)
(******************************************************************************)
Lemma insert_cons_eq: forall a k x,
    a = x ->
    insert (a :: k) x = a :: k.
Proof.
  intros. cbn.
  destruct_eq_args x a.
Qed.

Lemma insert_cons_neq: forall a k x,
    a <> x ->
    insert (a :: k) x = a :: insert k x.
Proof.
  intros. cbn.
  destruct_eq_args x a.
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

(** ** Properties of <<get_index>> *)
(******************************************************************************)
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

(** *** Keys known to contain a particular element *)
(******************************************************************************)
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
  exists (m: nat), get_index_rec acc a (insert k x) = Some m.
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
    get_atom (a :: k) (S ix) = get_atom k ix.
Proof.
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

(** ** Properties of <<get_atom>> *)
(******************************************************************************)
Lemma get_atom_0: forall a k ix,
    ix = 0 ->
    get_atom (a :: k) ix = Some a.
Proof.
  intros. subst.
  reflexivity.
Qed.

Lemma get_index_cons: forall a x k ix,
    get_index a (x :: k) = Some (S ix) ->
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

Lemma key_bijection1: forall a k ix,
    get_index a k = Some ix ->
    get_atom k ix = Some a.
Proof.
  intros.
  generalize dependent k.
  induction ix.
  - intro k. cbn. intro H.
    destruct k.
    + inversion H.
    + apply get_index_Some_0 in H.
      subst. reflexivity.
  - intros k H.
    destruct k.
    + inversion H.
    + rename a0 into x.
      rewrite get_atom_rw2.
      apply IHix.
      eapply get_index_cons.
      eassumption.
Qed.

Lemma key_bijection2: forall a k ix,
    (* uniq k -> *)
    get_atom k ix = Some a ->
    get_index a k = Some ix.
Proof.
  intros.
  generalize dependent ix.
  induction k.
  - cbn. inversion 1.
  - introv hyp.
    destruct ix.
    + rewrite get_atom_0 in hyp; auto.
      inversion hyp.
      now apply get_index_Some_0.
    + rewrite get_atom_rw2 in hyp.
      apply IHk in hyp.
Abort.
