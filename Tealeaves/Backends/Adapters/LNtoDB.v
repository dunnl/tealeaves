(*|
############################################################
Translating between locally nameless and de Bruijn indices
############################################################

We reason about a translation between syntax with de Bruijn indices
and locally nameless variables. This consists of a function which,
given a locally closed term t, outputs a term of the same shape whose
leaves are de Bruijn indices and a "key": some arbitrary permutation
of the names of free variables in t. Another function accepts a key
and a de Bruijn term and computes a locally nameless term of the same
shape. The two functions are shown to be inverses.

.. contents:: Table of Contents :depth: 2

============================
Imports and setup
============================

Since we are using the Kleisli typeclass hierarchy, we import modules
under the namespaces ``Classes.Kleisli`` and ``Theory.Kleisli.``
|*)
From Tealeaves Require Import
  Backends.LN
  Backends.DB.DB
  Backends.Adapters.Key
  Functors.Option.

Import LN.Notations.

Import DecoratedTraversableMonad.UsefulInstances.

#[local] Generalizable Variables W T U.
#[local] Open Scope nat_scope.

(*|
============================
Translation operations
============================
|*)
Definition toDB_loc (k: key) '(depth, l) : option nat :=
  match l with
  | Bd n => Some n
  | Fr x => map (fun ix => ix + depth) (key_lookup_atom k x)
  end.

Fixpoint toLNkey_list (l: list LN): key :=
  match l with
  | [] => nil
  | (Bd n :: rest) => toLNkey_list rest
  | (Fr x :: rest) => key_insert_atom (toLNkey_list rest) x
  end.

(*|
============================
Simplification support
============================
|*)
Lemma toDB_loc_rw1 (k: key) (depth: nat) (n: nat):
  toDB_loc k (depth, Bd n) = Some n.
Proof.
  reflexivity.
Qed.

Lemma toDB_loc_rw2 (k: key) (depth: nat) (x: atom):
  toDB_loc k (depth, Fr x) =
    map (fun ix => ix + depth) (key_lookup_atom k x).
Proof.
  reflexivity.
Qed.

(*|
============================
Properties of toLNkey
============================
|*)
Lemma toLNkey_unique: forall l,
    unique (toLNkey_list l).
Proof.
  intros l. induction l as [|[x|n] rest].
  - exact I.
  - now apply key_insert_unique.
  - cbn. assumption.
Qed.

Lemma toLNkey_bijection: forall l ix a,
    key_lookup_index (toLNkey_list l) ix = Some a <->
      key_lookup_atom (toLNkey_list l) a = Some ix.
Proof.
  intros.
  apply key_bijection.
  apply toLNkey_unique.
Qed.

(*|
============================
Global operations
============================
|*)
Definition toDB_from_key
  `{Mapdt_inst: Mapdt nat T} (k: key): T LN -> option (T nat) :=
  mapdt (G := option) (toDB_loc k).

Definition toLNkey
  `{Traverse_inst: Traverse T} (t: T LN): key :=
  toLNkey_list (tolist t).

Definition toDB
  `{Traverse_inst: Traverse T}
  `{Mapdt_inst: Mapdt nat T} (t: T LN): option (T nat) :=
  toDB_from_key (toLNkey t) t.
