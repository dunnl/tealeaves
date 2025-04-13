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
  Classes.Kleisli.DecoratedTraversableFunctor
  Functors.Option.

#[local] Generalizable Variables W T U.
#[local] Open Scope nat_scope.

(*|
============================
Operations
============================
|*)
Definition toLN_loc (k: key) '(depth, ix) : option LN :=
  if bound ix depth == true
  then
    Some (Bd ix)
  else
    map (F := option) Fr (key_lookup_index k (ix - depth)).

Definition toLN_from_key
  `{Mapdt_inst: Mapdt nat T} (k: key): T nat -> option (T LN) :=
  mapdt (G := option) (toLN_loc k).
