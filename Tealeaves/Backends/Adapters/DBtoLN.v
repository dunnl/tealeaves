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
From Tealeaves Require Export
  Backends.LN
  Backends.DB.DB
  Backends.Adapters.Key
  Classes.Kleisli.DecoratedTraversableMonad
  Functors.Option.

Import DecoratedTraversableMonad.UsefulInstances.

#[local] Generalizable Variables W T U.
#[local] Open Scope nat_scope.

(*|
============================
Operations
============================
|*)
Definition toLN_loc (k: key) '(depth, ix) : option LN :=
  if bound_b ix depth == true
  then
    Some (Bd ix)
  else
    map (F := option) Fr (getName k (ix - depth)).

Definition toLN
  `{Mapdt_inst: Mapdt nat T} (k: key): T nat -> option (T LN) :=
  mapdt (G := option) (toLN_loc k).

(*|
============================
Theory
============================
|*)
Section theory.

  Context
    `{Return_T: Return T}
    `{Map_T: Map T}
    `{Bind_TT: Bind T T}
    `{Traverse_T: Traverse T}
    `{Mapd_T: Mapd nat T}
    `{Bindt_TT: Bindt T T}
    `{Bindd_T: Bindd nat T T}
    `{Mapdt_T: Mapdt nat T}
    `{Binddt_TT: Binddt nat T T}
    `{! Compat_Map_Binddt nat T T}
    `{! Compat_Bind_Binddt nat T T}
    `{! Compat_Traverse_Binddt nat T T}
    `{! Compat_Mapd_Binddt nat T T}
    `{! Compat_Bindt_Binddt nat T T}
    `{! Compat_Bindd_Binddt nat T T}
    `{! Compat_Mapdt_Binddt nat T T}.

  Context
    `{Monad_inst: ! DecoratedTraversableMonad nat T}.

  Context
    `{Map_U: Map U}
    `{Bind_TU: Bind T U}
    `{Traverse_U: Traverse U}
    `{Mapd_U: Mapd nat U}
    `{Bindt_TU: Bindt T U}
    `{Bindd_TU: Bindd nat T U}
    `{Mapdt_U: Mapdt nat U}
    `{Binddt_TU: Binddt nat T U}
    `{! Compat_Map_Binddt nat T U}
    `{! Compat_Bind_Binddt nat T U}
    `{! Compat_Traverse_Binddt nat T U}
    `{! Compat_Mapd_Binddt nat T U}
    `{! Compat_Bindt_Binddt nat T U}
    `{! Compat_Bindd_Binddt nat T U}
    `{! Compat_Mapdt_Binddt nat T U}.

  Context
    `{Module_inst: ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.

  Lemma toLN_loc_None_iff:
    forall k d n, toLN_loc k (d, n) = None <-> n >= d /\ ~ (n - d < length k).
  Proof.
    intros.
    unfold toLN_loc.
    unfold bound_b, bound_within_b.
    replace (d + 0) with d by lia.
    remember (Nat.ltb n d) as b.
    symmetry in Heqb.
    destruct b.
    - cbn.
      rewrite PeanoNat.Nat.ltb_lt in Heqb.
      split; intro contra.
      + exfalso. inversion contra.
      + exfalso. lia.
    - cbn.
      rewrite PeanoNat.Nat.ltb_ge in Heqb.
      rewrite map_None_eq_iff.
      rewrite <- key_lookup_ix_None_iff.
      unfold contains_ix_upto.
      split; now auto.
  Qed.

  Lemma toLN_None_iff:
    forall k (t: U nat), toLN k t = None <-> ~ cl_at (length k) t.
  Proof.
    intros.
    rewrite cl_at_spec_not.
    unfold toLN.
    rewrite mapdt_option_None_spec.
    setoid_rewrite toLN_loc_None_iff.
    unfold cl_at_loc, bound_within.
    split; intros [e [a [Hin Hspec]]].
    - exists e. exists a; split; auto. lia.
    - exists e. exists a; split; auto. lia.
  Qed.

End theory.
