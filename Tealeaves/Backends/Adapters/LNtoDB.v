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
  Functors.Option.

Import LN.Notations.

Import DecoratedTraversableMonad.UsefulInstances.

From Coq Require Import Logic.Decidable.

#[local] Generalizable Variables W T U.
#[local] Open Scope nat_scope.

(*|
============================
Translation operations
============================
|*)
Definition toDB_loc (k: key) '(depth, l) : option nat :=
  match l with
  | Bd n => if Nat.ltb n depth then Some n else None
  | Fr x => map (fun ix => ix + depth) (key_lookup_atom k x)
  end.

Fixpoint LNtokey_list (l: list LN): key :=
  match l with
  | [] => nil
  | (Bd n :: rest) => LNtokey_list rest
  | (Fr x :: rest) => key_insert_atom (LNtokey_list rest) x
  end.

Lemma toDB_loc_None_iff:
  forall k d l, toDB_loc k (d, l) = None <->
             (exists x, l = Fr x /\ ~ x ∈ k) \/ (exists n, l = Bd n /\ n >= d).
Proof.
  intros.
  unfold toDB_loc.
  destruct l as [x | n].
  - rewrite map_None_eq_iff.
    setoid_rewrite key_lookup_atom_not_in_iff.
    firstorder.
    now inversion H.
    now inversion H.
  - split; intro contra.
    + assert (Nat.ltb n d = false).
      { now destruct (Nat.ltb n d). }
      apply PeanoNat.Nat.ltb_ge in H.
      right. exists n. auto.
    + destruct contra as [[x [contra rest]] | [n' [Heq contra]]].
      * false.
      * inversion Heq; subst.
        apply PeanoNat.Nat.ltb_ge in contra.
        rewrite contra.
        reflexivity.
Qed.

(*|
============================
Simplification support
============================
|*)
Lemma toDB_loc_rw1 (k: key) (depth: nat) (n: nat):
  n < depth -> toDB_loc k (depth, Bd n) = Some n.
Proof.
  intros. cbn.
  destruct depth.
  - false. lia.
  - apply PeanoNat.Nat.leb_le in H.
    cbn in H.
    rewrite H.
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
Properties of LNtokey
============================
|*)
Lemma LNtokey_unique: forall l,
    unique (LNtokey_list l).
Proof.
  intros l. induction l as [|[x|n] rest].
  - exact I.
  - now apply key_insert_unique.
  - cbn. assumption.
Qed.

Lemma LNtokey_bijection: forall l ix a,
    key_lookup_index (LNtokey_list l) ix = Some a <->
      key_lookup_atom (LNtokey_list l) a = Some ix.
Proof.
  intros.
  apply key_bijection.
  apply LNtokey_unique.
Qed.

(*|
============================
Global operations
============================
|*)
Definition toDB
  `{Mapdt_inst: Mapdt nat T} (k: key): T LN -> option (T nat) :=
  mapdt (G := option) (toDB_loc k).

Definition LNtokey
  `{Traverse_inst: Traverse T} (t: T LN): key :=
  LNtokey_list (tolist t).

Definition toDB_default_key
  `{Traverse_inst: Traverse T}
  `{Mapdt_inst: Mapdt nat T} (t: T LN): option (T nat) :=
  toDB (LNtokey t) t.

(*|
=================================
Properties of <<toDB>>
=================================
|*)
Section theory.

  Context
    `{Return_T: Return T}
    `{Map_T: Map T}
    `{Bind_TT: Bind T T}
    `{Traverse_T: Traverse T}
    `{Mapd_T: Mapd nat T}
    `{Bindt_TT: Bindt T T}
    `{Bindd_T: Bindd nat T}
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
    `{Monad_inst: ! DecoratedTraversableMonad nat T}
    `{Module_inst: ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.

  Definition scoped_key (k: key) (t: U LN) :=
    forall x: atom, x ∈ free t -> x ∈ k.

  Definition scoped_key_loc (k: key): LN -> Prop :=
    fun v => match v with
          | Bd _ => True
          | Fr x => x ∈ k
          end.

  Lemma decidable_scoped_key_loc (k: key) (v: LN):
    decidable (scoped_key_loc k v).
  Proof.
    unfold decidable.
    unfold scoped_key_loc.
    destruct v as [x | n].
    - destruct (elt_decidable x k); auto.
    - now left.
  Qed.

  Lemma scoped_key_equiv (k: key):
    scoped_key k = Forall (scoped_key_loc k).
  Proof.
    ext t.
    rewrite (forall_iff_eq (T := U)).
    unfold scoped_key_loc.
    unfold scoped_key. propext.
    - intros Hyp v Hvin.
      destruct v as [x | n].
      + setoid_rewrite in_free_iff in Hyp.
        auto.
      + trivial.
    - intros Hyp x Hin.
      rewrite in_free_iff in Hin.
      apply (Hyp (Fr x) Hin).
  Qed.

  Lemma scoped_key_decidable: forall (k: key),
      decidable_pred (scoped_key k).
  Proof.
    intros.
    rewrite scoped_key_equiv.
    apply decidable_Forall.
    intro t.
    apply decidable_scoped_key_loc.
  Qed.

  Lemma LCloc_decidable (gap: nat):
      decidable_pred (lc_loc gap).
  Proof.
    unfold lc_loc.
    unfold decidable_pred.
    intros [d v].
    destruct v.
    - now left.
    - unfold decidable.
      compare naturals n and d.
  Qed.

  Lemma LC_decidable:
      decidable_pred LC.
  Proof.
    unfold LC.
    unfold LCn.
    apply decidable_Forall_ctx.
    apply LCloc_decidable.
  Qed.

  Lemma toDB_None_iff: forall k,
    forall (t: U LN), toDB k t = None <->
                   (exists (a: atom), a ∈ free t /\ ~ a ∈ k) \/
                     (exists (depth n: nat), (depth, Bd n) ∈d t /\ n >= depth).
  Proof.
    intros.
    unfold toDB.
    rewrite mapdt_option_None_spec.
    setoid_rewrite in_free_iff.
    setoid_rewrite toDB_loc_None_iff.
    split.
    - intros [e [a [Hint rest]]].
      destruct rest as [ [x [HeqX xNotIn]] | [n [Heq Hgeq]]].
      + left. exists x. subst. split; auto.
        apply ind_implies_in in Hint.
        assumption.
      + right. exists e n. now subst.
    - intros [ [e [Hin Hnotin]] | [depth [n [Hin Heq]]]].
      + apply ind_iff_in in Hin.
        destruct Hin as [d Hind].
        exists d. exists (Fr e). split; eauto.
      + exists depth (Bd n). split; auto.
        right. exists n. auto.
  Qed.

  Lemma toDB_None_iff2: forall k,
    forall (t: U LN),
      toDB k t = None <->
        ~ scoped_key k t \/ ~ LC t.
  Proof.
    intros.
    rewrite toDB_None_iff.
    rewrite scoped_key_equiv.
    rewrite not_Forall_Forany.
    2:{ intro v.
        apply decidable_scoped_key_loc. }
    unfold LC, LCn.
    rewrite not_Forall_ctx_Forany_ctx.
    2:{ apply LCloc_decidable. }
    rewrite forany_iff_eq.
    rewrite forany_ctx_iff_eq. split.
    { intros [[x [Hin Hnin]] | [depth [n [Hin Hgt]]]].
      - left. exists (Fr x). split.
        rewrite in_free_iff in Hin. assumption.
        unfold compose. cbn.
        assumption.
      - right.
        exists depth (Bd n). split.
        + assumption.
        + unfold compose.
          cbn.
          lia.
    }
    { unfold compose, scoped_key_loc.
      intros [[x [Hin Hnin]] | [depth [n [Hin Hgt]]]].
      - destruct x as [x | n].
        + left. exists x. rewrite in_free_iff. auto.
        + contradiction.
      - unfold lc_loc in *.
        destruct n as [x | n].
        + contradiction.
        + right. exists depth n. split; auto.
          lia.
    }
  Qed.

End theory.
