From Tealeaves.Misc Require Import
  NaturalNumbers.
From Tealeaves.Theory Require Import
  TraversableFunctor
  DecoratedTraversableFunctor
  DecoratedTraversableMonad.


From Tealeaves Require Import
  Backends.LN.
From Tealeaves.Adapters Require Import
  MonadToApplicative
  KleisliToCategorical.Monad.

Open Scope nat_scope.

Import PeanoNat.Nat.

Import
  Product.Notations
  Monoid.Notations
  Batch.Notations
  List.ListNotations
  Subset.Notations
  Kleisli.Monad.Notations
  Kleisli.Comonad.Notations
  ContainerFunctor.Notations
  DecoratedMonad.Notations
  DecoratedContainerFunctor.Notations
  DecoratedTraversableMonad.Notations.

Import Coq.Init.Nat. (* Nat notations *)

#[local] Generalizable Variables W T U.

Open Scope nat_scope.

(** ** De Bruijn operations as defined by Tealeaves *)
(******************************************************************************)
Section ops.

  Context
    `{ret_inst : Return T}
      `{Mapd_T_inst : Mapd nat T}
      `{Bindd_U_inst : Bindd nat T U}.

  Definition bound_in: nat -> nat -> bool :=
    fun ix depth => ix <? depth.

  (* Local function for incrementing free variables
     by <<n>> *)
  Definition lift (n : nat) (p : nat * nat) : nat :=
    match p with
    | (depth, ix) =>
        if bound_in ix depth
        then ix
        else ix + n
    end.

  (* Given a depth and local substitution σ,
       adjust σ to account for the depth
       - σ should be a top-level map, e.g.
         σ 0 is the first element being substituted
         For open_by, σ 0 = u and σ (S n) = (S n)
       (<<ix - depth>> is the index into σ,
       adjusted to account for bound variables in scope
   *)
  (* TODO: Decrement free variables if necessary *)
  Definition scoot : nat -> (nat -> T nat) -> (nat -> T nat)  :=
    fun depth σ ix =>
      if bound_in ix depth
      then ret ix
      else mapd (lift depth) (σ (ix - depth)).

  Definition open (σ : nat -> T nat) : U nat -> U nat :=
    bindd (fun '(depth, ix) => scoot depth σ ix).

  Definition one (u: T nat): nat -> T nat :=
    fun n => if n =? 0 then u else ret n.

  Definition open_by (u : T nat) : U nat -> U nat :=
    open (one u).

End ops.

Section theory.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Mapd_T_inst : Mapd nat T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Mapdt_T_inst : Mapdt nat T}
      `{Bindd_T_inst : Bindd nat T T}
      `{Bindt_T_inst : Bindt T T}
      `{Binddt_T_inst : Binddt nat T T}
      `{! Compat_Map_Binddt nat T T}
      `{! Compat_Mapd_Binddt nat T T}
      `{! Compat_Traverse_Binddt nat T T}
      `{! Compat_Bind_Binddt nat T T}
      `{! Compat_Mapdt_Binddt nat T T}
      `{! Compat_Bindd_Binddt nat T T}
      `{! Compat_Bindt_Binddt nat T T}
      `{Monad_inst : ! DecoratedTraversableMonad nat T}
      `{Map_U_inst : Map U}
      `{Mapd_U_inst : Mapd nat U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Mapdt_U_inst : Mapdt nat U}
      `{Bindd_U_inst : Bindd nat T U}
      `{Bindt_U_inst : Bindt T U}
      `{Binddt_U_inst : Binddt nat T U}
      `{! Compat_Map_Binddt nat T U}
      `{! Compat_Mapd_Binddt nat T U}
      `{! Compat_Traverse_Binddt nat T U}
      `{! Compat_Bind_Binddt nat T U}
      `{! Compat_Mapdt_Binddt nat T U}
      `{! Compat_Bindd_Binddt nat T U}
      `{! Compat_Bindt_Binddt nat T U}
      `{Module_inst : ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.

  Lemma lift_zero:
    lift 0 = extract.
  Proof.
    ext [depth ix].
    cbn.
    destruct depth.
    - lia.
    - destruct (ix <=? depth); lia.
  Qed.

  Lemma scoot_zero:
    scoot 0 = id.
  Proof.
    unfold scoot.
    ext σ ix.
    cbn.
    rewrite lift_zero.
    rewrite mapd_id.
    replace (ix - 0) with ix by lia.
    reflexivity.
  Qed.

  Lemma lift1: forall (n m: nat),
      lift m ⋆4 lift n = lift (m + n).
  Proof.
    intros. ext p.
    unfold kc4, compose.
    unfold_ops @Cobind_reader.
    cbn.
    destruct p as [depth ix].
    destruct depth.
    - cbn. lia.
    - cbn.
      remember (ix <=? depth) as tmp.
      destruct tmp.
      rewrite <- Heqtmp.
      reflexivity.
      enough (ix + n <=? depth = false).
      + rewrite H. lia.
      + symmetry in Heqtmp.
        rewrite Compare_dec.leb_iff_conv in *.
        lia.
  Qed.

  Lemma scoot1 : forall (n m: nat),
      scoot m ∘ scoot n = scoot (m + n).
  Proof.
    intros.
    ext σ. unfold compose.
    ext ix.
    unfold scoot, bound_in.
    remember (ix <? m) as Hlt.
    destruct Hlt; symmetry in HeqHlt.
    - assert (Hlt2: ix <? m + n = true).
      { rewrite PeanoNat.Nat.ltb_lt in *.
        lia. }
      rewrite Hlt2.
      reflexivity.
    -  rewrite PeanoNat.Nat.ltb_ge in HeqHlt.
       assert ((ix - m <? n) = (ix <? m + n)).
       { remember (ix <? m + n) as tmp.
         destruct tmp; symmetry in Heqtmp.
         - rewrite PeanoNat.Nat.ltb_lt in *.
           lia.
         - rewrite PeanoNat.Nat.ltb_ge in *.
           lia.
       }
       rewrite H.
       remember (ix <? m + n) as tmp.
       destruct tmp.
       { compose near (ix - m).
         rewrite mapd_ret.
         unfold_ops @Return_Writer.
         unfold compose; cbn.
         replace (ix - m + m) with ix by lia.
         reflexivity.
       }
       { replace (ix - m - n) with (ix - (m + n)) by lia.
         unfold compose.
         compose near (σ (ix - (m + n))) on left.
         rewrite mapd_mapd.
         rewrite lift1.
         reflexivity.
       }
  Qed.

  Corollary scoot_S: forall (n: nat),
      scoot (S n) = scoot n ∘ scoot 1.
  Proof.
    intros.
    replace (S n) with (n + 1) by lia.
    rewrite scoot1.
    reflexivity.
  Qed.

End theory.
