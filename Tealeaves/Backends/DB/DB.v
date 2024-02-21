From Tealeaves.Misc Require Import
  NaturalNumbers.
From Tealeaves.Theory Require Import
  TraversableFunctor
  DecoratedTraversableFunctor
  DecoratedTraversableMonad.

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
      `{Bindd_T_inst : Bindd nat T T}.

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
  Definition scoot : nat -> (nat -> T nat) -> (nat -> T nat)  :=
    fun depth σ ix =>
      if bound_in ix depth
      then ret ix
      else mapd (lift depth) (σ (ix - depth)).

  Definition open (σ : nat -> T nat) : T nat -> T nat :=
    bindd (fun '(depth, ix) => scoot depth σ ix).


  Definition one (u: T nat): nat -> T nat :=
    fun n => if n =? 0 then u else ret n.

  (*
  Definition one (u: T nat): nat * nat -> T nat :=
    fun '(depth, ix) =>
      if ix <=? depth then ret ix else u.
   *)

  Definition open_by (u : T nat) : T nat -> T nat :=
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

From Tealeaves Require Import
  Backends.LN.
From Tealeaves.Adapters Require Import
  MonadToApplicative
  KleisliToCategorical.Monad.
From Tealeaves.Functors Require Import
  State
  Option.

Open Scope nat_scope.


Module FMap.

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

  Lemma get_index_rec_S (acc: nat) (a: atom) (k: key):
    get_index_rec (S acc) a k = map S (get_index_rec acc a k).
  Proof.
    generalize dependent acc.
    induction k; intro.
    - cbn. reflexivity.
    - cbn. destruct_eq_args a a0.
  Qed.

  Lemma get_index_rec_plus (acc acc': nat) (a: atom) (k: key):
    get_index_rec (acc + acc') a k = map (fun acc => acc + acc')
                                       (get_index_rec acc a k).
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


  Lemma get_index_rec_in_core (acc: nat) (x: atom) (k: key):
    ((exists ix : nat, get_index_rec acc x k = Some ix) ->
     exists ix : nat, map S (get_index_rec acc x k) = Some ix).
  Proof.
    intros. destruct H as [ix hyp].
    exists (S ix).
    rewrite hyp.
    reflexivity.
  Qed.

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
        apply get_index_rec_in_core.
        assumption.
  Qed.

  Lemma insert_cons_eq: forall a k x,
      a = x ->
      (insert (a :: k) x) = a :: k.
  Proof.
    intros. cbn.
    destruct_eq_args x a.
  Qed.

  Lemma insert_cons_neq: forall a k x,
      a <> x ->
      (insert (a :: k) x) = a :: (insert k x).
  Proof.
    intros. cbn.
    destruct_eq_args x a.
  Qed.

  (*
  Lemma insert_neq: forall a k x,
      (insert (a :: k) x) = a :: (insert k x).
  Proof.
    intros. induction k.
    - cbn. destruct_eq_args.
    cbn.
    destruct_eq_args x a.
    -
  Qed.
   *)

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


  (*
  Lemma get_index_rec_insert (acc: nat) (a: atom) (k: key) (x: atom):
    a = x ->
    get_index_rec acc a (insert k x) =
      Some (length k + 1)%nat.
  Proof.
    intros Heq.
    induction k.
    - cbn. destruct_eq_args a x.
      *)

  Definition get_index: atom -> key -> option nat :=
    get_index_rec 0.

  Lemma get_index_in (x: atom) (k: key):
    x ∈ k -> exists ix, get_index x k = Some ix.
  Proof.
    unfold get_index.
    apply get_index_rec_in.
  Qed.

  Corollary get_index_insert1 (a: atom) (k: key) (x: atom):
    a = x ->
    exists (m: nat), get_index a (insert k x) = Some m.
  Proof.
    apply get_index_rec_insert1.
  Qed.

  Fixpoint get_atom (k: key) (ix: nat): option atom :=
    match k, ix with
    | nil, _ => None
    | cons a rest, 0 => Some a
    | cons a rest, S ix => get_atom rest ix
    end.

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

  Lemma get_atom_0: forall a k ix,
      ix = 0 ->
      get_atom (a :: k) ix = Some a.
  Proof.
    intros. subst.
    reflexivity.
  Qed.

  Lemma hmm: forall a k ix,
      get_index a k = Some ix ->
      get_atom k ix = Some a.
  Proof.
    intros.
    unfold get_atom, get_index in *.
    unfold get_index_rec in *.
    Restart.
    intros.
    generalize dependent ix.
    induction k.
    - intros x hyp.
      cbn in *. inversion hyp.
    - rename a0 into x.
      intro ix.

      intro H.
      Restart.
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
        assert (forall a x k,
                   get_index a (x :: k) = Some (S ix) ->
                 get_index a k = Some ix).
        { introv HH.
          assert (Hneq: a0 <> x0).
          { Search get_index S.
            eapply get_index_Some_S. eassumption. }
          cbn in *.
          destruct_eq_args a0 x0.
          Search get_index_rec.
          rewrite get_index_rec_S in HH.
          unfold get_index.
          change (Some (S ix)) with (map S (Some ix)) in HH.
          enough (forall (o o':option nat), map S o = map S o' -> o = o').
          apply H0 in HH.
          assumption.
          intros [j|] [j'|];
            now inversion 1.
        }
        eapply H0.
        eassumption.
  Qed.
End FMap.

Import FMap.

Module toDB.

  Section translate.

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


    Definition toDB_loc (k: key) '(depth, l) : option nat :=
      match l with
      | Bd n => Some n
      | Fr x =>
          match get_index x k with
          | None => None
          | Some ix => Some (ix + depth)%nat
          end
      end.

    Lemma toDB_loc_insert_Bd (k: key) (a: atom) depth (n: nat):
      toDB_loc (insert k a) (depth, Bd n) = Some n.
    Proof.
      reflexivity.
    Qed.

    Lemma toDB_loc_insert_Fr (k: key) (a: atom) depth (x: atom):
      toDB_loc (insert k a) (depth, Fr x) =
        toDB_loc (insert k a) (depth, Fr x).
    Proof.
      cbn.
    Abort.

    Fixpoint tokey_loc (k: key) (l: list LN): key :=
      match l with
      | nil => k
      | cons ln rest =>
          match ln with
          | Bd n =>
              tokey_loc k rest
          | Fr x =>
              tokey_loc (insert k x) rest
          end
      end.

    Lemma tokey_loc_rw_app1 (k: key) (l1: list LN) (n: nat):
      tokey_loc k (l1 ++ ret (T := list) (Bd n)) = tokey_loc k l1.
    Proof.
    Admitted.

    Lemma tokey_loc_rw_app2 (k: key) (l1: list LN) (a: atom):
      tokey_loc k (l1 ++ ret (T := list) (Fr a)) =
        insert (tokey_loc k l1) a.
    Proof.
    Admitted.

    Definition tokey (t: T LN): key :=
      tokey_loc nil (tolist t).

    Definition toLN_loc (k: key) '(depth, ix) : option LN :=
      if bound_in ix depth then
        Some (Bd ix)
      else
        map (F := option) Fr (get_atom k (ix - depth)).

    Definition toDB_from_key (k: key): T LN -> option (T nat) :=
      @mapdt nat T Mapdt_T_inst
        option Map_option Pure_option Mult_option
        LN nat (toDB_loc k).

    Definition toDB: T LN -> option (T nat) :=
      fun t => toDB_from_key (tokey t) t.

    Definition toLN_from_key (k: key): T nat -> option (T LN) :=
      @mapdt nat T Mapdt_T_inst
        option Map_option Pure_option Mult_option
        nat LN (toLN_loc k).

    Import Applicative.Notations.

    Lemma toDB_Fr: forall n (a: atom) k,
      a ∈ (k : list atom) ->
      exists ix, toDB_loc k (n, Fr a) = Some ix.
    Proof.
    Admitted.

    Lemma toDB_Bd: forall n (m: nat) k,
      exists ix, toDB_loc k (n, Bd m) = Some ix.
    Proof.
    Admitted.

    Goal forall (t: T LN) (k : key),
      (forall (x : atom), Fr x ∈ t -> x ∈ (k : list atom)) ->
      exists (t': T nat), toDB_from_key k t = Some t'.
    Proof.
      intros.
      unfold toDB_from_key.
      rewrite mapdt_through_runBatch.
      unfold compose at 1.
      induction (toBatch6 t).
      - cbv. eauto.
      - rewrite runBatch_rw2.
        destruct IHb as [f Hfeq].
        rewrite Hfeq.
        destruct a as [depth l].
        destruct l.
        + pose toDB_Fr.
          specialize (e depth a k).
          assert (Fr a ∈ t). admit.
          specialize (H a H0).
          specialize (e H).
          destruct e as [ix Hixeq].
          rewrite Hixeq.
          cbn.
          eauto.

          Restart.
          intros.
          eexists.
          change (Some ?t') with (pure t').
          unfold toDB_from_key.
          Search mapdt pure.
          rewrite mapdt_to_binddt.
          Search binddt pure.
          pose (binddt_respectful_pure (W := nat) (U := T) (T := T)).
          specialize (e LN t).
          specialize (e option _ _ _ _).

          Restart.
      intros.
      unfold toDB_from_key.
      rewrite mapdt_through_runBatch.
      unfold compose at 1.
      rewrite (element_through_runBatch2 _ nat) in H.
      rewrite toBatch6_toBatch in H.
      unfold compose in H.
      induction (toBatch6 t).
      - cbv. eauto.
      - rewrite runBatch_rw2.
        assert ( (forall x : atom,
         @runBatch LN nat (@const Type Type (LN -> Prop))
           (@Map_const (LN -> Prop))
           (@Mult_const (LN -> Prop) (@Monoid_op_subset LN))
           (@Pure_const (LN -> Prop) (@Monoid_unit_subset LN))
           (@ret subset Return_subset LN) (nat -> C)
           (@mapfst_Batch nat (nat -> C) (nat * LN) LN
              (@extract (prod nat) (Extract_reader nat) LN) b)
           (Fr x) -> x ∈ k)).
        { intros x.
          specialize (H x).
          intros hyp.
          apply H.
          left.
          assumption. }
        specialize (IHb H0).
        destruct IHb as [f Hfeq].
        rewrite Hfeq.
        destruct a as [depth l].
        destruct l.
        + pose toDB_Fr.
          specialize (e depth a k).
          enough (a ∈ k).
          { specialize (e H1).
            destruct e as [ix Hixeq].
            rewrite Hixeq.
            cbn.
            eauto. }
          apply H.
          cbn. right.
          reflexivity.
        + pose toDB_Bd.
          specialize (toDB_Bd depth n k).
          intros hyp.
          destruct hyp as [ix Hixeq].
          rewrite Hixeq.
          cbn; eauto.
    Qed.

    Goal forall (t: T LN),
      exists (t': T nat), toDB t = Some t'.
    Proof.
      intros t.
      unfold toDB.
      unfold toDB_from_key.
      unfold tokey.
      rewrite (tolist_through_runBatch nat).
      rewrite mapdt_through_runBatch.
      unfold compose at 1.
      rewrite toBatch6_toBatch.
      unfold compose at 1.
      induction (toBatch6 t).
      - cbv. eauto.
      - rewrite runBatch_rw2.
        rewrite mapfst_Batch_rw2.
        rewrite runBatch_rw2.
        destruct a as [depth l].
        change (extract (depth, l)) with l.
        destruct IHb as [t' rest].
        cbn.
        unfold_ops @Monoid_op_list.
        destruct l.
        + rewrite tokey_loc_rw_app2.
          unfold get_index.
          unfold get_index_rec.
    Abort.


    Goal forall (t: T nat) (k : key),
      exists (t': T LN), toLN_from_key k t = Some t'.
    Proof.
      intros.
      unfold toLN_from_key.
      rewrite mapdt_through_runBatch.
      unfold compose at 1.
      (*
      rewrite (element_through_runBatch2 _ nat) in H.
      rewrite toBatch6_toBatch in H.
      unfold compose in H.
       *)
      induction (toBatch6 t).
      - cbv. eauto.
      - rewrite runBatch_rw2.
        (*
        assert ( (forall x : atom,
         @runBatch LN nat (@const Type Type (LN -> Prop))
           (@Map_const (LN -> Prop))
           (@Mult_const (LN -> Prop) (@Monoid_op_subset LN))
           (@Pure_const (LN -> Prop) (@Monoid_unit_subset LN))
           (@ret subset Return_subset LN) (nat -> C)
           (@mapfst_Batch nat (nat -> C) (nat * LN) LN
              (@extract (prod nat) (Extract_reader nat) LN) b)
           (Fr x) -> x ∈ k)).
        { intros x.
          specialize (H x).
          intros hyp.
          apply H.
          left.
          assumption. }
         *)
        destruct IHb as [f Hfeq].
        rewrite Hfeq.
        (*
        destruct a as [depth l].
        destruct l.
        + pose toDB_Fr.
          specialize (e depth a k).
          enough (a ∈ k).
          { specialize (e H1).
            destruct e as [ix Hixeq].
            rewrite Hixeq.
            cbn.
            eauto. }
          apply H.
          cbn. right.
          reflexivity.
        + pose toDB_Bd.
          specialize (toDB_Bd depth n k).
          intros hyp.
          destruct hyp as [ix Hixeq].
          rewrite Hixeq.
          cbn; eauto.
         *)
    Abort.

    Lemma mapdt_respectful_pure {G} `{Applicative G} :
      forall A (t : T A) (f : nat * A -> G A),
        (forall (e : nat) (a : A), (e, a) ∈d t -> f (e, a) = pure a)
        -> mapdt (G := G) (T := T) f t = pure (F := G) t.
    Proof.
      introv hyp.
    Admitted.


    Lemma lc_bound: forall t e n,
        locally_closed (U := U) t ->
        (e, Bd n) ∈d t ->
        bound_in n e = true.
    Proof.
    Admitted.

    Lemma main: forall t k e a,
        locally_closed t ->
        (e, a) ∈d t ->
        kc6 (toLN_loc k) (toDB_loc k) (e, a) = pure (F := option ∘ option) a.
    Proof.
      introv Hlc Hin.
      cbn.
      assert ((forall (x : atom), Fr x ∈ t -> x ∈ (k : list atom))).
      admit.
      unfold kc6.
      rewrite map_strength_cobind_spec.
      destruct a.
      - cbn.
        assert (Hin': Fr a ∈ t).
        admit.
        specialize (H a Hin').
        pose (lemma:= get_index_in a k H).
        destruct lemma as [ix hyp].
        rewrite  hyp.
        change (map ?f (Some ?x)) with (Some (f x)).
        unfold_ops @Pure_compose @Pure_option.
        fequal. unfold compose.
        { unfold toLN_loc.
          unfold bound_in.
          assert (Hlt: ix + e <? e = false).
          { rewrite ltb_ge.
            lia. }
          rewrite Hlt.
          replace (ix + e - e) with ix by lia.
          About hmm.
          apply hmm in hyp.
          rewrite hyp.
          reflexivity.
        }
      - compose near (e, Bd n).
        unfold compose at 1.
        change (toDB_loc k (e, Bd n))
          with (Some n).
        change (map ?f (Some ?x)) with (Some (f x)).
        unfold_ops @Pure_compose @Pure_option.
        fequal.
        unfold compose.
        unfold toLN_loc.
        rewrite (lc_bound t e n Hlc Hin).
        reflexivity.
    Admitted.

    Goal forall (t : U LN) (k: key),
        locally_closed t ->
        map (F := option) (toLN_from_key k) (toDB_from_key k t) =
          Some (Some t).
    Proof.
      intros.
      unfold toLN_from_key.
      unfold toDB_from_key.
      compose near t on left.
      rewrite mapdt_mapdt.
      all: try typeclasses eauto.
      change (Some (Some t)) with (pure (F := option ∘ option) t).
      apply (mapdt_respectful_pure (G := option ∘ option)).
      intros.
      rewrite (main t).


      unfold kc6
      unfold compose. cbn.
      destruct a.
      - destruct (get_index a k).
        + cbn.
      Search mapdt pure.
      unfold

    (*
    Definition tokey_loc '(depth, l): State key unit :=
      match l with
      | Bd n => ret (T := State key) n
      | Fr x =>
          mkState (fun k =>
          match get_index x k with
          | None => (insert k x, (length k + 1))%nat
          | Some ix => (insert k x, ix + depth)%nat
          end)
      end.

    Definition toDB_: T LN -> State key (T nat) :=
      @mapdt nat T Mapdt_T_inst
        (State key) Map_State Pure_Monad Mult_Monad
        LN nat toDB_enhanced_loc'.

    Definition toDB: T LN -> key * (T nat) :=
      fun t => runState (toDB_ t) nil.

    Instance: Applicative (State key).
    Proof.
    Admitted.

*)
    (*
    Definition toDB_enhanced_loc (k: key) (depth: nat) (l : LN) : key * option nat :=
      match l with
      | Bd n => (k, Some n)
      | Fr x =>
          match get_index x k with
          | None => (insert k x, None)
          | Some ix => (insert k x, Some (ix + depth)%nat)
          end
      end.

    (*
    Definition toDB_enhanced_loc' '(k, depth) (l : LN) : key * nat :=
      match l with
      | Bd n => (k, n)
      | Fr x =>
          match get_index x k with
          | None => (insert k x, (length k + 1))%nat
          | Some ix => (insert k x, ix + depth)%nat
          end
      end.
     *)

    Definition toDB_enhanced_loc' '(depth, l): State key nat :=
      match l with
      | Bd n => ret (T := State key) n
      | Fr x =>
          mkState (fun k =>
          match get_index x k with
          | None => (insert k x, (length k + 1))%nat
          | Some ix => (insert k x, ix + depth)%nat
          end)
      end.

    Definition toDB_: T LN -> State key (T nat) :=
      @mapdt nat T Mapdt_T_inst
        (State key) Map_State Pure_Monad Mult_Monad
        LN nat toDB_enhanced_loc'.

    Definition toDB: T LN -> key * (T nat) :=
      fun t => runState (toDB_ t) nil.

    Instance: Applicative (State key).
    Proof.
    Admitted.

    Lemma in_final_key: forall (t: T LN) (x: atom),
        Fr x ∈ t ->
        match toDB t with
          (k, _) => x ∈ k
        end.
    Proof.
      intros.
      unfold toDB.
      unfold runState.
      unfold toDB_.
      rewrite (element_through_runBatch2 _ nat) in H.
      rewrite toBatch6_toBatch in H.
      rewrite mapdt_through_runBatch.
      unfold compose in *.
      induction (toBatch6 t).
      - cbn in *. inversion H.
      - cbn in *.
        unfold ap.
        unfold mult.

        *)


  End translate.
End toDB.
