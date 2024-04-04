From Tealeaves.Misc Require Import
  NaturalNumbers.
From Tealeaves.Theory Require Import
  TraversableFunctor
  DecoratedTraversableFunctor
  DecoratedTraversableMonad.


From Tealeaves Require Import
  Backends.LN
  Backends.DB.DB
  Backends.DB.Key
  Functors.Option.
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
  DecoratedTraversableFunctor.Notations
  DecoratedTraversableMonad.Notations.

Import Coq.Init.Nat. (* Nat notations *)

#[local] Generalizable Variables W T U.

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


    (** ** Boring admitted lemmas *)
    (******************************************************************************)
    Lemma lc_bound: forall t e n,
        locally_closed (U := U) t ->
        (e, Bd n) ∈d t ->
        bound_in n e = true.
    Proof.
    Admitted.

    Lemma mapdt_respectful_pure {G} `{Applicative G} :
      forall A (t : U A) (f : nat * A -> G A),
        (forall (e : nat) (a : A), (e, a) ∈d t -> f (e, a) = pure a)
        -> mapdt (G := G) (T := U) f t = pure (F := G) t.
    Proof.
      introv hyp.
    Admitted.

    (** ** Translation *)
    (******************************************************************************)
    Definition toDB_loc (k: key) '(depth, l) : option nat :=
      match l with
      | Bd n => Some n
      | Fr x =>
          match key_lookup_atom k x with
          | None => None
          | Some ix => Some (ix + depth)%nat
          end
      end.

    Lemma toDB_loc_insert_Bd (k: key) (a: atom) depth (n: nat):
      toDB_loc (key_insert_atom k a) (depth, Bd n) = Some n.
    Proof.
      reflexivity.
    Qed.

    Lemma toDB_loc_insert_Fr (k: key) (a: atom) depth (x: atom):
      toDB_loc (key_insert_atom k a) (depth, Fr x) =
        toDB_loc (key_insert_atom k a) (depth, Fr x).
    Proof.
    Abort.

    (* Give a list of LN variables,
       build a key containing every atom *)
    Fixpoint LN_to_key_loc (l: list LN): key :=
      match l with
      | nil => nil
      | cons ln rest =>
          match ln with
          | Bd n =>
              LN_to_key_loc rest
          | Fr x =>
              key_insert_atom (LN_to_key_loc rest) x
          end
      end.

    Lemma LN_to_key_unique: forall l,
        unique (LN_to_key_loc l).
    Proof.
      intros l. induction l.
      - exact I.
      - cbn. destruct a.
        + now apply key_insert_unique.
        + assumption.
    Qed.

    Lemma LN_key_bijection: forall l ix a,
        key_lookup_index (LN_to_key_loc l) ix = Some a <->
          key_lookup_atom (LN_to_key_loc l) a = Some ix.
    Proof.
      intros.
      apply key_bijection.
      apply LN_to_key_unique.
    Qed.

    (*
    Lemma tokey_loc_rw_app1 (k: key) (l1: list LN) (n: nat):
      tokey_loc k (l1 ++ ret (T := list) (Bd n)) = tokey_loc k l1.
    Proof.
    Admitted.

    Lemma tokey_loc_rw_app2 (k: key) (l1: list LN) (a: atom):
      tokey_loc k (l1 ++ ret (T := list) (Fr a)) =
        insert (tokey_loc k l1) a.
    Proof.
    Admitted.
      *)

    Definition LN_to_key (t: U LN): key :=
      LN_to_key_loc (tolist t).

    Definition toLN_loc (k: key) '(depth, ix) : option LN :=
      if bound_in ix depth then
        Some (Bd ix)
      else
        map (F := option) Fr (key_lookup_index k (ix - depth)).

    Definition toDB_from_key (k: key): U LN -> option (U nat) :=
      @mapdt nat U Mapdt_U_inst
        option Map_option Pure_option Mult_option
        LN nat (toDB_loc k).

    Definition toDB: U LN -> option (U nat) :=
      fun t => toDB_from_key (LN_to_key t) t.

    Definition toLN_from_key (k: key): U nat -> option (U LN) :=
      @mapdt nat U Mapdt_U_inst
        option Map_option Pure_option Mult_option
        nat LN (toLN_loc k).

    Import Applicative.Notations.

    Lemma toDB_Fr: forall n (a: atom) k,
      a ∈ (k : list atom) ->
      exists ix, toDB_loc k (n, Fr a) = Some ix.
    Proof.
      intros.
      unfold toDB_loc.
      destruct (key_lookup_in1 _ _ H) as [m Hin].
      exists (m + n). now rewrite Hin.
    Qed.

    Lemma toDB_Bd: forall n (m: nat) k,
      exists ix, toDB_loc k (n, Bd m) = Some ix.
    Proof.
      intros.
      unfold toDB_loc.
      eauto.
    Qed.

    Definition whole_key (t: U LN) k :=
      forall x : atom, Fr x ∈ t -> x ∈ k.

    Lemma to_DB_from_key_total:
      forall (t: U LN) (k : key),
        whole_key t k ->
        exists (t': U nat), toDB_from_key k t = Some t'.
    Proof.
      introv Hin.
      unfold toDB_from_key.
      rewrite mapdt_through_runBatch.
      unfold compose at 1.
      unfold whole_key in Hin.
      rewrite (element_through_runBatch2 _ nat) in Hin.
      rewrite toBatch6_toBatch in Hin.
      unfold compose in Hin.
      induction (toBatch6 t).
      - cbv. eauto.
      - rewrite runBatch_rw2.
        assert (H: (forall x : atom,
         @runBatch LN nat (@const Type Type (LN -> Prop))
           (@Map_const (LN -> Prop))
           (@Mult_const (LN -> Prop) (@Monoid_op_subset LN))
           (@Pure_const (LN -> Prop) (@Monoid_unit_subset LN))
           (@ret subset Return_subset LN) (nat -> C)
           (@mapfst_Batch nat (nat -> C) (nat * LN) LN
              (@extract (prod nat) (Extract_reader nat) LN) b)
           (Fr x) -> x ∈ k)).
        { intros x.
          specialize (Hin x).
          intros hyp.
          apply Hin.
          left.
          assumption. }
        specialize (IHb H).
        destruct IHb as [f Hfeq].
        rewrite Hfeq.
        destruct a as [depth l].
        destruct l.
        + pose toDB_Fr.
          specialize (e depth a k).
          enough (H_a_in_k: a ∈ k).
          { specialize (e H_a_in_k).
            destruct e as [ix Hixeq].
            rewrite Hixeq.
            cbn.
            eauto. }
          apply Hin.
          cbn. right.
          reflexivity.
        + pose toDB_Bd.
          specialize (toDB_Bd depth n k).
          intros hyp.
          destruct hyp as [ix Hixeq].
          rewrite Hixeq.
          cbn; eauto.
    Qed.

    Lemma main: forall t k e a,
        (forall x : atom, Fr x ∈ t -> x ∈ k) ->
        locally_closed t ->
        (e, a) ∈d t ->
        kc6 (toLN_loc k) (toDB_loc k) (e, a) = pure (F := option ∘ option) a.
    Proof.
      introv Hcont Hlc Hin.
      cbn.
      unfold kc6.
      rewrite map_strength_cobind_spec.
      destruct a.
      - cbn.
        assert (Hin': Fr a ∈ t).
        rewrite ind_iff_in.
        eexists. eassumption.
        specialize (Hcont a Hin').
        specialize (key_lookup_in1 k a Hcont).
        intros [m Hlookup].
        rewrite Hlookup.
        change (map ?f (Some ?x)) with (Some (f x)).
        unfold_ops @Pure_compose @Pure_option.
        fequal. unfold compose.
        { unfold toLN_loc.
          unfold bound_in.
          assert (Hlt: m + e <? e = false).
          { rewrite ltb_ge.
            lia. }
          rewrite Hlt.
          replace (m + e - e) with m by lia.
          apply key_bijection1 in Hlookup.
          rewrite Hlookup.
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
    Qed.

    Theorem translation_inv1:
      forall (t : U LN) (k: key),
        (forall x : atom, Fr x ∈ t -> x ∈ k) ->
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
      now rewrite (main t).
    Qed.

    (*
    Goal forall (u : T nat) (t: U LN) (k : key),
        (forall (x : atom), Fr x ∈ t -> x ∈ (k : list atom)) ->
        exists (t': U nat), map (F := option) (open_by u) (toDB_from_key k t) = Some t'.
    Proof.
      intros.
      unfold open_by.
      unfold open_by, open, toDB_from_key.
      compose near t.
      rewrite bindd_mapdt.
      change (Some ?t') with (pure t').
      rewrite binddt_through_runBatch.
      rewrite (element_through_runBatch2 _ nat) in H.
      Search toBatch7.
    Abort.

    Goal forall (u : T nat) (u_pre : T LN) (t: U LN) (k : key),
        (forall (x : atom), Fr x ∈ t -> x ∈ (k : list atom)) ->
        map (F := option) (open_by u) (toDB_from_key k t) =
          toDB_from_key k (LN.open (U := U) u_pre t).
    Proof.
      intros.
      unfold open_by, open.
      unfold toDB_from_key.
      unfold LN.open.
      compose near t.
      rewrite bindd_mapdt.
      rewrite mapdt_bindd.
      apply binddt_respectful.
      - typeclasses eauto.
      - introv Hin.
    Abort.

    Goal forall (t: U LN),
      exists (t': U nat), toDB t = Some t'.
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

    Goal forall (t: U nat) (k : key),
      exists (t': U LN), toLN_from_key k t = Some t'.
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
    *)

  End translate.
End toDB.
