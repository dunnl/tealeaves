From Tealeaves Require Import
  Backends.LN
  Backends.Nominal.Common.Hmap
  Backends.Nominal.Common.Freshening
  Backends.Nominal.Common.Binding
  Backends.Common.Names
  Backends.Nominal.FV
  Backends.Nominal.Alpha
  Backends.Adapters.LNtoNominal
  Backends.Adapters.NominaltoLN.

From Tealeaves Require Import
  Categorical.DecoratedTraversableMonadPoly
  Kleisli.DecoratedFunctorZ.

From Tealeaves Require Import
  Adapters.PolyToMono.PDTM
  Adapters.PolyToMono.Categorical.DecoratedTraversableMonad.

From Tealeaves Require Import
  Theory.TraversableFunctor
  Theory.LiftRel.TraversableFunctor
  Classes.Kleisli.Theory.TraversableFunctor.

Import PDTM.KleisliClassesAll.
Import PDTM.CategoricalToKleisliAll.
Import PDTM.ListUnitToNat.
#[export] Remove Hints Monoid_Morphism_compose: typeclass_instances.

Import Subset.Notations.
Import Classes.Categorical.DecoratedFunctorPoly.
Import List.ListNotations.
Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variables W T U.
#[local] Open Scope list_scope.

(** ** Set Operations *)
(********************************************************************)
#[export] Existing Instance Tolist_Traverse.
#[export] Existing Instance ToSubset_Traverse.
#[export] Existing Instance ToCtxlist_Mapdt.
#[export] Existing Instance ToCtxset_Mapdt.

(** * Miscellaneous Supporting Lemmas *)
(**********************************************************************)

(** ** Properties about mapping over <<list>>/<<Z>> *)
(**********************************************************************)
Lemma mapd_list_prefix_const: forall (A: Type) (w: list A),
    mapdz (T := list) (const tt) w = map (F := list) (const tt) w.
Proof.
  intros.
  rewrite mapd_list_prefix_spec.
  unfold compose.
  induction w.
  - reflexivity.
  - cbn. fequal.
    compose near (decorate_prefix_list w).
    rewrite (fun_map_map).
    rewrite <- IHw.
    reflexivity.
Qed.

Lemma cobind_Z_const: forall (A: Type),
    cobind (A := A) (W := Z) (const tt) = map (F := Z) (const tt).
Proof.
  introv.
  ext [w a].
  cbn.
  rewrite mapd_list_prefix_const.
  reflexivity.
Qed.

Lemma cobind_L_const: forall (A A' B: Type) (f: L B A -> A'),
    cobind_L (B1 := B) (A1 := A) (const tt) f =
      fun '(w, a) => (map (F := list) (const tt) w, f (w, a)).
Proof.
  introv.
  ext [w a].
  cbn.
  compose near w on left.
  unfold_Z.
  rewrite <- mapd_list_prefix_spec.
  rewrite mapd_list_prefix_const.
  reflexivity.
Qed.

(** ** Lemma About Mapdtp with Constant Applicatives *)
(**********************************************************************)
Require Import Classes.Kleisli.DecoratedTraversableFunctorPoly.

Section constant_applicatives.

  Context
    `{Categorical.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly T}.

  Context
    {M} `{Monoid M}.

  Import Adapters.PolyToMono.Categorical.TraversableFunctor.ToMono (dist2_natural_rw).

  Lemma mapdtp_const1:
    forall {A1 B1: Type} (A2 B2: Type) `(g: list B1 * B1 -> M) `(f: list B1 * A1 -> M),
      mapdtp (G := const M) (B2 := False) (A2 := False) g f =
        mapdtp (G := const M) (B2 := B2) (A2 := A2) g f.
  Proof.
    intros.
    change_left
      (map (F := const M)
         (A := T False False)
         (B := T B2 A2)
         (map2 (F := T) (B1 := False) (A1 := False) (B2 := B2) (A2 := A2) exfalso exfalso)
         ∘ mapdtp (T := T) (G := const M) g f).
    unfold mapdtp.
    unfold Mapdtp_Categorical.
    reassociate <- on left.
    reassociate <- on left.
    unfold compose.
    ext t.
    rewrite <- dist2_natural_rw.
    compose near (decp t).
    rewrite fun2_map_map.
    fequal.
  Qed.

  Lemma mapdtp_const_normalize:
    forall {A1 B1: Type} (A2 B2: Type) `(g: list B1 * B1 -> M) `(f: list B1 * A1 -> M),
      mapdtp (G := const M) (B2 := B2) (A2 := A2) g f =
        mapdtp (G := const M) (B2 := False) (A2 := False) g f.
  Proof.
    intros.
    symmetry.
    apply mapdtp_const1.
  Qed.

End constant_applicatives.

(** * Roundtrips *)
(**********************************************************************)
Section roundtrips.

  Context `{Categorical.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly T}.

  (* Misc lemmas *)
  Import Adapters.PolyToMono.Categorical.TraversableFunctor.ToMono (Dist2_1_natural2).

  (* Test single-sorted DTM instance for B = 1 *)
  Print Instances Monoid_Morphism.
  Import Classes.Kleisli.DecoratedTraversableMonad.
  Print Instances DecoratedTraversableMonad.

  Goal Categorical.DecoratedTraversableMonad.DecoratedTraversableMonad (list unit) (T unit).
    typeclasses eauto.
  Qed.

  Goal Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad (list unit) (T unit).
    typeclasses eauto.
  Qed.

  (** ** Roundtrip from Nominal *)
  (********************************************************************)
  (* The operation mapping a nominal term to a locally nameless term,
     then back again into a nominal term *)
  Definition rtFromNominal: T name name -> T name name :=
    fun t =>
      let t_ln := nomToLN t
      in lnToNom (LN.free t_ln) t_ln.

  Lemma rtFromNominal_spec:
    forall (t: T name name),
      rtFromNominal t =
        let Γ := free (nomToLN t)
        in mapdp
             (kc_dz (assignNames_loc Γ) (const tt))
             (kc_dfunp (lnToNom_loc Γ) (const tt) nomToLN_loc) t.
  Proof.
    intros.
    unfold rtFromNominal.
    compose near t on left.
    unfold nomToLN at 2.
    unfold lnToNom at 1.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  (** ** Roundtrip from Nominal: Decomposed *)
  (********************************************************************)
  (* Given a binding occurrence (pre, b) in a nominal term t,
     return the new name of b after a Nominal~>LN~>Nominal roundtrip *)

  (** *** Decomposition in the Binders *)
  (********************************************************************)
  Section binders_decompose.

    Context (Γ: list atom).

    Definition roundtrip_Binder_loc: Z atom -> atom :=
      assignNames_loc Γ ∘ map (const tt).

    Lemma roundtrip_Binder_loc_spec:
      mapdz (T := list) roundtrip_Binder_loc =
        assignNames Γ ∘ map (const tt).
    Proof.
      intros.
      unfold roundtrip_Binder_loc.
      rewrite assignNames_spec.
      Set Keyed Unification.
      rewrite (mapdz_map_list (A' := atom) (B := atom) (A := unit)).
      Unset Keyed Unification.
      reflexivity.
    Qed.

  End binders_decompose.

  (** *** Decomposition in Variables *)
  (********************************************************************)
  Section variables_decompose.

    Context (Γ: list atom).

    (* Given a variable occurrence (pre, v) in a nominal term t,
       return the new name of v after a Nominal~>LN~>Nominal
       roundtrip *)
    Definition roundtrip_Var_loc: L atom atom -> atom :=
      kc_dfunp (lnToNom_loc Γ) (const tt) nomToLN_loc.

  End variables_decompose.

  (** *** Total Decomposition *)
  (********************************************************************)
  Section decomposed.

    Lemma rtFromNominal_spec_decomposed:
      forall (t: T name name),
        rtFromNominal t =
          let Γ := LN.free (nomToLN t)
          in mapdz (T := fun B => T B name) (roundtrip_Binder_loc Γ)
               (mapd (T := T name) (roundtrip_Var_loc Γ) t).
    Proof.
      intros.
      rewrite rtFromNominal_spec.
      cbn zeta.
      rewrite (mapdp_decompose T).
      unfold kc_dz.
      rewrite cobind_Z_const.
      reflexivity.
    Qed.

  End decomposed.

  (** ** Roundtrip effect on context occurrences *)
  (* if (ctx, a) ∈d t, then (rtFromNominal_occ (free t) (ctx, a)) ∈d roundtrip t *)
  (********************************************************************)
  Definition rtFromNominal_occ (Γ: list atom):
    list atom * atom -> list atom * atom :=
    fun '(ctx, a) =>
      (mapdz (roundtrip_Binder_loc Γ) ctx, roundtrip_Var_loc Γ (ctx, a)).

  Lemma rtFromNominal_occ_spec (Γ: list atom): forall ctx a,
      rtFromNominal_occ Γ (ctx, a) =
        (map_fst (mapdz (T := list) (roundtrip_Binder_loc Γ))
           (cobind (W := prod (list atom)) (roundtrip_Var_loc Γ) (ctx, a))).
  Proof.
    intros.
    unfold rtFromNominal_occ.
    unfold cobind.
    reflexivity.
  Qed.

  Lemma rtFromNominal_occ_spec_pw: forall (Γ: list atom) (ctx: list atom) (a: atom),
      rtFromNominal_occ Γ (ctx, a) =
        (mapdz (roundtrip_Binder_loc Γ) ctx, roundtrip_Var_loc Γ (ctx, a)).
  Proof.
    unfold rtFromNominal_occ.
    reflexivity.
  Qed.

  Lemma rtFromNominal_var_spec {Γ: list atom}:
    (kc_dfunp
       (lnToNom_loc Γ)
       (const tt)
       nomToLN_loc) =
      fun '(ctx, nm) =>
        match binding_to_ln (get_binding ctx nm) with
        | Fr x => x
        | Bd n => bdToName Γ (map (const tt) ctx) n
        end.
  Proof.
    ext [ctx nm].
    unfold kc_dfunp.
    unfold compose.
    unfold cobind_L.
    unfold compose.
    unfold map_L.
    cbn.
    compose near ctx.
    unfold_Z.
    rewrite <- mapd_list_prefix_spec.
    rewrite mapd_list_prefix_const.
    reflexivity.
  Qed.

  (** ** Specification for Decoration After Renaming Binders *)
  (********************************************************************)
  Lemma decorate_rename_binders {B1 B2 V}:
    forall (ρ: list B1 * B1 -> B2) (t: T B1 V),
      delete_binders (dec (T B2) (mapdz ρ t)) =
        delete_binders (map (F := T B1) (map_fst (mapdz (T := list) ρ)) (dec (T B1) t)).
  Proof.
    intros.
    unfold delete_binders.
    unfold bmap.
    unfold_ops @Map2_1.
    unfold Map2_2 at 1.
    unfold map at 1.
    unfold_ops @VDec.
    unfold compose.
    compose near (decp (F := T) (mapdz ρ t)).
    rewrite fun2_map_map.
    change (id ∘ ?x) with x.
    compose near (decp t).
    rewrite (fun2_map_map).
    change (id ∘ ?x) with x.
    compose near (decp t).
    unfold map at 1.
    unfold Map2_2.
    rewrite (fun2_map_map).
    change (id ∘ ?x) with x.
    change (?x ∘ id) with x.
    change ((@const B2 unit tt ∘ @extract Z Extract_Z B2)) with
      (@const (Z B2) unit tt).
    change ((@const B1 unit tt ∘ @extract Z Extract_Z B1)) with
      (@const (Z B1) unit tt).
    unfold mapdz at 1.
    unfold_ops @Mapdz_Categorical.
    unfold right_coaction.
    unfold BDec.
    unfold_ops @DecoratedFunctor.ToMono2.BDec.
    unfold map at 1.
    unfold compose.
    compose near (decp t) on left.
    rewrite fun2_map_map.
    compose near (decp t) on left.
    rewrite (polydecnat).
    repeat change (?f ∘ id) with f.
    repeat change (id ∘ ?f) with f.
    unfold compose.
    compose near t on left.
    rewrite dfunp_dec_dec.
    unfold compose.
    compose near (decp t) on left.
    rewrite (fun2_map_map).
    compose near (decp t) on left.
    rewrite (fun2_map_map).
    fequal.
    change (id ∘ ?x) with x.
    ext [w v].
    unfold compose.
    cbn.
    rewrite mapd_list_prefix_spec.
    reflexivity.
  Qed.

  Lemma decorate_rename_binders2 {B1 B2 V}:
    forall (ρ: list B1 * B1 -> B2) (t: T B1 V),
      delete_binders (dec (T B2) (mapdz ρ t)) =
        map (F := T unit)
          (map_fst (mapdz (T := list) ρ))
          (delete_binders (dec (T B1) t)).
  Proof.
    intros.
    rewrite decorate_rename_binders.
    compose near (dec (T B1) t).
    unfold delete_binders.
    unfold bmap.
    rewrite fun2_map22_map21_commute.
    reflexivity.
  Qed.

  (** *** Occurence Relation After Deleting Binders *)
  (********************************************************************)
  Lemma in_del_binders {B A}: forall (t: T B A) (a: A),
      element_of a (delete_binders t) = element_of a t.
  Proof.
    intros.
    unfold delete_binders.
    unfold bmap.
    unfold element_of.
    rewrite tosubset_to_mapReduce.
    rewrite tosubset_to_mapReduce.
    rewrite mapReduce_to_traverse1.
    rewrite mapReduce_to_traverse1.
    unfold_ops @Traverse_Categorical.
    unfold compose.
    compose near t.
    rewrite <- fun2_map22_map21_commute.
    unfold compose.
    rewrite Dist2_1_natural2.
    reflexivity.
  Qed.

  (** ** Relating Free Variables During Translation *)
  (********************************************************************)
  Lemma normalize_mapReduce {M} `{Monoid M} `(f: list name * name -> M): forall (t: T name name),
      mapdReduce f t =
        mapdtp (A2 := False) (G := const M) (T := T) (pure (F := const M) ∘ (const tt)) f t.
  Proof.
    intros.
    rewrite mapdReduce_to_mapdt1.
    unfold mapdt.
    unfold mapdt.
    unfold DecoratedTraversableFunctor.DerivedOperations.Mapdt_Categorical.
    unfold_ops @dist.
    unfold Dist2_1.
    unfold_ops @TraversableFunctor.ToMono.Dist2_1.
    unfold DecoratedFunctor.dec.
    unfold_ops @VDec.
    change_left ((dist2 (B := atom) (A := False) ∘ (map2 pure id ∘ map f ∘ map2 extract id) ∘ decp) t).
    rewrite fun2_map2_map21.
    rewrite fun2_map_map.
    change (id ∘ ?f) with f.
    change (f ∘ ?id) with f.
    change_left ((mapdtp (B2 := atom) (A2 := False) (B1 := atom) (A1 := atom) (pure (F := const M)) f) t).
    pose (cut := mapdtp_const_normalize False (A1 := atom) (B1 := atom) atom).
    rewrite cut.
    clear cut.
    pose (cut := mapdtp_const_normalize False (A1 := atom) (B1 := atom) unit).
    rewrite cut.
    clear cut.
    reflexivity.
  Qed.

  Lemma FV_preserved: forall (t: T name name),
      FV t =
        LN.free (nomToLN t).
  Proof.
    intros.
    unfold FV.
    unfold nomToLN.
    unfold free.
    rewrite mapReduce_to_traverse1.
    unfold_ops @traverse.
    unfold_ops @TraversableFunctor.DerivedOperations.Traverse_Categorical.
    unfold_ops @dist.
    unfold_ops @TraversableFunctor.ToMono.Dist2_1.
    unfold_ops @Map2_1.
    reassociate -> on right.
    rewrite fun2_map_map.
    unfold mapdp.
    unfold Mapdp_Categorical.
    change (?x ∘ id) with x; change (id ∘ ?x) with x.
    unfold compose.
    compose near (decp t).
    rewrite fun2_map_map.
    rewrite normalize_mapReduce.
    unfold mapdtp.
    unfold Mapdtp_Categorical.
    unfold compose.
    assert (cut: FV_loc = free_loc ∘ nomToLN_loc).
    { ext [l v].
      unfold compose.
      unfold nomToLN_loc.
      destruct (get_binding_spec_proof l v) as [[Hbinding Hspec] | [pre [post [Hbinding [Hspec1 Hspec2]]]]].
      - cbn.
        rewrite Hbinding.
        reflexivity.
      - cbn.
        rewrite Hbinding.
        reflexivity.
    }
    rewrite cut.
    reflexivity.
  Qed.

  (** ** Alpha Equivalence Local Reasoning *)
  (********************************************************************)
  Lemma assignNames_loc_preincr: forall Γ a,
      assignNames_loc Γ ∘ cobind (W := Z) (const tt) ∘ incr [a] =
        assignNames_loc (Γ ++ [fresh Γ]) ∘ cobind (const tt).
  Proof.
    intros.
    ext [ctx x].
    unfold compose.
    unfold assignNames_loc.
  Abort.

  (** *** Specification of <<rtFromNominal_occ>> when a is unbound *)
  (********************************************************************)
  Lemma rtFromNominal_occ_Unbound_spec: forall (Γ: list atom) (ctx: list atom) (a: atom),
      get_binding ctx a = Unbound ctx a ->
      rtFromNominal_occ Γ (ctx, a) = (mapdz (roundtrip_Binder_loc Γ) ctx, a).
  Proof.
    introv Hyp.
    rewrite rtFromNominal_occ_spec_pw.
    fequal.
    cbn.
    rewrite Hyp.
    reflexivity.
  Qed.

  (** *** Specification of <<roundtrip_Var_loc>> when a is bound *)
  (********************************************************************)
  Lemma roundtrip_Var_loc_Bound_spec: forall (Γ: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      ctx = prefix ++ [a'] ++ postfix ->
      a = a' ->
      roundtrip_Var_loc Γ (ctx, a) =
        historyToName Γ (assignNames Γ (map (const tt) prefix), tt).
  Proof.
    introv Hbinding Hctx Haeq.
    unfold historyToName.
    unfold roundtrip_Var_loc.
    unfold kc_dfunp.
    rewrite cobind_L_const.
    unfold compose at 1.
    unfold nomToLN_loc.
    rewrite Haeq in *; clear Haeq.
    rewrite Hbinding.
    unfold binding_to_ln.
    unfold lnToNom_loc.
    unfold bdToName.
    rewrite map_preserve_length.
    assert (HsafeIx: length postfix < length ctx).
    { subst.
      rewrite List.app_length.
      rewrite List.app_length.
      cbn.
      lia.
    }
    rewrite <- PeanoNat.Nat.ltb_lt in HsafeIx.
    rewrite HsafeIx.
    unfold assignNames_loc.
    unfold hadapt.
    unfold historyToName.
    fequal.
    fequal.
    unfold assignNames.
    fequal.
    assert (Hineq: length ctx - (length postfix + 1) = length prefix).
    { subst.
      rewrite List.app_length.
      rewrite List.app_length.
      cbn.
      lia.
    }
    rewrite Hineq.
    { clear. induction prefix.
      - reflexivity.
      - cbn. now rewrite IHprefix. }
  Qed.

  (** *** Specification of <<get_binding ∘ rtFromNominal_occ>> when a is unbound *)
  (********************************************************************)
  Lemma rtFromNominal_occ_get_binding_Unbound_spec:
    forall (Γ: list atom) (ctx: list atom) (a: atom),
      a ∈ Γ ->
      get_binding ctx a = Unbound ctx a ->
      match rtFromNominal_occ Γ (ctx, a) with
      | (foo, x) =>
          get_binding foo x = Unbound (mapdz (roundtrip_Binder_loc Γ) ctx) a
      end.
  Proof.
    introv Hnin Hyp.
    rewrite rtFromNominal_occ_Unbound_spec; auto.

    destruct (get_binding_spec_proof (mapdz (roundtrip_Binder_loc Γ) ctx) a)
      as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin']]]]].
    { rewrite Case1.
      reflexivity. }
    { assert (Hfresh: ~ a ∈ mapdz (roundtrip_Binder_loc Γ) ctx).
      { rewrite roundtrip_Binder_loc_spec.
        unfold compose at 1.
        apply assignNames_fresh.
        assumption.
      }
      apply get_binding1 in Hfresh.
      assumption.
    }
  Qed.

  (** *** Specification of <<get_binding ∘ rtFromNominal_occ>> when a is bound *)
  (********************************************************************)
  Lemma rtFromNominal_occ_get_binding_Bound_spec:
    forall (Γ: list atom) (ctx: list atom) (a: atom) prefix a' postfix,
      get_binding ctx a = Bound prefix a' postfix ->
      a = a' ->
      ctx = prefix ++ [a'] ++ postfix ->
      ~ a ∈ postfix ->
      match rtFromNominal_occ Γ (ctx, a) with
      | (foo, x) =>
          let NewPrefix := assignNames Γ (map (const tt) prefix)
          in let NewVar := historyToName Γ (NewPrefix, tt)
             in let NewPost := assignNames (Γ ++ NewPrefix ++ [NewVar]) (map (const tt) postfix)
                in get_binding foo x = Bound NewPrefix NewVar NewPost /\ length NewPrefix = length prefix
      end.
  Proof.
    introv Hyp Haeq Hctxeq Hnin.
    remember (rtFromNominal_occ Γ (ctx, a)).
    destruct p.
    rewrite rtFromNominal_occ_spec_pw in Heqp.
    injection Heqp; introv Hctx' HVar'.
    clear Heqp.
    intros NewPrefix NewVar NewPost.
    split.
    { assert
        (HRoundtripMapsToNewVar:
          roundtrip_Var_loc Γ (prefix ++ [a'] ++ postfix, a') = NewVar).
      { subst.
        unfold NewVar.
        unfold NewPrefix.
        eapply roundtrip_Var_loc_Bound_spec;
          eauto.
      }
      apply get_binding2.
      - subst. apply HRoundtripMapsToNewVar.
      - subst.
        rewrite roundtrip_Binder_loc_spec.
        unfold compose.
        rewrite map_list_app.
        rewrite map_list_app.
        rewrite map_list_one.
        change (const tt a') with tt.
        rewrite assignNames_decompose.
        fold NewPrefix.
        fold NewVar.
        fold NewPost.
        rewrite HRoundtripMapsToNewVar.
        reflexivity.
      - apply assignNames_fresh.
        rewrite element_of_list_app.
        rewrite element_of_list_app.
        right; right.
        rewrite element_of_list_one.
        subst.
        assumption.
    }
    { unfold NewPrefix.
      rewrite length_assignNames.
      rewrite map_preserve_length.
      reflexivity.
    }
  Qed.

  Lemma rt_correct_local2:
    forall (t: T name name) (Γ: list name)
      (HΓinit: forall (a: name), (a ∈ FV t -> a ∈ Γ)),
    forall (ctx: list name) (a: name),
      (ctx, a) ∈ (dec (T atom) t) ->
      alpha_equiv_local (ctx, a) (rtFromNominal_occ Γ (ctx, a)).
  Proof.
    introv HFV.
    introv Hin.
    unfold alpha_equiv_local.
    destruct (get_binding_spec_proof ctx a) as [[Case1 Hanin] | [prefix [postfix [Case2 [ctxspec Hnin]]]]].
    { rewrite Case1.
      assert (HΓ: a ∈ Γ).
      { apply HFV.
        apply (FV_lift_local (T := T atom) _ ctx); auto.
      }
      specialize (rtFromNominal_occ_get_binding_Unbound_spec Γ ctx a HΓ Case1).
      intro X.
      destruct (rtFromNominal_occ Γ (ctx, a)).
      rewrite X. destruct_eq_args a a.
    }
    {
      rewrite Case2.
      apply (rtFromNominal_occ_get_binding_Bound_spec Γ) in Case2; auto.
      destruct (rtFromNominal_occ Γ (ctx, a)).
      destruct Case2 as [Case2RW Case2Len].
      rewrite Case2RW.
      rewrite Case2Len.
      destruct_eq_args (length prefix) (length prefix).
    }
  Qed.

  Lemma rt_correct_local1:  forall (t: T name name),
      TraversableFunctor.Forall
        (fun a: list atom * atom =>
           (precompose (cobind (W := prod (list atom)) (roundtrip_Var_loc (free (nomToLN t))))
              ∘ (precompose (map_fst (mapdz (roundtrip_Binder_loc (free (nomToLN t))))) ∘ alpha_equiv_local)) a a)
        (delete_binders (dec (T atom) t)).
  Proof.
    intros t.
    rewrite TraversableFunctor.forall_iff.
    intros [ctx a].
    rewrite in_del_binders.
    unfold compose, precompose.
    rewrite <- rtFromNominal_occ_spec.
    apply rt_correct_local2.
    clear a.
    introv HinFV.
    rewrite (FV_preserved t) in HinFV.
    assumption.
  Qed.

  (** ** Correctness of <<rtFromNominal>> *)
  (********************************************************************)
  Theorem rtFromNominal_correct: forall (t: T name name),
      polymorphic_alpha T t (rtFromNominal t).
  Proof.
    intros.
    rewrite (rtFromNominal_spec_decomposed).
    unfold polymorphic_alpha.
    unfold lift_relation_ctx2.
    setoid_rewrite (decorate_rename_binders2).
    rewrite TraversableFunctor.relation_natural2.
    change (dec (mapd (roundtrip_Var_loc (free (nomToLN t))) t))
      with (DecoratedFunctor.dec (T atom) (mapd (roundtrip_Var_loc (free (nomToLN t))) t)).
    rewrite (CategoricalToKleisli.DecoratedFunctor.dec_mapd2 (list atom) (F := T atom)).
    change (map (F := ?F) (A := ?A) (B := ?B)) with (vmap (B := atom) (V1 := A) (V2 := A)).
    rewrite delete_binders_vmap.
    unfold vmap.
    rewrite relation_natural2.
    apply relation_diagonal1.
    apply rt_correct_local1.
  Qed.

  Theorem rtFromNominal_correct2: forall (t: T name name),
      polymorphic_alpha T t (lnToNom (free (nomToLN t)) (nomToLN t)).
  Proof.
    intros.
    unfold rtFromNominal.
    apply rtFromNominal_correct.
  Qed.

  (** ** Roundtrip in the Other Direction *)
  (********************************************************************)
  Definition rtFromLN:
    T unit LN -> T unit LN :=
    fun t =>
      let t_nom := lnToNom (LN.free t) t
      in nomToLN t_nom.

  Lemma rtFromLN_spec1:
    forall (t: T unit LN),
      rtFromLN t =
        mapdp (kc_dz (const tt) (assignNames_loc (free t)))
          (kc_dfunp nomToLN_loc (assignNames_loc (free t)) (lnToNom_loc (free t))) t.
  Proof.
    intros.
    unfold rtFromLN.
    compose near t on left.
    unfold nomToLN at 1.
    unfold lnToNom at 1.
    rewrite kdfunp_mapdp2.
    reflexivity.
  Qed.

  Lemma rtFromLN_spec_decomposed:
    forall (t: T unit LN),
      rtFromLN t =
        let Γ := free t
        in (mapdz (T := fun B => T B LN) (const tt)
           (mapd (T := T unit) (kc_dfunp (T := T)
                                  nomToLN_loc
                                  (assignNames_loc Γ)
                                  (lnToNom_loc Γ)) t)).
  Proof.
    intros.
    rewrite rtFromLN_spec1.
    unfold kc_dz.
    change (const tt ∘ cobind (assignNames_loc (free t)))
      with (const (A := list unit * unit) tt).
    rewrite (mapdp_decompose T).
    reflexivity.
  Qed.

  Lemma rtFromLN_spec_decomposed2:
    forall (t: T unit LN),
      rtFromLN t =
        let Γ := free t
        in (mapd (T := T unit)
              (kc_dfunp (T := T)
                 nomToLN_loc
                 (assignNames_loc Γ)
                 (lnToNom_loc Γ)) t).
  Proof.
    intros.
    rewrite rtFromLN_spec_decomposed.
    assert (Hren: mapdz (T := fun B => T B LN) (const tt (A := list unit * unit)) = id).
    { unfold mapdz.
      unfold Mapdz_Categorical.
      assert (Hconst: const tt (A := list unit * unit) = extract (W := Z)).
      { ext [? u]. cbv.
        destruct u. reflexivity. }
      rewrite Hconst.
      unfold map, right_coaction.
      unfold Map2_2.
      unfold BDec.
      reassociate <- on left.
      rewrite fun2_map_map.
      apply dfunp_dec_extract.
    }
    unfold_Z.
    rewrite Hren.
    reflexivity.
  Qed.

  Context
    `{! Compat_Map_Mapd (list unit) (T unit)}
      `{! DecoratedContainerFunctor (list unit) (T unit)}.

  Import CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.


  Section support.
    Context (Γ: list atom).

    Lemma get_binding_LN_rt2_lemma1: forall (ctx: list unit) (n: nat),
        n < length ctx ->
        ctx = (length_to_list_unit (length ctx - (n + 1)) ++ [ tt ]  ++ length_to_list_unit n).
    Proof.
      introv Hlt. induction ctx.
      - false. cbn in Hlt. lia.
      - compare naturals n and (length ctx).
        + specialize (IHctx ineqp).
          rewrite IHctx.
          rewrite length_cons.
          rewrite List.app_length.
          rewrite length_length_to_list_unit.
          rewrite List.app_length.
          rewrite length_length_to_list_unit.
          rewrite (length_one (a := tt)).
          assert (HlenEq: (S (length ctx - (n + 1) + (1 + n)) - (n + 1)) = S (length ctx - (n + 1))).
          { lia. }
          rewrite HlenEq.
          rewrite length_to_list_unit_S.
          destruct a.
          reflexivity.
        + clear IHctx.
          assert (HlenEq: (length (a :: ctx) - (length ctx + 1)) = 0).
          { rewrite length_cons.
            lia.
          }
          rewrite HlenEq.
          destruct a.
          rewrite <- length_list_unit_iso.
          reflexivity.
        + false. cbn in Hlt.
          lia.
    Qed.

    #[local] Open Scope nat_scope.

    Lemma nat_decompose: forall (ctx: nat) (part: nat),
        part < ctx ->
        ctx = part + 1 + (ctx - part - 1).
    Proof.
      introv Hlen.
      lia.
    Qed.

    Lemma list_unit_decompose: forall (ctx: list unit) (part: list unit),
        length part < length ctx ->
        ctx = part ++ [tt] ++ (length_to_list_unit (length ctx - length part - 1)).
    Proof.
      introv Hlen.
      pose (Helper:= nat_decompose (length ctx) (length part) Hlen).
      rewrite (length_list_unit_iso ctx) at 1.
      rewrite (length_list_unit_iso part) at 1.
      rewrite Helper.
      clear Helper.
      rewrite length_to_list_unit_plus.
      rewrite List.app_assoc.
      rewrite length_to_list_unit_plus.
      fequal.
      fequal. lia.
    Qed.

    Lemma get_binding_LN_rt2_generalized: forall (ctx: list unit) (part: list unit),
        length part < length ctx ->
        (get_binding (assignNames Γ ctx) (assignNames_loc Γ (part, tt))) =
          Bound
            (assignNames Γ part)
            (assignNames_loc Γ (part, tt))
            (assignNames (Γ ++ assignNames Γ part ++ [assignNames_loc Γ (part, tt)])
               (length_to_list_unit (length ctx - length part - 1))).
    Proof.
      introv Hlt.
      apply get_binding2.
      - reflexivity.
      - rewrite (list_unit_decompose ctx part); [| assumption].
        rewrite assignNames_decompose.
        cbn zeta.
        rewrite assignNames_loc_spec.
        fequal.
        fequal.
        fequal.
        fequal.
        do 2 rewrite List.app_length.
        rewrite (length_one (a := tt)).
        rewrite length_length_to_list_unit.
        lia.
      - apply assignNames_fresh.
        simpl_list.
        tauto.
    Qed.

    Lemma get_binding_LN_rt2: forall (ctx: list unit) (n: nat),
        n < length ctx ->
        (get_binding (assignNames Γ ctx)
           (assignNames_loc Γ (length_to_list_unit (length ctx - (n + 1)), tt))) =
          Bound
            (assignNames Γ (length_to_list_unit (length ctx - (n + 1))))
            (assignNames_loc Γ (length_to_list_unit (length ctx - (n + 1)), tt))
            (assignNames (Γ ++ assignNames Γ (length_to_list_unit (length ctx - (n + 1))) ++
                            [assignNames_loc Γ ((length_to_list_unit (length ctx - (n + 1))), tt)])
               (length_to_list_unit n)).
    Proof.
      introv Hlt.
      rewrite get_binding_LN_rt2_generalized.
      - fequal.
        fequal.
        fequal.
        rewrite length_length_to_list_unit.
        lia.
      - rewrite length_length_to_list_unit.
        lia.
    Qed.

    Lemma get_binding_LN_rt1: forall (ctx: list unit) (n: nat),
        n < length ctx ->
        binding_to_ln
          (get_binding (assignNames Γ ctx)
             (assignNames_loc Γ (length_to_list_unit (length ctx - (n + 1)), tt))) =
          Bd n.
    Proof.
      intros.
      rewrite get_binding_LN_rt2; auto.
      unfold binding_to_ln.
      rewrite length_assignNames.
      rewrite length_length_to_list_unit.
      reflexivity.
    Qed.

    Lemma decompose_list_by_ix: forall (A: Type) (l: list A) (n: nat),
        n < length l ->
        exists pre a post, l = pre ++ [a] ++ post /\
                        length post = n.
    Proof.
      introv Hlt.
      induction l.
      - false.
        inversion Hlt.
      - cbn in Hlt.
        compare naturals n and (length l).
        { apply IHl in ineqp.
          destruct ineqp as [pre [a' [post [Heq Hrest]]]].
          exists (a :: pre) a' post; split; auto.
          rewrite Heq.
          rewrite List.app_comm_cons.
          reflexivity.
        }
        { exists (@nil A)  a l.
          rewrite List.app_nil_l.
          auto.
        }
    Qed.

    Lemma get_binding_LN_new2: forall (l: list atom) (pre: list unit) (post: list unit),
        (get_binding
           (assignNames l pre ++
              [historyToName l (assignNames l pre, tt)] ++
              assignNames
              (l ++ assignNames l pre ++ [historyToName l (assignNames l pre, tt)]) post)
           (historyToName l (assignNames l pre, tt)))
        =  Bound
             (assignNames l pre)
             (historyToName l (assignNames l pre, tt))
             (assignNames
                (l ++ assignNames l pre ++ [historyToName l (assignNames l pre, tt)]) post).
    Proof.
      intros.
      apply get_binding2.
      - reflexivity.
      - reflexivity.
      - apply  assignNames_fresh.
        rewrite element_of_list_app.
        rewrite element_of_list_app.
        rewrite element_of_list_one.
        right. right. reflexivity.
    Qed.

  End support.

  #[export] Instance: forall B, Compat_Traverse_Mapdt (list B) (T B).
  Proof.
    intros.
    unfold Compat_Traverse_Mapdt.
    unfold Traverse_Categorical.
    unfold DerivedOperations.Traverse_Mapdt.
    intros.
    ext A' B' f'.
    unfold mapdt, Mapdt_Categorical.
    rewrite <- fun_map_map.
    reassociate -> on right.
    reassociate -> on right.
    rewrite dfun_dec_extract.
    reflexivity.
  Qed.

  #[export] Instance: Compat_Traverse_Binddt nat (T unit) (T unit).
  Proof.
    intros.
    unfold Compat_Traverse_Binddt.
    unfold Traverse_Categorical.
    unfold DerivedOperations.Traverse_Binddt.
    intros.
    ext A' B' f'.
    unfold binddt, Binddt_Categorical.
    rewrite <- fun_map_map.
    reassociate -> on right.
    reassociate -> on right.
    reassociate -> on right.
    rewrite dfun_dec_extract.
    reassociate <- on right.
    rewrite <- fun_map_map.
    change_right (map (F := G) join ∘ (dist (T unit) G ∘ map (F := T unit ∘ G) ret) ∘ map (F := T unit) f').
    Set Keyed Unification.
    rewrite <- (natural (Natural := dist_natural) (ϕ := @dist (T unit) _ G _ _ _)).
    Unset Keyed Unification.
    reassociate <- on right.
    unfold_ops @Map_compose.
    rewrite fun_map_map.
    rewrite (mon_join_map_ret (T := T unit)).
    rewrite fun_map_id.
    reflexivity.
  Qed.

  #[export] Instance: Compat_Mapdt_Binddt nat (T unit) (T unit).
  Proof.
    intros.
    unfold Compat_Traverse_Binddt.
    unfold Traverse_Categorical.
    unfold DerivedOperations.Traverse_Binddt.
    intros.
    unfold Compat_Mapdt_Binddt.
    intros.
    ext A' B' f'.
    unfold Mapdt_Categorical.
    unfold DerivedOperations.Mapdt_Binddt.
    unfold binddt, Binddt_Categorical.
    rewrite <- fun_map_map.
    reassociate -> on right.
    reassociate -> on right.
    reassociate -> on right.
    reassociate <- on right.
    reassociate <- on right.
    change_right (map (F := G) join ∘ (dist (T unit) G ∘ map (F := T unit ∘ G) ret) ∘
                    map (F := T unit) f' ∘ dec (T unit) (A := A')).
    Set Keyed Unification.
    rewrite <- (natural (Natural := dist_natural) (ϕ := @dist (T unit) _ G _ _ _)).
    Unset Keyed Unification.
    reassociate <- on right.
    unfold_ops @Map_compose.
    rewrite fun_map_map.
    rewrite (mon_join_map_ret (T := T unit)).
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma rtFromLN_id_local:
    forall (t : T unit LN) (HLC: LC t)
      (FVt: list atom) (HeqFVt: FVt = free t)
      (ctx: list unit) (v: LN) (Hin: (ctx, v) ∈d t),
      binding_to_ln (get_binding (assignNames FVt ctx) (lnToNom_loc FVt (ctx, v))) = v.
  Proof.
    intros.
    destruct v as [a | n].
    - unfold lnToNom_loc.
      assert (H_a_not_assigned: ~ a ∈ assignNames FVt ctx).
      { apply assignNames_fresh.
        subst.
        assert (Compat_ToSubset_ToCtxset (list unit) (T unit)).
        typeclasses eauto.
        apply ind_implies_in in Hin.
        rewrite <- in_free_iff in Hin.
        assumption.
      }
      assert (H_get_binding_Unbound:
               get_binding (assignNames FVt ctx) a = Unbound (assignNames FVt ctx) a).
      { destruct (get_binding_spec_proof (assignNames FVt ctx) a)
          as [[Case1 rest] | [prefix [postfix [Case2 [ctxspec Hnin']]]]].
        - assumption.
        - false. apply H_a_not_assigned.
          subst. rewrite ctxspec.
          simpl_list. tauto. }
      rewrite H_get_binding_Unbound.
      reflexivity.
    - unfold lnToNom_loc.
      unfold bdToName.
      assert (H_n_lt: Nat.ltb n (length ctx) = true).
      { rewrite OrdersEx.Nat_as_OT.ltb_lt.
        rewrite (LC_spec (T := T unit) (U := T unit)) in HLC.
        specialize (HLC (length ctx) (Bd n)).
        cbn in HLC.
        assert (Hin': (length ctx, Bd n) ∈d t).
        { unfold element_ctx_of in *.
          unfold toctxset in *.
          unfold ToCtxset_Mapdt in *.
          unfold mapdReduce in *.
          unfold mapdt in *.
          unfold Mapdt_Categorical in *.
          unfold dec.
          unfold Decorate_list_unit_nat.
          unfold Categorical.Decorate_Monoid_Morphism.
          rewrite <- compose_assoc.
          change (?x ○ ?y) with (x ∘ y).
          rewrite compose_assoc.
          rewrite compose_assoc.
          change ((@dist (T unit) (@Dist2_1 T H H1 unit)
                     (@const Type Type (nat * LN -> Prop)) (@Map_const (nat * LN -> Prop))
                     (@Pure_const (nat * LN -> Prop) (@Monoid_unit_subset (nat * LN)))
                     (@Mult_const (nat * LN -> Prop) (@Monoid_op_subset (nat * LN))) False
                     ∘ (@map (T unit) (@Map2_1 T H unit) (nat * LN) (@const Type Type (nat * LN -> Prop) False)
                          (@ret subset Return_subset (nat * LN))
                          ∘ @map (T unit) (@Map2_1 T H unit) (list unit * LN) (nat * LN)
                          (map (F := fun A => A) (@map_fst LN (list unit) nat (@length unit))))
                     ∘ @dec (list unit) (T unit) (@VDec T H H0 unit) LN) t (@length unit ctx, Bd n)).
          rewrite fun_map_map.
          setoid_rewrite <- (natural (ϕ := @ret (subset) _)).
          rewrite <- fun_map_map.
          change (map (F := T unit) (map (F := subset) (@map_fst LN (list unit) nat (@length unit))))
            with (map (F := T unit ∘ subset) (@map_fst LN (list unit) nat (@length unit))).
          reassociate <-.
          try rewrite <- (natural (ϕ := @dist (T unit) _ (@const Type Type (nat * LN -> Prop)) _ _ _ )).
        admit.
        }
        specialize (HLC Hin').
        lia.
      }
      rewrite H_n_lt.
      rewrite get_binding_LN_rt1.
      + reflexivity.
      + rewrite <- OrdersEx.Nat_as_OT.ltb_lt.
        assumption.
  Admitted.

  Lemma rtFromLN_id: forall (t: T unit LN),
      LC t ->
      rtFromLN t = t.
  Proof.
    introv HLC.
    rewrite rtFromLN_spec_decomposed2.
    remember (free t) as FVt.
    cbn.
    apply mapd_respectful_id.
    intros ctx v Hin.
    unfold kc_dfunp.
    unfold compose at 1.
    unfold cobind_L, cojoin_L, compose at 1.
    unfold map_L.
    compose near ctx on left.
    unfold_Z.
    rewrite <- mapd_list_prefix_spec.
    change (mapd_list_prefix (assignNames_loc FVt) ctx)
      with (mapdz (assignNames_loc FVt) ctx).
    rewrite <- assignNames_spec.
    unfold nomToLN_loc.
    eapply rtFromLN_id_local; eauto.
  Qed.

  Lemma rtFromLN_correct: forall (t: T unit LN),
      LC t ->
      nomToLN (lnToNom (free t) t) = t.
  Proof.
    introv HLC.
    unfold rtFromLN.
    apply rtFromLN_id.
    assumption.
  Qed.

End roundtrips.
