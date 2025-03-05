From Tealeaves Require Import
  Backends.LN
  Backends.Named.Common
  Backends.Named.Names
  Backends.Named.Named
  Theory.DecoratedTraversableFunctorPoly
  CategoricalToKleisli.DecoratedTraversableFunctorPoly.


Import Subset.Notations.
Import Classes.Categorical.DecoratedFunctorPoly.
Import DecoratedTraversableMonad.UsefulInstances.


Import Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly.
Import Kleisli.DecoratedTraversableMonadPoly.DerivedOperations.

(*
Import CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedOperations.
Import CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedInstances.
*)

Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations.
Import CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.

Print Instances DecoratedTraversableFunctorPoly.

#[local] Generalizable Variables W T U.

#[local] Open Scope nat_scope.

Section with_DTM.

  Context
    (T: Type -> Type -> Type)
      `{Categorical.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly T}.

  Definition binding_to_ln: Binding -> LN.
  Proof.
    intros [prefix var postfix| ub_context ].
    exact (Bd (length prefix)).
    exact (Fr n).
    exact
    intros x b.
    destruct b.
    - exact (Some (length l)).
    - exact (map (fun n => length l + n) (key_lookup_name k x)).
  Defined.

  Definition toDB_from_key_loc (k: key):
    list name * name -> option nat.
  Proof.
    intros [ctx x].
    exact (binding_to_ix k x (get_binding ctx x)).
  Defined.

  Definition toDB_from_key (k: key):
    T name name -> option (T unit nat).
  Proof.
    apply mapdtp.
    - exact (const (Some tt)).
    - apply (toDB_from_key_loc k).
  Defined.

  Import List.ListNotations.

  #[program] Fixpoint generate_fresh_name_rec
    (k: key) (acc: list name) (n: nat) :=
    match n with
    | 0 => fresh (k ++ acc)
    | S m =>
        let x_fresh := fresh (k ++ acc)
        in generate_fresh_name_rec k (acc ++ [x_fresh]) m
    end.

  Definition generate_fresh_name
    (k: key) (n: nat): name :=
    generate_fresh_name_rec k [] n.

  Definition toVariable_from_key_loc (k: key):
    list unit * nat -> option name.
  Proof.
    intros [ctx n].
    pose (num_binders_under := length ctx).
    destruct (Compare_dec.le_gt_dec (num_binders_under) n).
    - (* n is a free variable, look it up in the key *)
      exact (key_lookup_index k (n - num_binders_under)).
    - (* in is bound, generate a non-conflicting name for it *)
      exact (Some (generate_fresh_name k (n - num_binders_under))).
  Defined.

  Definition toBinder_from_key_loc (k: key):
    list unit * unit -> option name.
  Proof.
    intros [ctx _].
    exact (Some (generate_fresh_name k (length ctx))).
  Defined.

  Definition toNominal_from_key (k: key):
    T unit nat -> option (T name name).
  Proof.
    apply mapdtp.
    - exact (toBinder_from_key_loc k).
    - exact (toVariable_from_key_loc k).
  Defined.

  Definition roundtrip_Named (k: key):
    T name name -> option (option (T name name)).
  Proof.
    intro t.
    exact (map (F := option) (toNominal_from_key k)
             (toDB_from_key k t)).
  Defined.

  Lemma roundtrip_Named_spec: forall (k: key) (t: T name name),
      roundtrip_Named k t =
        mapdtp (T := T) (G := option ∘ option)
          (Gmap := Map_compose option option)
          (kc3_ci  (G1 := option) (G2 := option)
             (toBinder_from_key_loc k) (const (Some tt)))
          (kc_dtfp (T := T) (G1 := option) (G2 := option)
             (toVariable_from_key_loc k) (const (Some tt))
             (toDB_from_key_loc k)) t.
  Proof.
    intros.
    unfold roundtrip_Named.
    unfold toNominal_from_key.
    unfold toDB_from_key.
    compose near t on left.
    rewrite kdtfp_mapdtp2.
    reflexivity.
    { intro.
      constructor.
      - constructor.
        reflexivity.
      - constructor; intros.
        + destruct x.
          * reflexivity.
          * reflexivity.
        + destruct x.
          * reflexivity.
          * reflexivity.
    }.
  Qed.




  Axiom (allthings: forall P, P).

  Lemma correctness_no_alpha: forall (k: key) (t: T name name),
    exists (u: T name name),
      roundtrip_Named k t = Some (Some u).
  Proof.
    intros.
    rewrite roundtrip_Named_spec.
    unfold roundtrip_Named.
    rewrite mapdtp_through_toBatchp.
    2:{ typeclasses eauto. }
    unfold compose at 1.
    unfold alpha.
    compose near t on right.
    unfold compose at 1.
    apply (Batch2_ind (list name * name) name (list name * name) name
           (fun (T1 : Type) (b0 : Batch2 (list name * name) name (list name * name) name T1) =>
            exists u : T1,
              (runBatch2
                 (option ∘ option)
                 (kc3_ci (W := Z) (toBinder_from_key_loc k) (const (Some tt)))
                 (kc_dtfp (T := T) (toVariable_from_key_loc k) (const (Some tt)) (toDB_from_key_loc k))) b0 =
                Some (Some u))).
    - intros.
      exists c. reflexivity.
    - intros.
      rewrite runBatch2_rw3.
      destruct H5 as [mkU rest].
      destruct b0 as [ctxU nmU].
      exists (mkU nmU).
      rewrite rest.
      unfold kc3_ci.
      unfold compose.
      cbn.
  Abort.

  Lemma decorate_fusion {B A}: forall (t: T B A) (u: T B A)
      (R1: list B * B -> list B * B -> Prop) (R2: list B * A -> list B * A -> Prop),
      mapdtp (T := T) (G := fun X => X -> Prop) R1 R2 t (decp u) <->
        mapdtp (T := T) (G := fun X => X -> Prop) R1 R2 t (decp u).
  Proof.
    intros.
    compose near u on right.
    Check mapdtp (G := subset) (T := T) R1 R2 t.
  Abort.


  Lemma correctness: forall (k: key) (t: T name name),
    exists (u: T name name),
      roundtrip_Named k t = Some (Some u) /\
        (alpha T t u).
  Proof.
    intros.
    rewrite roundtrip_Named_spec.
    unfold roundtrip_Named.
    rewrite mapdtp_through_toBatchp.
    2:{ typeclasses eauto. }
    unfold compose at 1.
    unfold alpha.
    compose near t on right.
    replace ((traversep (T := T) (G := fun A => A -> Prop)
                (fun _ _ : Z name => True) alpha_equiv_local ∘
                DecoratedFunctorPoly.decp) t)
      with (mapdtp (G := fun A => A -> Prop)
              (B2 := Z name) (A2 := Z name) (fun _ _ : Z name => True) alpha_equiv_local t).
    2:{ unfold mapdtp.
        unfold MapdtPoly_Substitute.
        unfold TraversePoly_Substitute.
        unfold traversep.
        admit. }
    rewrite mapdtp_through_toBatchp.
    2:{ admit. }
    unfold compose at 1.
    unfold compose at 2.
    assert ( runBatch2 subset (fun _ _ : Z name => True) alpha_equiv_local (toBatchp t) =
               runBatch2 subset (fun _ _ : Z name => True) alpha_equiv_local (toBatchp t)).
    unfold alpha_equiv_local.
    Set Printing Implicit.
    Check (@toBatchp T (Mapdt_Categorical T)  name name name name ).
    Check (@toBatchp T (@Mapdt_Categorical T H H0 H1) name (Z name) name (Z name) t).
    Set Printing Implicit.


    unfold toNominal_from_key.
    unfold toDB_from_key.
    compose near t on left.
    Search mapdtp.
    rewrite kdtfp_mapdtp2.
    About mapdtp.
    Set Typeclasses Debug.
    Print Instances Map.
    Check mapdtp (T := T) (G := option ∘ option)
      (Gmap := Map_compose option option).
    Timeout 1 Check
    Set Printing Implicit.
    Check mapdtp (kc3_ci (toBinder_from_key_loc k) (const (Some tt)))
    (kc_dtfp (toVariable_from_key_loc k) (const (Some tt)) (toDB_from_key_loc k))
    t.
    Set Printing Implicit.
    admit.
    { intro.
      constructor.
      - constructor.
        reflexivity.
      - constructor; intros.
        + destruct x.
          * reflexivity.
          * reflexivity.
        + destruct x.
          * reflexivity.
          * reflexivity.
    }.
  Abort.

End with_DTM.
