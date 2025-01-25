From Tealeaves Require Import
  Backends.DB.DB
  Backends.LN.Atom
  Backends.Named.Names
  Backends.Named.Named
  Backends.Adapters.KeyName
  Functors.Option
  Theory.DecoratedTraversableFunctorPoly.

Import DecoratedTraversableMonad.UsefulInstances.

#[local] Generalizable Variables W T U.
#[local] Open Scope nat_scope.

Section with_DTM.

  Context
    (T: Type -> Type -> Type)
    `{DecoratedTraversableFunctorPoly T}.

  Print Binding.

  Definition binding_to_ix (k: key): name -> Binding -> option nat.
  Proof.
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
          (kc_dtfp (G1 := option) (G2 := option)
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

  Lemma correctness: forall (k: key) (t: T name name),
      roundtrip_Named k t = roundtrip_Named k t.
  Proof.
    intros.
    unfold roundtrip_Named.
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
