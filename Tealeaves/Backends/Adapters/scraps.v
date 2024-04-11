
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



(*

    Goal forall (t: U LN) (k : key),
      (forall (x : atom), Fr x ∈ t -> x ∈ (k : list atom)) ->
      exists (t': U nat), toDB_from_key k t = Some t'.
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
          pose (binddt_respectful_pure (W := nat) (U := U) (T := T)).
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
*)
