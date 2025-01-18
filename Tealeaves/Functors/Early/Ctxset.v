From Tealeaves Require Export
  Functors.Early.Subset
  Functors.Early.Reader (map_strength_cobind_spec)
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedMonad
  Classes.Categorical.DecoratedFunctor (shift).

Import Comonad.Notations.
Import Kleisli.Monad.Notations.
Import Categorical.Monad.Notations.
Import Product.Notations.
Import Functors.Early.Subset.Notations.
Import Monoid.Notations.
Import DecoratedMonad.Notations.

#[local] Generalizable Variables W A B.

(** * The <<ctxset>> functor *)
(******************************************************************************)
Definition ctxset (E: Type) := fun A => subset (E * A).

Section ctxset.

  Context
    (E: Type).

  (** ** Operations and specifications *)
  (******************************************************************************)
  #[export] Instance Mapd_ctxset: Mapd E (ctxset E) :=
    fun `(f: E * A -> B) (s: ctxset E A) =>
    fun '(e, b) => exists (a: A), s (e, a) /\ f (e, a) = b.

  #[export] Instance Map_ctxset: Map (ctxset E) :=
    fun `(f: A -> B) (s: ctxset E A) =>
    fun '(e, b) => exists (a: A), s (e, a) /\ f a = b.

  Lemma ctxset_mapd_spec: forall (A B: Type) `(f: E * A -> B),
      mapd (T := ctxset E) f = map (F := subset) (cobind f).
  Proof.
    intros. ext s [e b].
    cbv. propext.
    - intros [a [Hin Heq]].
      exists (e, a). now subst.
    - intros [[e' a] [Hin Heq]].
      exists a. inversion Heq. now subst.
  Qed.

  Lemma ctxset_map_spec: forall (A B: Type) `(f: A -> B),
      map (F := ctxset E) f = map (F := subset) (map f).
  Proof.
    intros. ext s [e b].
    cbv. propext.
    - intros [a [Hin Heq]].
      exists (e, a). now subst.
    - intros [[e' a] [Hin Heq]].
      exists a. inversion Heq. now subst.
  Qed.

  (** ** Operations and specifications *)
  (******************************************************************************)
  Lemma ctxset_map_to_mapd: forall (A B: Type) (f: A -> B),
      map f = mapd (T := ctxset E) (f ∘ extract).
  Proof.
    intros.
    rewrite ctxset_mapd_spec, ctxset_map_spec.
    rewrite (map_to_cobind (W := (E ×))).
    reflexivity.
  Qed.

  Lemma kdf_subset_mapd1 :
    forall A: Type, mapd (T := ctxset E) extract = @id (ctxset E A).
  Proof.
    intros. cbv. ext f [e a]. propext.
    - intros [a' Heq]. now preprocess.
    - intros H. exists a. intuition.
  Qed.

  Lemma kdf_subset_mapd2 :
    forall (A B C: Type) (g: E * B -> C) (f: E * A -> B),
      mapd g ∘ mapd f = mapd (g ⋆1 f).
  Proof.
    intros. do 2 rewrite ctxset_mapd_spec.
    rewrite (fun_map_map (E * A) (E * B) (E * C) (F := subset)).
    rewrite (kcom_cobind2).
    rewrite <- ctxset_mapd_spec.
    reflexivity.
  Qed.

  (** ** Decorated functor typeclass instance *)
  (******************************************************************************)
  #[export] Instance DTF_ctxset: DecoratedFunctor E (ctxset E) :=
    {| kdf_mapd1 := kdf_subset_mapd1;
       kdf_mapd2 := kdf_subset_mapd2;
    |}.

  (*
  #[export] Instance Compat_Map_Mapd_ctxset :
    `{Compat_Map_Mapd}.
  Proof.
    hnf.
    ext A B f.
    now rewrite ctxset_map_to_mapd.
  Qed.
   *)

  #[export] Instance Functor_ctxset:
    Functor (ctxset E).
  Proof.
  Admitted.

  (** ** Monoid instances *)
  (******************************************************************************)
  Instance Monoid_op_ctxset {A: Type}: Monoid_op (ctxset E A) :=
    @Monoid_op_subset (E * A).

  Instance Monoid_unit_ctxset {A: Type}: Monoid_unit (ctxset E A) :=
    @Monoid_unit_subset (E * A).

  Instance Monoid_ctxset {A: Type}: Monoid (ctxset E A) := @Monoid_subset (E * A).

  #[export] Instance Monmor_ctxset_mapd: forall `(f: E * A -> B),
      Monoid_Morphism (ctxset E A) (ctxset E B) (mapd f).
  Proof.
    intros. unfold ctxset.
    rewrite ctxset_mapd_spec.
    Fail typeclasses eauto.
  Admitted.

  #[export] Instance map_ctxset_morphism: forall `(f: A -> B),
      Monoid_Morphism (ctxset E A) (ctxset E B) (map f).
  Proof.
    intros. unfold ctxset.
    rewrite ctxset_map_spec.
    Fail typeclasses eauto.
  Admitted.

End ctxset.


(** * The <<ctxset>> monad *)
(******************************************************************************)
Section ctxset.

  Context `{Monoid W}.

  (** ** Monad instance *)
  (******************************************************************************)
  #[export] Instance Return_ctxset: Return (ctxset W) :=
    fun A a '(w, b) => a = b /\ w = Ƶ.

  #[export] Instance Bindd_ctxset: Bindd W (ctxset W) (ctxset W) :=
    fun A B f s_a =>
      (fun '(w, b) => exists (wa: W) (a: A),
           s_a (wa, a) /\
             exists (wb: W), f (wa, a) (wb, b) /\ w = wa ● wb).

  #[export] Instance Bind_ctxset: Bind (ctxset W) (ctxset W) :=
    fun A B f s_a =>
      (fun '(w, b) => exists (wa: W) (a: A),
           s_a (wa, a) /\
             exists (wb: W), f a (wb, b) /\ w = wa ● wb).

  Lemma ctxset_ret_spec: forall (A: Type),
      ret (T := ctxset W) (A := A) =
        ret (T := subset) ∘ ret (T := (W ×)).
  Proof.
    intros. ext a. ext [w b]. propext.
    - cbv. now intuition subst.
    - cbv. now inversion 1.
  Qed.

  Lemma ctxset_bindd_spec: forall (A B: Type) (f: W * A -> ctxset W B),
      bindd (T := ctxset W) f =
        bind (T := subset) (shift subset ∘ cobind (W := (W ×)) f).
  Proof.
    intros. ext s [w b]. unfold shift.
    rewrite (map_strength_cobind_spec (G := subset)).
    unfold_ops @Bind_subset @Bindd_ctxset @Map_subset.
    propext.
    - intros [wa [a [contra [w' [Hin Heq]]]]].
      subst. exists (wa, a). split.
      + assumption.
      + exists (w', b). easy.
    - intros [[wa a] [Hin [[wb b'] [Hin' Heq]]]].
      inversion Heq. subst.
      exists wa a. split.
      + assumption.
      + exists wb. easy.
  Qed.

  Lemma ctxset_bind_to_bindd: forall (A B: Type) (f: A -> ctxset W B),
      bind (T := ctxset W) f =
        bindd (T := ctxset W) (f ∘ extract).
  Proof.
    reflexivity.
  Qed.

  (*
  Lemma ctxset_mapd_to_bindd: forall (A B: Type) (f: W * A -> B),
      mapd (T := ctxset W) f =
        bindd (T := ctxset W) (ret ∘ f).
  Proof.
    intros.
    rewrite ctxset_mapd_spec.
    rewrite ctxset_bindd_spec.
    rewrite Monad.map_to_bind.
    fequal.
    rewrite ctxset_ret_spec.
    unfold_ops @Return_subset @Return_Writer.
    ext [w a] [w' b]. unfold shift, compose; cbn.
    unfold_ops @Map_subset; unfold uncurry.
    propext.
    - inversion 1. subst.
      exists (w', (Ƶ, f (w', a))). splits.
      + eauto.
      + cbn. now simpl_monoid.
    - intros. preprocess. now simpl_monoid.
  Qed.

  Lemma ctxset_map_to_bindd: forall (A B: Type) (f: A -> B),
      map f = bindd (T := ctxset W) (ret ∘ f ∘ extract).
  Proof.
    intros.
    rewrite ctxset_map_to_mapd.
    rewrite ctxset_mapd_to_bindd.
    reflexivity.
  Qed.

  Lemma ctxset_bind_spec: forall (A B: Type) (f: A -> ctxset W B),
      bind (T := ctxset W) f =
        bind (T := subset) (shift subset ∘ map (F := (W ×)) f).
  Proof.
    intros.
    rewrite ctxset_bind_to_bindd.
    rewrite ctxset_bindd_spec.
    rewrite map_to_cobind.
    reflexivity.
  Qed.

  #[export] Instance Compat_Bind_Bindd_ctxset :
    Compat_Bind_Bindd W (ctxset W) (ctxset W).
  Proof.
    reflexivity.
  Qed.

  #[export] Instance Compat_Map_Bindd_ctxset :
    Compat_Map_Bindd W (ctxset W) (ctxset W).
  Proof.
    hnf. ext A B f.
    rewrite ctxset_map_to_bindd.
    reflexivity.
  Qed.

  #[export] Instance Compat_Mapd_Bindd_ctxset :
    Compat_Mapd_Bindd W (ctxset W) (ctxset W).
  Proof.
    hnf. ext A B f.
    rewrite ctxset_mapd_to_bindd.
    reflexivity.
  Qed.
  *)

  (** ** Rewriting laws *)
  (******************************************************************************)
  Lemma bindd_ctxset_nil `{f: W * A -> ctxset W B} :
    bindd f (@subset_empty (W * A)) = @subset_empty (W * B).
  Proof.
    ext [w b]. cbn. propext.
    - intros [wa [a [contra [w' [Hin Heq]]]]].
      inversion contra.
    - inversion 1.
  Qed.

  Lemma bindd_ctxset_one `{f: W * A -> ctxset W B} {w: W} {a: A} :
    bindd f {{ (w, a) }} = shift subset (w, f (w, a)).
  Proof.
    rewrite ctxset_bindd_spec.
    autorewrite with tea_set.
    reflexivity.
  Qed.

  Lemma bindd_ctxset_add `{f: W * A -> ctxset W B} {x y} :
      bindd f (x ∪ y: ctxset W A) = bindd f x ∪ bindd f y.
  Proof.
    rewrite ctxset_bindd_spec.
    now autorewrite with tea_set.
  Qed.

  #[local] Hint Rewrite
    @bindd_ctxset_nil @bindd_ctxset_one @bindd_ctxset_add
   : tea_set.

  (** ** Decorated monad laws *)
  (******************************************************************************)
  Lemma ctxset_bindd0: forall (A B: Type) (f: W * A -> ctxset W B),
      bindd f ∘ ret = f ∘ pair Ƶ.
  Proof.
    intros. ext a.
    rewrite ctxset_bindd_spec.
    rewrite ctxset_ret_spec.
    unfold compose.
    rewrite bind_set_one.
    change (cobind f (η a)) with (Ƶ, f (Ƶ, a)).
    unfold ctxset. (* hidden *)
    rewrite (DecoratedFunctor.shift_zero subset).
    reflexivity.
  Qed.

  (*
  Lemma ctxset_bindd1: forall A: Type,
      bindd (T := ctxset W) (ret (T := ctxset W) ∘ extract) = @id (ctxset W A).
  Proof.
    intros.
    rewrite ctxset_bindd_spec.
    rewrite <- map_to_cobind.
    replace (@id (ctxset W A))
      with (bind (U := subset) (T := subset) (@ret subset _ (W * A)))
      by (now rewrite kmon_bind1).
    fequal. unfold compose.
    ext [w a]. cbn.
    change ((η ∘ extract) (w, a)) with (η a).
    rewrite ctxset_ret_spec.
    change ((η ∘ η) a) with ({{ (Ƶ, a) }}).
    unfold ctxset. (* hidden *)
    rewrite (DecoratedFunctor.shift_spec subset).
    autorewrite with tea_set.
    cbn. simpl_monoid.
    reflexivity.
  Qed.
   *)

  (*
  Lemma ctxset_bindd2_lemma :
    forall (A B C :Type) (g: W * B -> ctxset W C)
      (f: W * A -> ctxset W B),
      kc1 (T := subset) (shift subset ∘ cobind g)
        (shift subset ∘ cobind f) =
        shift subset ∘ cobind (g ⋆5 f).
  Proof.
    intros. unfold kc1, kc5.
    ext [w a].
    unfold compose at 1 3. (* LHS *)
    unfold compose at 2. (* RHS *)
    cbn.
    rewrite ctxset_bindd_spec.
    unfold ctxset.
    rewrite (DecoratedFunctor.shift_spec subset).
    rewrite (DecoratedFunctor.shift_spec subset).
    compose near (f (w, a)).
    rewrite (bind_map (U := subset)).
    rewrite (map_bind (U := subset)).
    fequal. ext [w' b].
    unfold shift.
    do 2 reassociate <- on right.
    rewrite (fun_map_map (F:= subset)).
    rewrite (map_strength_cobind_spec (G := subset) (E := W)).
    rewrite (map_strength_cobind_spec (G := subset) (E := W)).
    unfold preincr, compose. cbn.
    fequal. ext [w'' c].
    cbn. simpl_monoid.
    reflexivity.
  Qed.

  Lemma ctxset_bindd2 :
    forall (A B C: Type) (g: W * B -> ctxset W C) (f: W * A -> ctxset W B),
      bindd g ∘ bindd f = bindd (g ⋆5 f).
  Proof.
    intros.
    do 3 rewrite ctxset_bindd_spec.
    unfold ctxset. (*hidden*)
    rewrite (kmon_bind2 (T := subset)).
    rewrite ctxset_bindd2_lemma.
    reflexivity.
  Qed.

  #[export] Instance DecoratedRightPreModule_ctxset :
    DecoratedRightPreModule W (ctxset W) (ctxset W) :=
    {| kdmod_bindd1 := ctxset_bindd1;
       kdmod_bindd2 := ctxset_bindd2;
    |}.

  #[export] Instance DecoratedMonad_ctxset :
    DecoratedMonad W (ctxset W) :=
    {| kdm_bindd0 := ctxset_bindd0;
    |}.

  #[export] Instance DecoratedRightModule_ctxset :
    DecoratedRightModule W (ctxset W) (ctxset W) :=
    {| kdmod_monad := _ |}.

  (** * <<bindd>> is a monoid homomorphism *)
  (******************************************************************************)
  #[export] Instance Monmor_ctxset_bindd {A B f} :
    Monoid_Morphism (ctxset W A) (ctxset W B) (bindd f).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - now rewrite bindd_ctxset_nil.
    - intros. apply bindd_ctxset_add.
  Qed.

  (** * Querying for an element is a monoid homomorphism *)
  (******************************************************************************)
  #[export] Instance Monmor_ctxset_evalAt {A: Type} (w: W) (a: A) :
    @Monoid_Morphism (ctxset W A) Prop
      (@Monoid_op_subset (W * A))
      (@Monoid_unit_subset (W * A))
      (Monoid_op_or) (Monoid_unit_false)
      (evalAt (w, a)).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - reflexivity.
    - reflexivity.
  Qed.
 *)
End ctxset.
