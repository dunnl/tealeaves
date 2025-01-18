From Tealeaves Require Import
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.RightComodule
  Classes.Categorical.Bimonad
  Functors.Early.Writer.

#[local] Generalizable Variables E T W F G.

Import Monad.Notations.
Import Strength.Notations.
Import Product.Notations.
Import Monoid.Notations.

#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments dec {E}%type_scope F%function_scope {Decorate} {A}%type_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.

(** * A decorated functor is precisely a right comodule of <<prod E>> *)
(******************************************************************************)
Definition RightComodule_DecoratedFunctor
  `{DecoratedFunctor E F}
  : RightComodule F (prod E) :=
  {| rcom_coaction_coaction := dfun_dec_dec;
    rcom_map_extr_coaction := dfun_dec_extract;
  |}.

Definition DecoratedFunctor_RightComodule
  `{Map F} `{RightCoaction F (prod E)}
  `{! RightComodule F (prod E)} `{Monoid E}
  : DecoratedFunctor E F :=
  {| dfun_dec_dec := rcom_coaction_coaction;
    dfun_dec_extract := rcom_map_extr_coaction;
  |}.

(** * Decorated functors form a monoidal category *)
(******************************************************************************)

(** ** Null-decorated functors *)
(** Every functor is trivially decorated using the operation that
    pairs each leaf with the unit of the monoid. We call such functors
    null-decorated. This allows us to see _all_ functors as (maybe
    trivially) decorated. *)
(******************************************************************************)
Section DecoratedFunctor_Zero.

  Context
    `{Monoid W}
    `{Functor F}.

  Instance Decorate_zero : Decorate W F :=
    fun A => @map F _ A (W * A) (pair Ƶ).

  Instance Natural_dec_zero :
    Natural (@dec W F _).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Map_compose @Decorate_zero.
    now do 2 rewrite fun_map_map.
  Qed.

  Lemma dec_dec_zero {A} :
    dec F ∘ dec F (A:=A) =
    map F (cojoin (W :=(W ×))) ∘ dec F.
  Proof.
    intros. unfold_ops @Decorate_zero.
    now do 2 rewrite fun_map_map.
  Qed.

  Lemma dec_extract_zero {A} :
    map F (extract (W := (W ×))) ∘ dec F = @id (F A).
  Proof.
    intros. unfold_ops @Decorate_zero.
    rewrite fun_map_map.
    unfold compose; cbn.
    now rewrite fun_map_id.
  Qed.

  Instance DecoratedFunctor_zero : DecoratedFunctor W F :=
    {| dfun_dec_natural := Natural_dec_zero;
       dfun_dec_dec := @dec_dec_zero;
       dfun_dec_extract := @dec_extract_zero;
    |}.

End DecoratedFunctor_Zero.

(** ** The identity (zero-)decorated functor *)
(******************************************************************************)
Section DecoratedFunctor_I.

  Context
    `{Monoid W}.

  Definition dec_I : forall A, A -> prod W A :=
    fun A => @pair W A Ƶ.

  #[global] Instance Decorate_I : Decorate W (fun A => A) := dec_I.

  #[global] Instance Natural_dec_I :
    Natural (G:=prod W) (fun _ => dec (fun A => A)).
  Proof.
    constructor; try typeclasses eauto.
    reflexivity.
  Qed.

  Lemma dec_dec_I {A} :
    dec (fun A => A) ∘ dec (A:=A) (fun A => A) =
    map (fun A => A) (fun '(n, a) => (n, (n, a))) ∘ dec (fun A => A).
  Proof.
    intros. cbv.
    reflexivity.
  Qed.

  Lemma dec_extract_I {A} :
    map (fun A => A) (extract (W := (W ×))) ∘ dec (fun A => A) = (@id A).
  Proof.
    intros. reflexivity.
  Qed.

  #[global] Instance DecoratedFunctor_I : DecoratedFunctor W (fun A => A) :=
    {| dfun_dec_natural := Natural_dec_I;
       dfun_dec_dec := @dec_dec_I;
       dfun_dec_extract := @dec_extract_I;
    |}.

End DecoratedFunctor_I.

(** ** Decorated functors are closed under composition *)
(******************************************************************************)
Section Decoratedfunctor_composition.

  Context
    `{Monoid W}
    `{Map F} `{Map G}
    `{Decorate W F} `{Decorate W G}
    `{! DecoratedFunctor W F}
    `{! DecoratedFunctor W G}.

  #[global] Instance Decorate_compose : Decorate W (F ∘ G) :=
    fun A => map F (shift G) ∘ dec F ∘ map F (dec G).

  Instance Natural_dec_compose :
    Natural (fun A => dec (A:=A) (E:=W) (F ∘ G)).
  Proof.
    constructor; try typeclasses eauto. introv.
    unfold_ops @Map_compose. unfold map at 1.
    unfold_ops @Decorate_compose.
    (* Move << F (shift G)>> past <<F (G ∘ F) f>>. *)
    repeat reassociate <- on left.
    unfold_compose_in_compose; rewrite (fun_map_map (F := F)).
    change (map G (map (W ×) f)) with (map (G ∘ (W ×)) f).
    #[local] Set Keyed Unification.
    rewrite (shift_map2 G).
    #[local] Unset Keyed Unification.
    rewrite <- (fun_map_map (F := F)).
    (* mov <<dec F>> past <<F ∘ W ∘ G ∘ W f>> *)
    change (map F (map (prod W ∘ G ∘ prod W) f))
      with (map (F ∘ prod W) (map (G ∘ prod W) f)).
    repeat reassociate ->;
           reassociate <- near (map (F ∘ prod W) (map (G ∘ prod W) f)).
    rewrite (natural (G := F ∘ prod W) (ϕ := @dec W F _)).
    (* move <<F (dec G)>> past <<F ((G ∘ W) f)>> *)
    reassociate -> on left.
    rewrite (fun_map_map (F := F)).
    #[local] Set Keyed Unification.
    rewrite (natural (G := G ∘ prod W) (ϕ := @dec W G _)).
    #[local] Unset Keyed Unification.
    now rewrite <- (fun_map_map (F := F)).
  Qed.

  (** The next few lemmas are used to build up a proof of the
   "double decoration law", [dfun_dec_dec (F ∘ G)] *)

  (** Split the decoration wire on <<G>> into two wires with
      <<dfun_dec_dec G>> law. *)
  Lemma dec_dec_compose_1 {A} :
    (map F (map (G ∘ prod W) (cojoin (W := prod W)) ∘ strength (F := G)))
      ∘ dec F
      ∘ map F (dec G)
    = (map F (strength (F := G)))
        ∘ dec F
        ∘ map F (dec G ∘ dec G (A := A)).
  Proof.
    (* Move <<F (strength)>> past <<F ((W ○ G) (cojoin (prod W)))>> *)
    rewrite (natural (G := (G ∘ prod W)) (ϕ := @strength G _ W)).
    unfold_ops @Map_compose.
    rewrite <- (fun_map_map (F := F)).
    (* Move <<dec F>> past <<F ((W ○ G) (cojoin (prod W)))>> *)
    change (map ?F (map (prod W) ?f)) with (map (F ∘ (prod W)) f).
    reassociate -> near (dec F).
    rewrite (natural (ϕ := @dec W F _) (G := F ∘ prod W)).
    do 2 reassociate -> near (map F (dec G)).
    rewrite (fun_map_map (F := F)).
    now rewrite <- (dfun_dec_dec (E := W) (F := G)).
  Qed.

  Lemma strength_cojoin_r {A} :
    (map G (cojoin (W := (W ×))))
      ∘ strength (F := G)
    = strength (F := G)
        ∘ map (prod W) (strength (F := G))
        ∘ cojoin (W := (W ×)) (A := G A).
  Proof.
    ext [w a]. unfold strength, compose. cbn.
    compose near a. now do 2 rewrite (fun_map_map (F := G)).
  Qed.

  (** Split the decoration wire on <<F>> into two wires with
     <<dfun_dec_dec F>>. *)
  Lemma dec_dec_compose_2 {A} :
    (map F (map G (cojoin (W := prod W)) ∘ strength))
      ∘ dec F
    = (map F strength)
        ∘ dec F
        ∘ map F strength
        ∘ dec F (A := G A).
  Proof.
    rewrite strength_cojoin_r.
    rewrite <- (fun_map_map (F := F)).
    reassociate -> on left. rewrite <- (dfun_dec_dec (E := W) (F := F)).
    reassociate <- on left.
    rewrite <- (fun_map_map (F := F)).
    change (?f ∘ map F (map (prod W) strength) ∘ dec F ∘ ?g)
      with (f ∘ (map F (map (prod W) strength) ∘ dec F) ∘ g).
    change (map ?F (map ?G ?f)) with (map (F ∘ G) f).
    now rewrite (natural (ϕ := @dec W F _) (strength (B := A))).
  Qed.

  (** Slide the upper decoration wire on <<G>> past the lower
  decoration wire on <<F>>, which requires crossing them. *)
  Lemma dec_dec_compose_3 {A} :
    (map F strength)
      ∘ dec F
      ∘ map F (dec G) =
    (map (F ∘ G) (bdist (prod W) (prod W)))
      ∘ map F (dec G)
      ∘ map F strength
      ∘ dec F (A := G A).
  Proof.
    unfold_ops @BeckDistribution_strength.
    #[local] Set Keyed Unification.
    rewrite (fun_map_map (F := F)).
    rewrite (fun_map_map (F := F)).
    #[local] Unset Keyed Unification.
    reassociate -> on left. rewrite <- (natural (ϕ := @dec W F _)).
    unfold_ops @Map_compose. reassociate <- on left.
    rewrite (fun_map_map (F := F)). fequal. fequal.
    unfold compose; ext [w x]; cbn.
    compose near x. rewrite <- (natural (ϕ := @dec W G _)).
    unfold_ops @Map_compose. compose near x on right.
    reassociate <- on right. rewrite (fun_map_map (F := G)).
    unfold strength, compose, id. fequal.
    now ext [? ?].
  Qed.

  (** Re-arrange using naturality *)
  Lemma dec_dec_compose_5 : forall (A : Type),
      map F (map G (join (prod W))) ∘ map F σ ∘ dec F ∘ map F (dec G)
           ∘ (map F (map G (join (prod W))) ∘ map F strength) ∘ dec F ∘ map F (dec G)
      =
      map F (map G (join (prod W)) ∘ map G (map (prod W ∘ prod W) (join (prod W))) ∘ strength) ∘ dec F
           ∘ map F (dec G) ∘ map F σ ∘ dec F ∘ map F (dec G (A := A)).
  Proof.
    intros. fequal. fequal. reassociate <-.
    unfold_ops @Map_compose.
    change (map G (map (prod W) (map (prod W) (join (A:=?A) (prod W)))))
      with (map (G ○ prod W) (map (prod W) (join (A:=A) (prod W)))).
    reassociate -> near strength.
    rewrite (natural (ϕ := @strength G _ W)).
    rewrite <- (fun_map_map (F := F)).
    rewrite <- (fun_map_map (F := F)).
    reassociate -> near (@dec W F H2 (G (W * (prod W ∘ prod W) A))).
    change (map F (map (prod W ○ G) (map (prod W) (join (A:=?A) (prod W)))))
      with (map (F ○ prod W) (map G (map (prod W) (join (A:=A) (prod W))))).
    reassociate -> near (dec F).
    rewrite (natural (ϕ := @dec W F _)). fequal.
    do 3 reassociate <-.
    reassociate -> on right.
    rewrite (fun_map_map (F := F) _ _ _ (@dec W G _ (W * (W * A)))).
    change (map G (map (prod W) (join (A:=?A) (prod W))))
      with (map (G ∘ prod W) (join (A:=A) (prod W))).
    rewrite (natural (ϕ := @dec W G _)).
    rewrite <- (fun_map_map (F := F)) at 1.
    reflexivity.
  Qed.

  #[local] Set Keyed Unification.
  Theorem dec_dec_compose {A} :
    dec (F ∘ G) ∘ dec (F ∘ G) =
    map (F ∘ G) (cojoin (W := prod W)) ∘ dec (F ∘ G) (A:=A).
  Proof.
    intros. unfold_ops @Map_compose @Decorate_compose.
    (* Rewrite the RHS with the butterfly law *)
    do 2 reassociate <- on right. rewrite (fun_map_map (F := F)).
    unfold shift at 3.
    reassociate <- on right. rewrite (fun_map_map (F := G)).
    rewrite incr_spec.
    rewrite (Writer.bimonad_butterfly).
    (* Rewrite the outer (prod W) wire with the <<dfun_dec_dec>> law *)
    rewrite <- (fun_map_map (F := G)).
    change (map ?F (map ?G ?f)) with (map (F ∘ G) f).
    reassociate -> near (strength (F := G)). rewrite <- (fun_map_map (F := F)).
    change (?f ∘ map F (map (G ∘ prod W) cojoin ∘ strength (F := G)) ∘ dec F ∘ map F (dec G))
      with (f ∘ (map F (map (G ∘ prod W) cojoin ∘ strength (F := G)) ∘ dec F ∘ map F (dec G))).
    rewrite dec_dec_compose_1.
    (* Rewrite the outer (prod W) wire with the <<dfun_dec_dec>> law *)
    do 2 reassociate <- on right. rewrite (fun_map_map (F := F)).
    rewrite <- (fun_map_map (F := G)). reassociate -> near strength.
    rewrite <- (fun_map_map (F := F)). reassociate -> near (dec F).
    rewrite dec_dec_compose_2.
    repeat change (map ?F (map ?G ?f)) with (map (F ∘ G) f).
    (* Slide a decoration on <<F>> and one on <<G>> past each other *)
    rewrite <- (fun_map_map (F := F)). do 4 reassociate <- on right.
    do 2 reassociate <- on left.
    rewrite <- (fun_map_map (F := F ∘ G)).
    change (?f ∘ map F strength
             ∘ dec F
             ∘ map F (dec G)
             ∘ ?g) with
        (f ∘ (map F strength
                   ∘ dec F
                   ∘ map F (dec G))
           ∘ g).
    rewrite dec_dec_compose_3.
    (* Flatten out a distribution bubble. Move the second decoration on <<F>>
     out of the way to juxtapose the two distributions. *)
    rewrite (fun_map_map (F := F ∘ G)). unfold shift.
    rewrite (fun_map_map (F := F) _ _ _(@strength G _ W (W * (W * (W * A))))).
    rewrite <- (fun_map_map (F := G)).
    change (map G (map (prod W) (bdist (prod W) (prod W))))
      with (map (G ○ prod W) (bdist (A := W * A) (prod W) (prod W))).
    reassociate -> near (@strength G _ W _).
    rewrite (natural (ϕ := @strength G _ W)).
    do 4 reassociate <-.
    rewrite <- (fun_map_map (F := F) _ _ _ (map (prod W ○ G) (bdist (prod W) (prod W)))).
    change (map F (map (prod W ○ G) (bdist (A:=?A) (prod W) (prod W))))
      with (map (F ∘ prod W) (map G (bdist (A:=A) (prod W) (prod W)))).
    reassociate -> near (dec F (A := (G (W * (W * (W * A)))))).
    rewrite (natural (ϕ := @dec W F _)).
    reassociate <-.
    change (map F (map G (bdist (A:=?A) (prod W) (prod W))))
      with (map (F ∘ G) (bdist (A:=A) (prod W) (prod W))).
    reassociate -> near (map (F ∘ G) (bdist (prod W) (prod W))).
    rewrite (fun_map_map (F := F ∘ G)).
    rewrite writer_dist_involution.
    rewrite (fun_map_id (F := F ∘ G)).
    change (?x ∘ id) with x.
    (* final cleanup *)
    rewrite (natural (ϕ := @join (prod W) _)).
    rewrite <- (fun_map_map (F := G)).
    rewrite <- (fun_map_map (F := F)) at 1.
    rewrite <- (fun_map_map (F := F)) at 1.
    do 2 rewrite incr_spec.
    apply dec_dec_compose_5.
  Qed.
  #[local] Unset Keyed Unification.

  Theorem dec_extract_compose {A} :
    map (F ∘ G) (extract (W := (W ×))) ∘ dec (F ∘ G) = @id (F (G A)).
  Proof.
    intros. unfold_ops @Map_compose @Decorate_compose.
    repeat reassociate <-. unfold_compose_in_compose.
    rewrite (fun_map_map (F := F)).
    rewrite (shift_extract G).
    rewrite <- (fun_map_map (F := F)).
    do 2 reassociate -> on left.
    reassociate <- near (map (A := W * G (W * A)) F (extract (W := (W ×)) (A := G (W * A)))).
    rewrite (dfun_dec_extract (E := W) (F := F)).
    change (id ∘ ?f) with f.
    rewrite (fun_map_map (F := F)).
    rewrite (dfun_dec_extract (E := W) (F := G)).
    now rewrite (fun_map_id (F := F)).
  Qed.

  #[global] Instance DecoratedFunctor_compose : DecoratedFunctor W (F ∘ G) :=
    {| dfun_dec_natural := Natural_dec_compose;
       dfun_dec_dec := @dec_dec_compose;
       dfun_dec_extract := @dec_extract_compose;
    |}.

End Decoratedfunctor_composition.

(** ** Category laws for composition of decorated functors *)
(** Next we prove that composition of decorated functors satisfies the
    laws of a category, i.e. that composition with the identity
    decorated functor on the left or is the identity, and that
    composition is associative. This is not immediately obvious
    because in each case we must verify that the <<dec>> operation is
    the same for both sides. *)
(******************************************************************************)
Section DecoratedFunctor_composition_laws.

  Section identity_laws.

    (** Let <<T>> be a decorated functor. *)
    Context
      `{Functor T}
      `{dec_T : Decorate W T}
      `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{! DecoratedFunctor W T}
      `{! Monoid W}.

    (** *** Composition with a zero-decorated functor *)
    (** When <<F>> has a trivial decoration,
        <<dec (F ∘T)>> and <<dec (T ∘ F)>> have a special form. *)
    (******************************************************************************)
    Section zero_decorated_composition.

      (** Let <<F>> be a functor, which we will treat as zero-decorated. *)
      Context
        (F : Type -> Type)
        `{Functor F}.

      (** Composition with a zero-decorated functor on the left returns <<T>>. *)
      Theorem decorate_zero_compose_l : forall (A : Type),
          @dec W (F ∘ T) (@Decorate_compose W op F _ T _ Decorate_zero dec_T) A =
          map F (dec T).
      Proof.
        intros. unfold_ops @Decorate_compose. unfold_ops @Decorate_zero.
        do 2 rewrite (fun_map_map (F := F)).
        fequal. unfold shift.
        reassociate -> near (pair Ƶ). rewrite strength_2.
        rewrite (fun_map_map (F := T)).
        change (pair Ƶ) with (ret (W ×) (W * A)).
        rewrite incr_spec.
        rewrite (mon_join_ret (T := prod W)).
        now rewrite (fun_map_id (F := T)).
      Qed.

      (** Composition with the identity functor on the left returns <<T>>. *)
      Theorem decorate_zero_compose_r : forall (A : Type),
          @dec W (T ∘ F) (@Decorate_compose W op T _ F _ dec_T Decorate_zero) A =
          map T σ ∘ dec T.
      Proof.
        intros. unfold_ops @Decorate_compose. unfold_ops @Decorate_zero.
        reassociate -> on left.
        rewrite <- (natural (ϕ := @dec W T _)).
        reassociate <-. fequal. unfold_ops @Map_compose.
        rewrite (fun_map_map (F := T)). fequal.
        ext [w t]; unfold compose; cbn. unfold id.
        rewrite (shift_spec F). compose near t on left.
        rewrite (fun_map_map (F := F)). fequal. ext a; cbn.
        now simpl_monoid.
      Qed.

    End zero_decorated_composition.

    (** *** Composition with the identity decorated functor *)
    (******************************************************************************)
    Theorem decorate_identity_compose_l : forall (A : Type),
        @dec W ((fun A => A) ∘ T) (@Decorate_compose W op (fun A => A) _ T _ Decorate_zero dec_T) A =
        dec T.
    Proof.
      intros. now rewrite (decorate_zero_compose_l (fun A => A)).
    Qed.

    Theorem decorate_identity_compose_r : forall (A : Type),
        @dec W (T ∘ (fun A => A)) (@Decorate_compose W op T _ (fun A => A) _ dec_T Decorate_zero) A =
        dec T.
    Proof.
      intros. rewrite (decorate_zero_compose_r (fun A => A)).
      rewrite strength_I. now rewrite (fun_map_id (F := T)).
    Qed.

  End identity_laws.

  Section associativity_law.

    Context
      `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{! Monoid W}
      `{Map T1} `{Map T2} `{Map T3}
      `{dec_T1 : Decorate W T1}
      `{dec_T2 : Decorate W T2}
      `{dec_T3 : Decorate W T3}
      `{! DecoratedFunctor W T1}
      `{! DecoratedFunctor W T2}
      `{! DecoratedFunctor W T3}.

    Lemma decorate_compose_assoc1 : forall (A : Type),
        (map T2 (map T1 (μ (A:=A) (prod W)) ∘ σ ∘ μ (prod W)) ∘ σ) =
        (map T2 (map T1 (μ (W ×)) ∘ σ) ∘ σ) ∘ map ((W ×) ∘ T2) (map T1 (μ (W ×)) ∘ σ).
    Proof.
      intros. ext [w1 t]. unfold compose; cbn.
      compose near t. unfold id.
      rewrite 2(fun_map_map (F := T2)).
      compose near t on right.
      rewrite (fun_map_map (F := T2)). fequal.
      ext [w2 t2]. unfold compose; cbn. unfold id.
      compose near t2. rewrite 2(fun_map_map (F := T1)).
      do 2 (compose near t2 on right; rewrite 1(fun_map_map (F := T1))).
      fequal. ext [w3 a]. cbn. fequal. now rewrite monoid_assoc.
    Qed.

    Set Keyed Unification.
    Theorem decorate_compose_assoc : forall (A : Type),
        @dec W (T3 ∘ T2 ∘ T1)
             (@Decorate_compose W op (T3 ∘ T2) _ T1 _ _ dec_T1) A =
        @dec W (T3 ∘ T2 ∘ T1)
             (@Decorate_compose W op T3 _ (T2 ∘ T1) _ dec_T3 _) A.
    Proof.
      intros. unfold_ops @Decorate_compose; unfold dec at 1 6.
      do 2 reassociate <- on left.
      rewrite (fun_map_map (F := T3)).
      reassociate -> near (map (T3 ∘ T2) (dec T1));
        rewrite (fun_map_map (F := T3)).
      unfold shift at 1 2.
      reassociate <- on left.
      rewrite (fun_map_map (F := T2)).
      repeat rewrite incr_spec.
      rewrite decorate_compose_assoc1.
      unfold shift at 1 2.
      change (map T2 (map T1 (μ (A:=?A) (prod W)) ∘ σ) ∘ dec T2 ∘ map T2 (dec T1))
        with (map T2 (map T1 (μ (A:=A) (prod W)) ∘ σ) ∘ (dec T2 ∘ map T2 (dec T1))).
      rewrite <- (fun_map_map (F := T3) _ _ _ (dec T2 ∘ map T2 (dec T1))).
      change (H0 ?x ?y ?f) with (map T2 f).
      (* ^^ not sure why this guy got unfolded *)
      reassociate <- on right.
      repeat rewrite incr_spec.
      reassociate -> near (map T3 (map T2 (map T1 (μ (prod W)) ∘ σ))).
      rewrite <- (natural (ϕ := @dec W T3 _)).
      reassociate <- on right. fequal. fequal.
      rewrite (fun_map_map (F := T3)). fequal.
      rewrite strength_compose.
      reassociate <- on right.
      now rewrite (fun_map_map (F := T2)).
    Qed.
    Unset Keyed Unification.

  End associativity_law.

End DecoratedFunctor_composition_laws.

(** ** Composition with zero-decorated functors *)
(******************************************************************************)
Section DecoratedFunctor_zero_composition.

  Context
    (F G : Type -> Type)
    `{Monoid W}
    `{Functor F}
    `{DecoratedFunctor W G}.

  Instance: Decorate W F := Decorate_zero.

  Theorem decorate_zero_compose {A} :
    `(dec (F ∘ G) (A := A) = map F (dec G)).
  Proof.
    intros. unfold_ops @Decorate_compose.
    unfold_ops @Decorate_instance_0 @Decorate_zero.
    reassociate -> near (map F (dec G)).
    do 2 rewrite (fun_map_map (F := F)).
    reassociate <-.
    replace (shift G ∘ (fun a : G (W * A) => (Ƶ, a))) with (@id (G (W * A))).
    now reflexivity.
    ext g. unfold compose; cbn.
    now rewrite (shift_zero G).
  Qed.

End DecoratedFunctor_zero_composition.

(** * Decorated monads in terms of monad homomorphisms *)
(******************************************************************************)
Section DecoratedMonad_characterization.

  Context
    `{Categorical.Monad.Monad T} `{Decorate W T} `{Monoid W}
    `{! Categorical.DecoratedFunctor.DecoratedFunctor W T}.

  (** <<ret T>> commutes with decoration if and only if <<dec T>> maps
     <<ret T>> to <<ret (T ∘ W)>> *)
  Lemma dec_ret_iff {A} :
    (dec T ∘ ret T A = ret T (W * A) ∘ dec (fun x => x) (A:=A)) <->
    (dec T ∘ ret T A = ret (T ∘ prod W) A).
  Proof with auto.
    split...
  Qed.

  (** <<join T>> commutes with decoration if and only if <<dec T>>
     maps <<join T>> to <<join (T ∘ prod W)>> of <<dec T ∘ map T (dec T)>>
     (in other words iff <<dec T>> commutes with <<join>>). *)
  Lemma dec_join_iff {A} :
    `(dec T ∘ join T = join T ∘ dec (T ∘ T) (A := A)) <->
    `(dec T ∘ join T = join (T ∘ prod W) ∘ dec T ∘ map T (dec T (A:=A))).
  Proof.
    enough (Heq : join T ∘ dec (A := A) (T ∘ T)
                  = join (T ∘ prod W) ∘ dec T ∘ map T (dec T))
      by (split; intro hyp; now rewrite hyp).
    unfold_ops @Join_Beck @Decorate_compose @BeckDistribution_strength.
    repeat reassociate <-. fequal. fequal.
    rewrite (natural (ϕ := @join T _)).
    unfold_ops @Map_compose. reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (fun_map_map (F := T)).
    unfold shift.
    rewrite incr_spec.
    reflexivity.
  Qed.

  (* TODO Prove (T ∘ prod W) is a monad *)
  (*
  Theorem decorated_monad_compatibility_spec :
    Monad_Hom T (T ∘ prod W) (@dec W T _) <->
    DecoratePreservingTransformation (fun A => A) T (ret T) /\
    DecoratePreservingTransformation (T ∘ T) T (@join T _).
  Proof with auto.
    split.
    - introv mhom. inverts mhom. inverts mhom_domain. split.
      + constructor...
        introv. symmetry. rewrite dec_ret_iff. apply mhom_ret.
      + constructor...
        introv. symmetry. rewrite dec_join_iff. apply mhom_join.
    - intros [h1 h2]. inverts h1. inverts h2.
      constructor; try typeclasses eauto.
      + admit.
      + admit.
      + introv  rewrite <- dec_ret_iff...
      + introv. rewrite <- dec_join_iff...
  Qed.

  Theorem decorated_monad_spec :
    Categorical.DecoratedMonad.DecoratedMonad W T <->
      Monad_Hom T (T ∘ prod W) (@dec W T _).
  Proof with try typeclasses eauto.
    rewrite decorated_monad_compatibility_spec.
    split; intro hyp.
    - inversion hyp. constructor...
      + constructor... intros. now rewrite (dmon_ret (W := W) (T := T)).
      + constructor... intros. now rewrite (dmon_join (W := W) (T := T)).
    - destruct hyp as [hyp1 hyp2]. constructor...
      + intros. inversion hyp1. now rewrite dectrans_commute.
      + intros. inversion hyp2. now rewrite <- dectrans_commute.
  Qed.
   *)

End DecoratedMonad_characterization.
