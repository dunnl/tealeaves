(** This file implements "functors decorated by monoid <<W>>" and
    proves their basic properties.  *)

From Tealeaves Require Export
     Singlesorted.Classes.Monoid
     Singlesorted.Classes.Comonad
     Singlesorted.Theory.Product
     Singlesorted.Functors.Writer.

Import Product.Notations.
Import Functor.Notations.
Import Comonad.Notations.
Import Monoid.Notations.
#[local] Open Scope tealeaves_scope.

(** * Decorated functors *)
(******************************************************************************)
Section DecoratedFunctor_operations.

  Context
    (W : Type)
    (F : Type -> Type).

  Class Decorate :=
    dec : F ⇒ F ○ (W ×).

End DecoratedFunctor_operations.

Section DecoratedFunctor.

  Context
    (W : Type)
    {op : Monoid_op W}
    {unit : Monoid_unit W}
    (F : Type -> Type)
    `{Fmap F} `{Decorate W F}.

  Class DecoratedFunctor :=
    { dfun_functor :> Functor F;
      dfun_monoid : Monoid W;
      dfun_dec_natural :> Natural (@dec W F _);
      dfun_dec_dec :
        `(dec W F (W * A) ∘ dec W F A = fmap F (cojoin (prod W)) ∘ dec W F A);
      dfun_dec_extract :
        `(fmap F (extract (prod W)) ∘ dec W F A = @id (F A));
    }.

End DecoratedFunctor.

(* Mark <<W>> and the type argument implicit *)
Arguments dec {W}%type_scope _%function_scope {Decorate} {A}%type_scope _.

(** ** Decoration-preserving natural transformations *)
(******************************************************************************)
Class DecoratePreservingTransformation
      {F G : Type -> Type}
      `{! Fmap F} `{Decorate W F}
      `{! Fmap G} `{Decorate W G}
      (ϕ : F ⇒ G) :=
  { dectrans_commute : `(ϕ (W * A) ∘ dec F = dec G ∘ ϕ A);
    dectrans_natural : Natural ϕ;
  }.

(** ** The [shift] operation *)
(** The theory of decorated functors makes frequent use of an
    operation [shift] that uniformly increments the annotations of a
    W-annotated term (i.e., something of type <<F (prod W A)>> by some
    value <<w : W>>. This is used in concrete definitions of <<dec>>,
    where it is applied to recursive subcalls of <<dec>> on the bodies
    of abstractions to add the current binder to the front of the
    contexts. *)
(******************************************************************************)
Definition shift F `{Fmap F} `{Monoid_op W} {A} : W * F (W * A) -> F (W * A) :=
  fmap F (join (prod W)) ∘ strength F.

Definition map_then_shift `{Monoid_op W} T `{Fmap T} `{Decorate W T} {A B}
           (f : A -> T B) : W * A -> T (W * B) :=
  shift T ∘ fmap (prod W) (dec T ∘ f).

Section shift_functor_lemmas.

  Context
    `{Monoid W}.

  (** The definition of [shift] is convenient for theorizing, but [shift_spec]
      offers an intuitive characterization that is more convenient for
      practical reasoning. *)
  Corollary shift_spec `{Functor F} {A} : forall (w : W) (x : F (W * A)),
      shift F (w, x) = fmap F (map_fst (fun m => w ● m)) x.
  Proof.
    intros ? x. unfold shift. unfold_ops @Join_writer.
    unfold compose; cbn. compose near x on left.
    rewrite (fun_fmap_fmap F). f_equal. now ext [? ?].
  Qed.

  Lemma shift_fmap1 `{Functor F} {A B} (t : F (W * A)) (w : W) (f : A -> B) :
    shift F (w, fmap (F ∘ prod W) f t) = fmap (F ∘ prod W) f (shift F (w, t)).
  Proof.
    unfold_ops @Fmap_compose. rewrite (shift_spec).
    unfold compose; rewrite shift_spec.
    compose near t. rewrite 2(fun_fmap_fmap F).
    fequal. now ext [w' a].
  Qed.

  Lemma shift_fmap2 {A B} `{Functor F} : forall (f : A -> B),
      fmap (F ∘ prod W) f ∘ shift F =
      shift F ∘ fmap (prod W ∘ F ∘ prod W) f.
  Proof.
    intros. ext [w t]. unfold compose at 2.
    now rewrite <- shift_fmap1.
  Qed.

  Lemma shift_fmap3 {A B} `{Functor F} : forall (f : A -> B),
      fmap F (fmap (prod W) f) ∘ shift F =
      shift F ∘ fmap (prod W) (fmap F (fmap (prod W) f)).
  Proof.
    apply shift_fmap2.
  Qed.

  (* This is used in the binding case of the decorate-join law. *)
  Lemma shift_increment `{Functor F} {A} : forall (w : W),
      shift F (A := A) ∘ map_fst (fun m : W => w ● m) =
      fmap F (map_fst (fun m : W => w ● m)) ∘ shift F.
  Proof.
    intros. ext [w' a]. unfold compose. cbn. rewrite 2(shift_spec).
    compose near a on right. rewrite (fun_fmap_fmap F).
    fequal. ext [w'' a']; cbn. now rewrite monoid_assoc.
  Qed.

  (** [shift] followed by discarding annotations ([extract] i.e. [snd]) is
      equivalent to simply discarding the original annotations. *)
  Lemma shift_extract `{Functor F} {A} :
    fmap F (extract (prod W)) ∘ shift F =
    fmap F (extract (prod W)) ∘ extract (prod W) (A := F (W * A)).
  Proof.
    unfold shift. reassociate <- on left.
    ext [w t]. unfold compose; cbn.
    do 2 compose near t on left.
    do 2 rewrite (fun_fmap_fmap F).
    fequal. now ext [w' a].
  Qed.

  Lemma shift_zero `{Functor F} {A} : forall (t : F (W * A)),
    shift F (Ƶ, t) = t.
  Proof.
    intros. rewrite shift_spec.
    cut (map_fst (Y := A) (fun w => Ƶ ● w) = id).
    intros rw; rewrite rw. now rewrite (fun_fmap_id F).
    ext [w a]. cbn. now simpl_monoid.
  Qed.

End shift_functor_lemmas.

(** ** Helper lemmas for proving typeclass instances *)
(** Each of the following lemmas is useful for proving one of the laws
    of decorated functors in the binder case(s) of proofs that proceed
    by induction on terms. *)
(******************************************************************************)
Section helper_lemmas.

  Context
    `{Functor F}
    `{Decorate W F}
    `{Monoid W}.

  (** This lemmasis useful for proving naturality of <<dec>>. *)
  Lemma dec_helper_1 {A B} : forall (f : A -> B) (t : F A) (w : W),
      fmap F (fmap (prod W) f) (dec F t) =
      dec F (fmap F f t) ->
      fmap F (fmap (prod W) f) (shift F (w, dec F t)) =
      shift F (w, dec F (fmap F f t)).
  Proof.
    introv IH. (* there is a hidden compose to unfold *)
    unfold compose; rewrite 2(shift_spec).
    compose near (dec F t) on left. rewrite (fun_fmap_fmap F).
    rewrite <- IH.
    compose near (dec F t) on right. rewrite (fun_fmap_fmap F).
    fequal. now ext [w' a].
  Qed.

  (** Now we can assume that <<dec>> is a natural transformation,
      which is needed for the following. *)
  Context
    `{! Natural (@dec W F _)}.

  (** This lemmas is useful for proving the dec-extract law. *)
  Lemma dec_helper_2 {A} : forall (t : F A) (w : W),
      fmap F (extract (prod W)) (dec F t) = t ->
      fmap F (extract (prod W)) (shift F (w, dec F t)) = t.
  Proof.
    intros.
    compose near (w, dec F t).
    rewrite (shift_extract). unfold compose; cbn.
    auto.
  Qed.

  (** This lemmas is useful for proving the double decoration law. *)
  Lemma dec_helper_3 {A} : forall (t : F A) (w : W),
      dec F (dec F t) = fmap F (cojoin (prod W)) (dec F t) ->
      shift F (w, dec F (shift F (w, dec F t))) =
      fmap F (cojoin (prod W)) (shift F (w, dec F t)).
  Proof.
    introv IH. unfold compose. rewrite 2(shift_spec).
    compose near (dec F t).
    rewrite <- (natural (F := F) (G := F ○ prod W)).
    unfold compose. compose near (dec F (dec F t)).
    rewrite IH. unfold_ops @Fmap_compose.
    rewrite (fun_fmap_fmap F).
    compose near (dec F t).
    rewrite (fun_fmap_fmap F).
    rewrite (fun_fmap_fmap F).
    unfold compose. fequal.
    now ext [w' a].
  Qed.

  (** This lemmas is useful for proving the decoration-join law. *)
  Lemma dec_helper_4 `{Monad T} `{Decorate W T} {A} : forall (t : T (T A)) (w : W),
      dec T (join T t) =
      join T (fmap T (shift T) (dec T (fmap T (dec T) t))) ->
      shift T (w, dec T (join T t)) =
      join T (fmap T (shift T) (shift T (w, dec T (fmap T (dec T) t)))).
  Proof.
    introv IH. rewrite !(shift_spec) in *. rewrite IH.
    compose near (dec T (fmap T (dec T) t)) on right.
    rewrite (fun_fmap_fmap T). rewrite (shift_increment).
    rewrite <- (fun_fmap_fmap T).
    change (fmap T (fmap T ?f)) with (fmap (T ∘ T) f).
    compose near (dec T (fmap T (dec T) t)).
    reassociate <-.
    #[local] Set Keyed Unification.
    now rewrite <- (natural (ϕ := @join T _)).
    #[local] Unset Keyed Unification.
  Qed.

End helper_lemmas.

(** ** Zero-decorated functors *)
(** Every functor is trivially decorated using the operation that
    pairs each leaf with the unit of the monoid. We call such functors
    zero-decorated. This allows us to see _all_ functors as (maybe
    trivially) decorated. *)
(******************************************************************************)
Section DecoratedFunctor_Zero.

  Context
    `{Monoid W}
    `{Functor F}.

  Instance Decorate_zero : Decorate W F :=
    fun A => fmap F (pair Ƶ).

  Instance Natural_dec_zero :
    Natural (@dec W F _).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Fmap_compose @Decorate_zero.
    now do 2 rewrite (fun_fmap_fmap F).
  Qed.

  Lemma dec_dec_zero {A} :
    dec F ∘ dec F (A:=A) =
    fmap F (cojoin (prod W)) ∘ dec F.
  Proof.
    intros. unfold_ops @Decorate_zero.
    now do 2 rewrite (fun_fmap_fmap F).
  Qed.

  Lemma dec_extract_zero {A} :
    fmap F (extract (prod W)) ∘ dec F = @id (F A).
  Proof.
    intros. unfold_ops @Decorate_zero.
    rewrite (fun_fmap_fmap F).
    unfold compose; cbn.
    now rewrite (fun_fmap_id F).
  Qed.

  Instance DecoratedFunctor_zero : DecoratedFunctor W F :=
    {| dfun_dec_natural := Natural_dec_zero;
       dfun_dec_dec := @dec_dec_zero;
       dfun_dec_extract := @dec_extract_zero;
    |}.

End DecoratedFunctor_Zero.

(** * Decorated functors form a monoidal category *)
(******************************************************************************)

(** ** The identity (zero-)decorated functor *)
(******************************************************************************)
Section DecoratedFunctor_I.

  Context
    `{Monoid W}.

  Definition dec_I : forall A, A -> prod W A :=
    fun A => pair Ƶ.

  #[global] Instance Decorate_I : Decorate W (fun A => A) := dec_I.

  #[global] Instance Natural_dec_I :
    Natural (G:=prod W) (fun _ => dec (fun A => A)).
  Proof.
    constructor; try typeclasses eauto.
    reflexivity.
  Qed.

  Lemma dec_dec_I {A} :
    dec (fun A => A) ∘ dec (A:=A) (fun A => A) =
    fmap (fun A => A) (fun '(n, a) => (n, (n, a))) ∘ dec (fun A => A).
  Proof.
    intros. cbv.
    reflexivity.
  Qed.

  Lemma dec_extract_I {A} :
    fmap (fun A => A) (extract (prod W)) ∘ dec (fun A => A) = (@id A).
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
    `{Fmap F} `{Fmap G}
    `{Decorate W F} `{Decorate W G}
    `{! DecoratedFunctor W F}
    `{! DecoratedFunctor W G}.

  #[global] Instance Decorate_compose : Decorate W (F ∘ G) :=
    fun A => fmap F (shift G) ∘ dec F ∘ fmap F (dec G).

  Instance Natural_dec_compose :
    Natural (fun A => dec (A:=A) (W:=W) (F ∘ G)).
  Proof.
    constructor; try typeclasses eauto. introv.
    unfold_ops @Fmap_compose. unfold fmap at 1.
    unfold_ops @Decorate_compose.
    (* Move << F (shift G)>> past <<F (G ∘ F) f>>. *)
    repeat reassociate <- on left.
    unfold_compose_in_compose; rewrite (fun_fmap_fmap F).
    rewrite shift_fmap3.
    rewrite <- (fun_fmap_fmap F).
    (* mov <<dec F>> past <<F ∘ W ∘ G ∘ W f>> *)
    change (fmap G (fmap (prod W) ?f)) with (fmap (G ∘ prod W) f).
    change (fmap F (fmap (prod W) ?f)) with (fmap (F ∘ prod W) f).
    repeat reassociate ->;
           reassociate <- near (fmap (F ∘ prod W) (fmap (G ∘ prod W) f)).
    rewrite (natural (G := F ∘ prod W) (ϕ := @dec W F _)).
    (* move <<F (dec G)>> past <<F ((G ∘ W) f)>> *)
    reassociate -> on left.
    rewrite (fun_fmap_fmap F).
    #[local] Set Keyed Unification.
    rewrite (natural (G := G ∘ prod W) (ϕ := @dec W G _)).
    #[local] Unset Keyed Unification.
    rewrite <- (fun_fmap_fmap F).
    reflexivity.
  Qed.

  (** The next few lemmas are used to build up a proof of the
   "double decoration law", [dfun_dec_dec (F ∘ G)] *)

  (** Split the decoration wire on <<G>> into two wires with
      <<dfun_dec_dec G>> law. *)
  Lemma dec_dec_compose_1 {A} :
    (fmap F (fmap (G ∘ prod W) (cojoin (prod W)) ∘ strength G))
      ∘ dec F
      ∘ fmap F (dec G)
    = (fmap F (strength G))
        ∘ dec F
        ∘ fmap F (dec G ∘ dec G (A := A)).
  Proof.
    (* Move <<F (strength)>> past <<F ((W ○ G) (cojoin (prod W)))>> *)
    rewrite (natural (G := (G ∘ prod W)) (ϕ := @strength G _ W)).
    unfold_ops @Fmap_compose.
    rewrite <- (fun_fmap_fmap F).
    (* Move <<dec F>> past <<F ((W ○ G) (cojoin (prod W)))>> *)
    change (fmap ?F (fmap (prod W) ?f)) with (fmap (F ∘ (prod W)) f).
    reassociate -> near (dec F).
    rewrite (natural (ϕ := @dec W F _) (G := F ∘ prod W)).
    do 2 reassociate -> near (fmap F (dec G)).
    rewrite (fun_fmap_fmap F).
    now rewrite <- (dfun_dec_dec W G).
  Qed.

  Lemma strength_cojoin_r {A} :
    (fmap G (cojoin (prod W)))
      ∘ strength G
    = (strength G)
        ∘ fmap (prod W) (strength G)
        ∘ cojoin (prod W) (A := G A).
  Proof.
    ext [w a]. unfold strength, compose. cbn.
    compose near a. now do 2 rewrite (fun_fmap_fmap G).
  Qed.

  (** Split the decoration wire on <<F>> into two wires with
     <<dfun_dec_dec F>>. *)
  Lemma dec_dec_compose_2 {A} :
    (fmap F (fmap G (cojoin (prod W)) ∘ strength G))
      ∘ dec F
    = (fmap F (strength G))
        ∘ dec F
        ∘ fmap F (strength G)
        ∘ dec F (A := G A).
  Proof.
    rewrite strength_cojoin_r.
    rewrite <- (fun_fmap_fmap F).
    reassociate -> on left. rewrite <- (dfun_dec_dec W F).
    reassociate <- on left.
    rewrite <- (fun_fmap_fmap F).
    change (?f ∘ fmap F (fmap (prod W) (strength G)) ∘ dec F ∘ ?g)
      with (f ∘ (fmap F (fmap (prod W) (strength G)) ∘ dec F) ∘ g).
    change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f).
    now rewrite (natural (ϕ := @dec W F _) (strength G (B := A))).
  Qed.

  (** Slide the upper decoration wire on <<G>> past the lower
  decoration wire on <<F>>, which requires crossing them. *)
  Lemma dec_dec_compose_3 {A} :
    (fmap F (strength G))
      ∘ dec F
      ∘ fmap F (dec G) =
    (fmap (F ∘ G) (bdist (prod W) (prod W)))
      ∘ fmap F (dec G)
      ∘ fmap F (strength G)
      ∘ dec F (A := G A).
  Proof.
    unfold_ops @BeckDistribution_strength.
    #[local] Set Keyed Unification.
    rewrite (fun_fmap_fmap F).
    rewrite (fun_fmap_fmap F).
    #[local] Unset Keyed Unification.
    reassociate -> on left. rewrite <- (natural (ϕ := @dec W F _)).
    unfold_ops @Fmap_compose. reassociate <- on left.
    rewrite (fun_fmap_fmap F). fequal. fequal.
    unfold compose; ext [w x]; cbn.
    compose near x. rewrite <- (natural (ϕ := @dec W G _)).
    unfold_ops @Fmap_compose. compose near x on right.
    reassociate <- on right. rewrite (fun_fmap_fmap G).
    unfold strength, compose, id. fequal.
    now ext [? ?].
  Qed.

  (** Re-arrange using naturality *)
  Lemma dec_dec_compose_5 : forall (A : Type),
      fmap F (fmap G (join (prod W))) ∘ fmap F (strength G) ∘ dec F ∘ fmap F (dec G)
           ∘ (fmap F (fmap G (join (prod W))) ∘ fmap F (strength G)) ∘ dec F ∘ fmap F (dec G)
      =
      fmap F (fmap G (join (prod W)) ∘ fmap G (fmap (prod W ∘ prod W) (join (prod W))) ∘ strength G) ∘ dec F
           ∘ fmap F (dec G) ∘ fmap F (strength G) ∘ dec F ∘ fmap F (dec G (A := A)).
  Proof.
    intros. fequal. fequal. reassociate <-.
    unfold_ops @Fmap_compose.
    change (fmap G (fmap (prod W) (fmap (prod W) (join (A:=?A) (prod W)))))
      with (fmap (G ○ prod W) (fmap (prod W) (join (A:=A) (prod W)))).
    reassociate -> near (strength G).
    rewrite (natural (ϕ := @strength G _ W)).
    rewrite <- (fun_fmap_fmap F).
    rewrite <- (fun_fmap_fmap F).
    reassociate -> near (@dec W F H2 (G (W * (prod W ∘ prod W) A))).
    change (fmap F (fmap (prod W ○ G) (fmap (prod W) (join (A:=?A) (prod W)))))
      with (fmap (F ○ prod W) (fmap G (fmap (prod W) (join (A:=A) (prod W))))).
    reassociate -> near (dec F).
    rewrite (natural (ϕ := @dec W F _)). fequal.
    do 3 reassociate <-.
    reassociate -> on right.
    rewrite (fun_fmap_fmap F (f := @dec W G _ (W * (W * A)))).
    change (fmap G (fmap (prod W) (join (A:=?A) (prod W))))
      with (fmap (G ∘ prod W) (join (A:=A) (prod W))).
    rewrite (natural (ϕ := @dec W G _)).
    rewrite <- (fun_fmap_fmap F) at 1.
    reflexivity.
  Qed.

  #[local] Set Keyed Unification.
  Theorem dec_dec_compose {A} :
    dec (F ∘ G) ∘ dec (F ∘ G) =
    fmap (F ∘ G) (cojoin (prod W)) ∘ dec (F ∘ G) (A:=A).
  Proof.
    intros. unfold_ops @Fmap_compose @Decorate_compose.
    (* Rewrite the RHS with the butterfly law *)
    do 2 reassociate <- on right. rewrite (fun_fmap_fmap F).
    unfold shift at 3.
    reassociate <- on right. rewrite (fun_fmap_fmap G).
    rewrite (Writer.bimonad_butterfly).
    (* Rewrite the outer (prod W) wire with the <<dfun_dec_dec>> law *)
    rewrite <- (fun_fmap_fmap G).
    change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f).
    reassociate -> near (strength G). rewrite <- (fun_fmap_fmap F).
    change (?f ∘ fmap F (fmap (G ∘ prod W) (cojoin (prod W)) ∘ strength G) ∘ dec F ∘ fmap F (dec G))
      with (f ∘ (fmap F (fmap (G ∘ prod W) (cojoin (prod W)) ∘ strength G) ∘ dec F ∘ fmap F (dec G))).
    rewrite dec_dec_compose_1.
    (* Rewrite the outer (prod W) wire with the <<dfun_dec_dec>> law *)
    do 2 reassociate <- on right. rewrite (fun_fmap_fmap F).
    rewrite <- (fun_fmap_fmap G). reassociate -> near (strength G).
    rewrite <- (fun_fmap_fmap F). reassociate -> near (dec F).
    rewrite (dec_dec_compose_2).
    repeat change (fmap ?F (fmap ?G ?f)) with (fmap (F ∘ G) f).
    (* Slide a decoration on <<F>> and one on <<G>> past each other *)
    rewrite <- (fun_fmap_fmap F). do 4 reassociate <- on right.
    do 2 reassociate <- on left.
    rewrite <- (fun_fmap_fmap (F ∘ G)).
    change (?f ∘ fmap F (strength G)
             ∘ dec F
             ∘ fmap F (dec G)
             ∘ ?g) with
        (f ∘ (fmap F (strength G)
                   ∘ dec F
                   ∘ fmap F (dec G))
           ∘ g).
    rewrite (dec_dec_compose_3).
    (* Flatten out a distribution bubble. Move the second decoration on <<F>>
     out of the way to juxtapose the two distributions. *)
    rewrite (fun_fmap_fmap (F ∘ G)). unfold shift.
    rewrite (fun_fmap_fmap F (f := @strength G _ W (W * (W * (W * A))))).
    rewrite <- (fun_fmap_fmap G).
    change (fmap G (fmap (prod W) (bdist (prod W) (prod W))))
      with (fmap (G ○ prod W) (bdist (A := W * A) (prod W) (prod W))).
    reassociate -> near (@strength G _ W _).
    rewrite (natural (ϕ := @strength G _ W)).
    do 4 reassociate <-.
    rewrite <- (fun_fmap_fmap F (f := fmap (prod W ○ G) (bdist (prod W) (prod W)))).
    change (fmap F (fmap (prod W ○ G) (bdist (A:=?A) (prod W) (prod W))))
      with (fmap (F ∘ prod W) (fmap G (bdist (A:=A) (prod W) (prod W)))).
    reassociate -> near (dec F (A := (G (W * (W * (W * A)))))).
    rewrite (natural (ϕ := @dec W F _)).
    reassociate <-.
    change (fmap F (fmap G (bdist (A:=?A) (prod W) (prod W))))
      with (fmap (F ∘ G) (bdist (A:=A) (prod W) (prod W))).
    reassociate -> near (fmap (F ∘ G) (bdist (prod W) (prod W))).
    rewrite (fun_fmap_fmap (F ∘ G)).
    rewrite (writer_dist_involution).
    rewrite (fun_fmap_id (F ∘ G)).
    change (?x ∘ id) with x.
    (* final cleanup *)
    rewrite (natural (ϕ := @join (prod W) _)).
    rewrite <- (fun_fmap_fmap G).
    rewrite <- (fun_fmap_fmap F) at 1.
    rewrite <- (fun_fmap_fmap F) at 1.
    apply dec_dec_compose_5.
  Qed.
  #[local] Unset Keyed Unification.

  Theorem dec_extract_compose {A} :
    fmap (F ∘ G) (extract (prod W)) ∘ dec (F ∘ G) = @id (F (G A)).
  Proof.
    intros. unfold_ops @Fmap_compose @Decorate_compose.
    repeat reassociate <-. unfold_compose_in_compose.
    rewrite (fun_fmap_fmap F).
    rewrite shift_extract.
    rewrite <- (fun_fmap_fmap F).
    do 2 reassociate -> on left.
    reassociate <- near (fmap (A:=W * G (W * A)) F (extract (prod W))).
    rewrite (dfun_dec_extract W F).
    change (id ∘ ?f) with f.
    rewrite (fun_fmap_fmap F).
    rewrite (dfun_dec_extract W G).
    now rewrite (fun_fmap_id F).
  Qed.

  #[global] Instance DecoratedFunctor_compose : DecoratedFunctor W (F ∘ G) :=
    {| dfun_dec_natural := Natural_dec_compose;
       dfun_dec_dec := @dec_dec_compose;
       dfun_dec_extract := @dec_extract_compose;
       dfun_monoid := dfun_monoid W F;
    |}.

End Decoratedfunctor_composition.

(** ** Composition monoid laws *)
(******************************************************************************)
Section DecoratedFunctor_composition_laws.

  Section identity_laws.

    Context
      `{Functor T}
      `{dec_T : Decorate W T}
      `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{! DecoratedFunctor W T}
      `{! Monoid W}
      `{Functor F}.

    Theorem decorate_compose_l : forall (A : Type),
        @dec W (F ∘ T) (@Decorate_compose W op F _ T _ Decorate_zero dec_T) A =
        fmap F (dec T).
    Proof.
      intros. unfold_ops @Decorate_compose. unfold_ops @Decorate_zero.
      do 2 rewrite (fun_fmap_fmap F).
      fequal. unfold shift.
      reassociate -> near (pair Ƶ). rewrite (strength_2).
      rewrite (fun_fmap_fmap T).
      change (pair Ƶ) with (ret (W ×) (A := W * A)).
      rewrite (mon_join_ret (prod W)).
      now rewrite (fun_fmap_id T).
    Qed.

    Theorem decorate_compose_r : forall (A : Type),
        @dec W (T ∘ F) (@Decorate_compose W op T _ F _ dec_T Decorate_zero) A =
        fmap T (σ F) ∘ dec T.
    Proof.
      intros. unfold_ops @Decorate_compose. unfold_ops @Decorate_zero.
      reassociate -> on left.
      rewrite <- (natural (ϕ := @dec W T _)).
      reassociate <-. fequal. unfold_ops @Fmap_compose.
      rewrite (fun_fmap_fmap T). fequal.
      ext [w t]; unfold compose; cbn. unfold id.
      rewrite shift_spec. compose near t on left.
      rewrite (fun_fmap_fmap F). fequal. ext a; cbn.
      now simpl_monoid.
    Qed.

  End identity_laws.

  Section associativity_law.

    Context
      `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Fmap T1} `{Fmap T2} `{Fmap T3}
      `{dec_T1 : Decorate W T1}
      `{dec_T2 : Decorate W T2}
      `{dec_T3 : Decorate W T3}
      `{! DecoratedFunctor W T1}
      `{! DecoratedFunctor W T2}
      `{! DecoratedFunctor W T3}.

    Theorem decorate_compose_assoc : forall (A : Type),
        @dec W (T3 ∘ T2 ∘ T1)
             (@Decorate_compose W op (T3 ∘ T2) _ T1 _ _ dec_T1) A =
        @dec W (T3 ∘ T2 ∘ T1)
             (@Decorate_compose W op T3 _ (T2 ∘ T1) _ dec_T3 _) A.
    Proof.
      intros. unfold_ops @Decorate_compose.
      unfold dec at 1 6.
      - rewrite <- (fun_fmap_fmap T3). repeat reassociate <-.
        fequal.
        rewrite <- (fun_fmap_fmap T3). repeat reassociate <-.
        fequal.
        reassociate -> on right.
        rewrite <- (natural (ϕ := @dec W T3 _)). reassociate <-.
        fequal. Set Keyed Unification.
        rewrite (fun_fmap_fmap T3).
        rewrite (fun_fmap_fmap T3). fequal.
    Abort.

  End associativity_law.

End DecoratedFunctor_composition_laws.

(** ** Composition with zero-decorated functors *)
(******************************************************************************)
Section DecoratedFunctor_zero_composition.

  Context
    (F G : Type -> Type)
    `{Functor F}
    `{DecoratedFunctor W G}.

  Instance: Decorate W F := Decorate_zero.

  Existing Instance dfun_monoid.

  Theorem decorate_zero_compose :
    `(dec (F ∘ G) (A := A) = fmap F (dec G)).
  Proof.
    intros. unfold_ops @Decorate_compose.
    unfold_ops @Decorate_instance_0 @Decorate_zero.
    reassociate -> near (fmap F (dec G)).
    do 2 rewrite (fun_fmap_fmap F).
    reassociate <-.
    replace (shift G ∘ (fun a : G (W * A) => (Ƶ, a))) with (@id (G (W * A))).
    now reflexivity.
    ext g. unfold compose; cbn.
    now rewrite (shift_zero).
  Qed.

End DecoratedFunctor_zero_composition.

(** * Decorated functor instance for Writer *)
(******************************************************************************)
Section DecoratedFunctor_writer.

  Context
    `{Monoid W}.

  #[global] Instance Decorate_prod : Decorate W (prod W) := @cojoin (prod W) _.

  #[global, program] Instance DecoratedFunctor_prod : DecoratedFunctor W (prod W).

  Solve Obligations with (intros; now ext [? ?]).

End DecoratedFunctor_writer.

(** * Kleisli presentation of decorated functors *)
(******************************************************************************)

(** ** Kleisli lifting operation <<fmapd>>  *)
(******************************************************************************)
Definition fmapd F `{Fmap F} `{Decorate W F} {A B} (f : W * A -> B) : F A -> F B :=
  fmap F f ∘ dec F.

(** ** Specification for <<fmap>>  *)
(******************************************************************************)
Section decoratedfunctor_suboperations.

  Context
    (F : Type -> Type)
    `{DecoratedFunctor W F}.

  (** *** [fmap] as a special case of [fmapd] *)
  Theorem fmap_to_fmapd {A B} : forall (f : A -> B),
      fmap F f = fmapd F (f ∘ extract (prod W)).
  Proof.
    introv. unfold fmapd.
    rewrite <- (fun_fmap_fmap F).
    reassociate -> on right.
    now rewrite (dfun_dec_extract W F).
  Qed.

End decoratedfunctor_suboperations.

(** ** Interaction of [dec] and [fmapd], [fmap] *)
(******************************************************************************)
Section decoratedfunctor_dec_fmapd.

  Context
    (F : Type -> Type)
    `{DecoratedFunctor W F}.

  Theorem dec_fmapd {A B}: forall (f : W * A -> B),
      dec F ∘ fmapd F f = fmapd F (cobind (prod W) f).
  Proof.
    introv. unfold fmapd.
    reassociate <- on left.
    rewrite <- (natural (G := F ○ prod W)).
    reassociate -> on left.
    rewrite (dfun_dec_dec W F).
    reassociate <- on left.
    unfold transparent tcs. rewrite (fun_fmap_fmap F).
    reflexivity.
  Qed.

  Theorem dec_fmap {A B}: forall (f : A -> B),
      dec F ∘ fmap F f = fmap F (fmap (prod W) f) ∘ dec F.
  Proof.
    introv. now rewrite <- (natural (G := F ○ prod W)).
  Qed.

End decoratedfunctor_dec_fmapd.

(** ** Functoriality of [fmapd] *)
(******************************************************************************)
Section fmapd_functoriality.

  Context
    (F : Type -> Type)
    `{DecoratedFunctor W F}.

  Theorem fmapd_id {A} : fmapd F (extract _) = @id (F A).
  Proof.
    introv. apply (dfun_dec_extract W F).
  Qed.

  Theorem fmapd_fmapd {A B C} (f : W * A -> B) (g : W * B -> C) :
    fmapd F g ∘ fmapd F f = fmapd F (g co⋆ f).
  Proof.
    intros. unfold fmapd.
    reassociate <- on left.
    reassociate -> near (fmap F f).
    rewrite <- (natural (G := F ○ prod W)).
    reassociate <- on left.
    unfold transparent tcs.
    rewrite (fun_fmap_fmap F).
    reassociate -> on left.
    rewrite (dfun_dec_dec W F).
    reassociate <- on left.
    rewrite (fun_fmap_fmap F).
    reflexivity.
  Qed.

End fmapd_functoriality.

(** ** Composition laws for <<fmapd>>/<<fmap>> *)
(******************************************************************************)
Section fmapd_suboperation_composition.

  Context
    (F : Type -> Type)
    `{DecoratedFunctor W F}.

  Corollary fmap_fmapd {A B C} : forall (g : B -> C) (f : W * A -> B),
    fmap F g ∘ fmapd F f = fmapd F (g ∘ f).
  Proof.
    introv. rewrite (fmap_to_fmapd F), (fmapd_fmapd F).
    do 2 fequal. now ext [w a].
  Qed.

  Corollary fmapd_fmap {A B C} : forall (g : W * B -> C) (f : A -> B),
      fmapd F g ∘ fmap F f = fmapd F (g ∘ map_snd f).
  Proof.
    introv. rewrite (fmap_to_fmapd F), (fmapd_fmapd F).
    fequal. now ext [w a].
  Qed.

End fmapd_suboperation_composition.
