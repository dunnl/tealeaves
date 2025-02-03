(** This file implements "monads decorated by monoid <<W>>." *)
From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.DecoratedFunctor
  Classes.Categorical.RightModule
  Functors.Early.Writer.

Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables W T F.

#[local] Arguments ret (T)%function_scope {Return}
  (A)%type_scope _.
#[local] Arguments join T%function_scope {Join}
  (A)%type_scope _.
#[local] Arguments map F%function_scope {Map}
  {A B}%type_scope f%function_scope _.
#[local] Arguments extract (W)%function_scope {Extract}
  (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin}
  {A}%type_scope _.

(** * The [shift] operation *)
(* uncurry (incr W) = join (W ×) *)
(**********************************************************************)
Definition shift (F: Type -> Type) `{Map F} `{Monoid_op W} {A}:
  W * F (W * A) -> F (W * A) := map F (uncurry incr) ∘ strength.

(** ** Basic Properties of [shift] *)
(**********************************************************************)
Section shift_functor_lemmas.

  Context
    (F: Type -> Type)
    `{Monoid W}
    `{Functor F}.

  (** The definition of [shift] is convenient for theorizing, but
      [shift_spec] offers an intuitive characterization that is more
      convenient for practical reasoning. *)
  Corollary shift_spec {A}: forall (w: W) (x: F (W * A)),
      shift F (w, x) = map F (map_fst (fun m => w ● m)) x.
  Proof.
    intros ? x. unfold shift. unfold_ops @Join_writer.
    unfold compose; cbn. compose near x on left.
    rewrite fun_map_map.
    reflexivity.
  Qed.

  Corollary shift_spec2 {A: Type}:
    shift F (A := A) = map F (join (W ×) A) ∘ strength.
  Proof.
    intros.
    unfold shift.
    rewrite incr_spec.
    reflexivity.
  Qed.

  (** If we think of <<shift>> as a function of two arguments,
      then it is natural in its second argument. *)
  Lemma shift_map1 {A B} (t: F (W * A)) (w: W) (f: A -> B):
    shift F (w, map (F ∘ prod W) f t)
    = map (F ∘ prod W) f (shift F (w, t)).
  Proof.
    unfold_ops @Map_compose.
    rewrite shift_spec.
    unfold compose.
    rewrite shift_spec.
    compose near t.
    rewrite 2(fun_map_map).
    unfold_ops @Map_reader.
    rewrite product_map_slide_pf.
    reflexivity.
  Qed.

  (** We can also say <<shift>> is a natural transformation
      of type <<(W ×) ∘ F ∘ (W ×) \to F ∘ (W ×)>>. *)
  Lemma shift_map2 {A B}: forall (f: A -> B),
      map (F ∘ prod W) f ∘ shift F =
        shift F ∘ map (prod W ∘ F ∘ prod W) f.
  Proof.
    intros. ext [w t]. unfold compose at 2.
    now rewrite <- shift_map1.
  Qed.

  Corollary shift_natural: Natural (@shift F _ W _).
  Proof.
    constructor; try typeclasses eauto.
    intros. apply shift_map2.
  Qed.

  (** We can increment the first argument before applying <<shift>>,
      or we can <<shift>> and then increment. This lemma is used
      e.g. in the binding case of the decorate-join law. *)
  Lemma shift_increment {A}: forall (w: W),
      shift F (A := A) ∘ map_fst (fun m: W => w ● m) =
        map F (map_fst (fun m: W => w ● m)) ∘ shift F.
  Proof.
    intros. ext [w' a]. unfold compose. cbn. rewrite 2(shift_spec).
    compose near a on right. rewrite fun_map_map.
    fequal. ext [w'' a']; cbn. now rewrite monoid_assoc.
  Qed.

  (** Applying <<shift>>, followed by discarding annotations at the
      leaves, is equivalent to simply discarding the original
      annotations and the argument to <<shift>>. *)
  Lemma shift_extract {A}:
    map F (extract (prod W) A) ∘ shift F =
      map F (extract (prod W) A) ∘ extract (prod W) (F (W * A)).
  Proof.
    unfold shift. reassociate <- on left.
    ext [w t]. unfold compose; cbn.
    do 2 compose near t on left.
    do 2 rewrite fun_map_map.
    fequal. now ext [w' a].
  Qed.

  Lemma shift_zero {A}: forall (t: F (W * A)),
      shift F (Ƶ, t) = t.
  Proof.
    intros. rewrite shift_spec.
    cut (map_fst (Y := A) (fun w => Ƶ ● w) = id).
    intros rw; rewrite rw. now rewrite fun_map_id.
    ext [w a]. cbn. now simpl_monoid.
  Qed.

End shift_functor_lemmas.

From Tealeaves Require Import
  Classes.Categorical.RightComodule.

(** * Decorated Monads *)
(**********************************************************************)
Class DecoratedMonad
  (W: Type)
  (T: Type -> Type)
  `{Map T} `{Return T} `{Join T} `{Decorate W T}
  `{Monoid_op W} `{Monoid_unit W} :=
  { dmon_functor :> DecoratedFunctor W T;
    dmon_monad :> Monad T;
    dmon_monoid :> Monoid W;
    dmon_ret: forall (A: Type),
      dec T ∘ ret T A = ret T (W * A) ∘ pair Ƶ;
    dmon_join: forall (A: Type),
      dec T ∘ join T A =
        join T (W * A) ∘ map T (shift T) ∘ dec T ∘ map T (dec T);
  }.

(** * Decorated Right Modules *)
(**********************************************************************)
Section DecoratedModule.

  Context
    (W: Type)
    (F T: Type -> Type)
    `{Map T} `{Return T} `{Join T} `{Decorate W T}
    `{Map F} `{RightAction F T} `{Decorate W F}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedRightModule :=
    { dmod_monad :> DecoratedMonad W T;
      dmod_functor :> DecoratedFunctor W T;
      dmon_module :> Categorical.RightModule.RightModule F T;
      dmod_action: forall (A: Type),
        dec F ∘ right_action F (A := A) =
          right_action F ∘ map F (shift T) ∘ dec F ∘ map F (dec T);
    }.

End DecoratedModule.

(** * Basic Properties of [shift] on Monads *)
(**********************************************************************)
Section shift_monad_lemmas.

  #[local] Generalizable Variables A.

  Context
    `{Monad T}
    `{Monoid W}.

  (** [shift] applied to a singleton simplifies to a singleton. *)
  Lemma shift_return `(a: A) (w1 w2: W):
    shift T (w2, ret T _ (w1, a)) = ret T _ (w2 ● w1, a).
  Proof.
    unfold shift, compose. rewrite strength_return.
    compose near (w2, (w1, a)) on left.
    now rewrite (natural (F := fun A => A)).
  Qed.

  Lemma shift_join `(t: T (T (W * A))) (w: W):
    shift T (w, join T (W * A) t) =
      join T (W * A) (map T (fun t => shift T (w, t)) t).
  Proof.
    rewrite (shift_spec T). compose near t on left.
    rewrite natural. unfold compose; cbn.
    fequal. unfold_ops @Map_compose.
    fequal. ext x. now rewrite (shift_spec T).
  Qed.

End shift_monad_lemmas.

(** ** Helper Lemmas for Proving Typeclass Instances *)
(** Each of the following lemmas is useful for proving one of the laws
    of decorated functors in the binder case(s) of proofs that proceed
    by induction on terms. *)
(**********************************************************************)
Section helper_lemmas.

  Context
    `{Functor F}
    `{Decorate W F}
    `{Monoid W}.

  (** This lemma is useful for proving naturality of <<dec>>. *)
  Lemma dec_helper_1 {A B}: forall (f: A -> B) (t: F A) (w: W),
      map F (map (prod W) f) (dec F t) =
        dec F (map F f t) ->
      map F (map (prod W) f) (shift F (w, dec F t)) =
        shift F (w, dec F (map F f t)).
  Proof.
    introv IH. (* there is a hidden compose to unfold *)
    unfold compose; rewrite 2(shift_spec F).
    compose near (dec F t) on left. rewrite (fun_map_map).
    rewrite <- IH.
    compose near (dec F t) on right. rewrite (fun_map_map).
    fequal. now ext [w' a].
  Qed.

  Context
    `{Monad T}
    `{Decorate W T}.

  (** Now we can assume that <<dec>> is a natural transformation,
      which is needed for the following. *)
  Context
    `{! Natural (@dec W F _)}.

  (** This lemmas is useful for proving the dec-extract law. *)
  Lemma dec_helper_2 {A}: forall (t: F A) (w: W),
      map F (extract (prod W) A) (dec F t) = t ->
      map F (extract (prod W) A) (shift F (w, dec F t)) = t.
  Proof.
    intros.
    compose near (w, dec F t).
    rewrite (shift_extract F). unfold compose; cbn.
    auto.
  Qed.

  (** This lemmas is useful for proving the double decoration law. *)
  Lemma dec_helper_3 {A}: forall (t: F A) (w: W),
      dec F (dec F t) = map F (cojoin (prod W)) (dec F t) ->
      shift F (w, dec F (shift F (w, dec F t))) =
        map F (cojoin (prod W)) (shift F (w, dec F t)).
  Proof.
    introv IH. unfold compose. rewrite 2(shift_spec F).
    compose near (dec F t).
    rewrite <- (natural (F := F) (G := F ○ prod W)).
    unfold compose. compose near (dec F (dec F t)).
    rewrite IH. unfold_ops @Map_compose.
    rewrite (fun_map_map).
    compose near (dec F t).
    rewrite (fun_map_map).
    rewrite (fun_map_map).
    unfold compose. fequal.
    now ext [w' a].
  Qed.

  (** This lemmas is useful for proving the decoration-join law. *)
  Lemma dec_helper_4 {A}: forall (t: T (T A)) (w: W),
      dec T (join T A t) =
        join T (W * A) (map T (shift T) (dec T (map T (dec T) t))) ->
      shift T (w, dec T (join T A t)) =
        join T (W * A)
          (map T (shift T) (shift T (w, dec T (map T (dec T) t)))).
  Proof.
    introv IH. rewrite !(shift_spec T) in *. rewrite IH.
    compose near (dec T (map T (dec T) t)) on right.
    rewrite (fun_map_map (F := T)). rewrite (shift_increment T).
    rewrite <- (fun_map_map (F := T)).
    change (map T (map T ?f)) with (map (T ∘ T) f).
    compose near (dec T (map T (dec T) t)).
    reassociate <-.
    #[local] Set Keyed Unification.
    now rewrite <- (natural (ϕ := @join T _)).
    #[local] Unset Keyed Unification.
  Qed.

End helper_lemmas.

#[local] Generalizable Variables ϕ A B.

(** * Pushing Decorations through a Monoid Homomorphism *)
(** If a functor is readable by a monoid, it is readable by any target
    of a homomorphism from that monoid too. *)
(**********************************************************************)
Section DecoratedFunctor_monoid_homomorphism.

  Import Product.Notations.

  Context
    (Wsrc Wtgt: Type)
    `{Monoid_Morphism Wsrc Wtgt ϕ}
    `{Decorate Wsrc F} `{Map F} `{Return F} `{Join F}
    `{! DecoratedMonad Wsrc F}.

  Instance Decorate_homomorphism:
    Decorate Wtgt F := fun A => map F (map_fst ϕ) ∘ dec F.

  Instance Natural_read_morphism:
    Natural (@dec Wtgt F Decorate_homomorphism).
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. unfold_ops @Decorate_homomorphism.
      unfold_ops @Map_compose.

      reassociate <- on left.
      rewrite (fun_map_map (F := F)).
      rewrite (product_map_commute).
      rewrite <- (fun_map_map (F := F)).
      reassociate -> on left.
      change (map F (map (prod Wsrc) f)) with
        (map (F ∘ prod Wsrc) f).
      reassociate ->.
      rewrite <- (natural (ϕ := @dec Wsrc F _ )).
      reflexivity.
  Qed.

  Lemma map_hom_cojoin: forall (A: Type),
      map_fst ϕ ∘ map (prod Wsrc) (map_fst ϕ) ∘
        cojoin (prod Wsrc) (A := A) =
        cojoin (prod Wtgt) ∘ map_fst ϕ.
  Proof.
    intros. now ext [w a].
  Qed.

  Instance DecoratedFunctor_morphism:
    Categorical.DecoratedFunctor.DecoratedFunctor Wtgt F.
  Proof.
    constructor; try typeclasses eauto.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate <-. reassociate -> near (map F (map_fst ϕ)).
      rewrite <- (natural (ϕ := @dec Wsrc F _) (map_fst ϕ)).
      reassociate <-.
      unfold_ops @Map_compose. rewrite (fun_map_map (F := F)).
      reassociate -> near (@dec Wsrc F _ A).
      rewrite (dfun_dec_dec (E := Wsrc) (F := F)).
      reassociate <-. rewrite (fun_map_map (F := F)).
      reassociate <-. rewrite (fun_map_map (F := F)).
      rewrite map_hom_cojoin.
      reflexivity.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate <-. rewrite (fun_map_map (F := F)).
      replace (extract (Wtgt ×) A ∘ map_fst ϕ)
        with (extract (Wsrc ×) A) by now ext [w a].
      rewrite (dfun_dec_extract (E := Wsrc) (F := F)).
      reflexivity.
  Qed.

  Instance DecoratedMonad_morphism:
    DecoratedMonad.DecoratedMonad Wtgt F.
  Proof.
    inversion H.
    constructor; try typeclasses eauto.
    - intros. unfold dec, Decorate_homomorphism.
      reassociate ->. rewrite (dmon_ret (W := Wsrc) (T := F)).
      reassociate <-. rewrite (natural (ϕ := @ret F _)).
      ext a. unfold compose; cbn.
      now rewrite (monmor_unit).
    - intros. unfold dec, Decorate_homomorphism.
      reassociate ->. rewrite (dmon_join (W := Wsrc) (T := F)).
      repeat reassociate <-.
      rewrite (natural (ϕ := @join F _)).
      reassociate -> near (map F (shift F)).
      unfold_ops @Map_compose.
      unfold_compose_in_compose.
      rewrite (fun_map_map (F := F) _ _ _
                 (shift F) (map F (map_fst ϕ))).
      reassociate -> near (map F (map_fst ϕ)).
      rewrite (fun_map_map (F := F)).
      rewrite <- (fun_map_map (F := F) _ _ _
                   (dec F) (map F (map_fst ϕ))).
      reassociate <-.
      reassociate -> near (map F (map F (map_fst ϕ))).
      rewrite <- (natural (ϕ := @dec Wsrc F _)).
      reassociate <-. unfold_ops @Map_compose.
      reassociate -> near (map F (map (prod Wsrc) (map F (map_fst ϕ)))).
      rewrite (fun_map_map (F := F)).
      repeat fequal. ext [w t].
      unfold compose; cbn.
      change (id ?f) with f. unfold shift.
      unfold compose; cbn.
      do 2 (compose near t;
            repeat rewrite (fun_map_map (F := F))).
      fequal. ext [w' a].
      unfold compose; cbn. rewrite monmor_op.
      reflexivity.
  Qed.

End DecoratedFunctor_monoid_homomorphism.
