From Tealeaves Require Export
  Classes.Kleisli.Monad
  Classes.Kleisli.DT.Functor
  Classes.Kleisli.Decorated.Functor
  Classes.Kleisli.Traversable.Functor
  Classes.Kleisli.DT.Monad
  Classes.Kleisli.Decorated.Monad
  Classes.Kleisli.Traversable.Monad
  Theory.Kleisli.Decorated.Prepromote
  Theory.Kleisli.DT.Monad.Properties
  Theory.Kleisli.DT.Monad.ToFunctor.

Import Comonad.Notations.
Import Kleisli.Monad.Notations.
Import Product.Notations.
Import DT.Functor.Notations.
Import Decorated.Monad.Notations.
Import Traversable.Monad.Notations.
Import DT.Monad.Notations.

(** * Lesser Kleisli operations *)
(******************************************************************************)
Module Operations.
  Section with_monad.
    Context
      (W : Type)
      (T : Type -> Type)
      `{Return T}
      `{Binddt W T T}.

    #[export] Instance Fmapdt_Binddt: Fmapdt W T
      := fun G _ _ _ A B f => binddt T G (fmap G (ret T) ∘ f).
    #[export] Instance Bindd_Binddt: Bindd W T T
      := fun A B f => binddt T (fun A => A) f.
    #[export] Instance Bindt_Binddt: Bindt T T
      := fun G _ _ _ A B f => binddt T G (f ∘ extract (W ×)).
    #[export] Instance Bind_Binddt: Bind T T
      := fun A B f => binddt T (fun A => A) (f ∘ extract (W ×)).
    #[export] Instance Fmapd_Binddt: Fmapd W T
      := fun A B f => binddt T (fun A => A) (ret T ∘ f).
    #[export] Instance Traverse_Binddt: Traverse T
      := fun G _ _ _ A B f => binddt T G (fmap G (ret T) ∘ f ∘ extract (W ×)).
    (*
    #[export] Instance Fmap_Binddt: Fmap T
      := fun A B f => binddt T (fun A => A) (ret T ∘ f ∘ extract (W ×)).
     *)
  End with_monad.
End Operations.

(** ** Specifications for lesser Kleisli operations *)
(******************************************************************************)
Section special_cases.

  Import ToFunctor.Operation.
  Import DT.Monad.ToFunctor.Instance.

  Import Operations.
  #[local] Generalizable Variables A B F.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Return T}
    `{Binddt W T T}
    `{Applicative F}.

  (** *** Rewriting rules for special cases of <<binddt>> *)
  (******************************************************************************)
  Lemma bindt_to_binddt `(f : A -> F (T B)):
    bindt T F f = binddt T F (f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  Lemma bindd_to_binddt `(f : W * A -> T B):
    bindd T f = binddt T (fun A => A) f.
  Proof.
    reflexivity.
  Qed.

  Lemma fmapdt_to_binddt `(f : W * A -> F B):
    fmapdt T F f = binddt T F (fmap F (ret T) ∘ f).
  Proof.
    reflexivity.
  Qed.

  Lemma bind_to_binddt `(f : A -> T B):
    bind T f = binddt T (fun A => A) (f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  Lemma fmapd_to_binddt `(f : W * A -> B):
    fmapd T f = binddt T (fun A => A) (ret T ∘ f).
  Proof.
    reflexivity.
  Qed.

  Lemma fmapt_to_binddt `(f : A -> F B):
    traverse T F f = binddt T F (fmap F (ret T) ∘ f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_to_binddt `(f : A -> B):
    fmap T f = binddt T (fun A => A) (ret T ∘ f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  (** *** Rewriting rules for special cases of <<bindt>> *)
  (******************************************************************************)
  Lemma bind_to_bindt `(f : A -> T B):
    bind T f = bindt T (fun A => A) f.
  Proof.
    reflexivity.
  Qed.

  Lemma fmapt_to_bindt `(f : A -> F B):
    traverse T F f = bindt T F (fmap F (ret T) ∘ f).
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_to_bindt `(f : A -> B):
    fmap T f = bindt T (fun A => A) (ret T ∘ f).
  Proof.
    reflexivity.
  Qed.

  (** *** Rewriting rules for special cases of <<bindd>> *)
  (******************************************************************************)
  Lemma bind_to_bindd `(f : A -> T B):
    bind T f = bindd T (f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  Lemma fmapd_to_bindd `(f : W * A -> B):
    fmapd T f = bindd T (ret T ∘ f).
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_to_bindd `(f : A -> B):
    fmap T f = bindd T (ret T ∘ f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  (** *** Rewriting rules for special cases of <<fmapdt>> *)
  (******************************************************************************)
  Lemma fmapd_to_fmapdt `(f : W * A -> B):
    fmapd T f = fmapdt T (fun A => A) f.
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_to_fmapdt `(f : A -> B):
    fmap T f = fmapdt T (fun A => A) (f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  Lemma fmapt_to_fmapdt `(f : A -> F B):
    traverse T F f = fmapdt T F (f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  (** *** Rewriting rules for special cases of <<fmapt>> *)
  (******************************************************************************)
  Lemma fmap_to_fmapt `(f : A -> B):
    fmap T f = traverse T (fun A => A) f.
  Proof.
    reflexivity.
  Qed.

  (** *** Rewriting rules for special cases of <<fmapd>> *)
  (******************************************************************************)
  Lemma fmap_to_fmapd `(f : A -> B):
    fmap T f = fmapd T (f ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  (** *** Rewriting rules for special cases of <<bind>> *)
  (******************************************************************************)
  Lemma fmap_to_bind `(f : A -> B):
    fmap T f = bind T (ret T ∘ f).
  Proof.
    reflexivity.
  Qed.

End special_cases.

(** ** Special cases of Kleisli composition *)
(******************************************************************************)
Section kleisli_composition.

  Import Operations.
  #[local] Generalizable Variables A B C G.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  (*
    d/t/m:
    000 0 no d or t or m
    001 1 no context or effect
    010 2 no context or subst
    011 3 no context
    100 4 no effect or subst
    101 5 no effect
    110 6 no subst
    111 7 everything
   *)

  (** *** Composition when <<g>> is context-agnostic *)
  (******************************************************************************)

  (** Composition when <<g>> is context-agnostic reduces to Kleisli
  composition for traversable monads. *)
  Theorem dtm_kleisli_37 {A B C} : forall
      `{Applicative G1} `{Applicative G2}
        (g : B -> G2 (T C)) (f : W * A -> G1 (T B)),
      (g ∘ extract (W ×)) ⋆dtm f = g ⋆tm f.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. rewrite prepromote_extract.
    reflexivity.
  Qed.

  (** Composition when neither <<g>> or <<f>> is context-sensitive *)
  Lemma kcompose_dtm_33 :
    forall `{Applicative G1} `{Applicative G2}
      `(g : B -> G2 (T C)) `(f : A -> G1 (T B)),
      kcompose_dtm (G1 := G1) (G2 := G2) (g ∘ extract (W ×)) (f ∘ extract (W ×)) =
        (kcompose_tm (G1 := G1) (G2 := G2) g f) ∘ extract (W ×).
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. rewrite prepromote_extract.
    reflexivity.
  Qed.

  (** Composition when <<g>> has no applicative effect *)
  Theorem dtm_kleisli_57 {A B C} : forall
      `{Applicative G1}
      (g : W * B -> T C) (f : W * A -> G1 (T B)),
      kcompose_dtm (G2 := fun A => A) g f = g ⋆dtm f.
  Proof.
    reflexivity.
  Qed.

  (** *** Composition when <<g>> has no substitution *)
  (******************************************************************************)

  (** Composition when <<g>> has no substitution *)
  Theorem dtm_kleisli_67 {A B C} : forall
      `{Applicative G1} `{Applicative G2}
      (g : W * B -> G2 C) (f : W * A -> G1 (T B)),
      (fmap G2 (ret T) ∘ g) ⋆dtm f = (fmap G2 (ret T) ∘ g) ⋆dtm f.
  Proof.
    reflexivity.
  Qed.

  (** Composition when neither <<g>> or <<f>> perform a substitution *)
  Lemma kcompose_dtm_66 : forall
      `{Applicative G1} `{Applicative G2}
      `(g : W * B -> G2 C) `(f : W * A -> G1 B),
      (fmap G2 (ret T) ∘ g) ⋆dtm (fmap G1 (ret T) ∘ f) =
        fmap (G1 ∘ G2) (ret T) ∘ (kcompose_dt (G1 := G1) (G2 := G2) g f).
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. unfold compose at 2.
    compose near (f (w, a)).
    rewrite (fun_fmap_fmap G1).
    rewrite (kdtm_binddt0 W T); auto.
    rewrite prepromote_ret.
    unfold kcompose_dt. unfold_ops @Fmap_compose.
    do 2 reassociate <-.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G1).
    unfold strength.
    unfold compose; cbn.
    compose near (f (w, a)) on right.
    rewrite (fun_fmap_fmap G1).
    reflexivity.
  Qed.

  (** *** Composition when <<g>> has no applicative effect *)
  (******************************************************************************)

  (** Composition when neither <<g>> or <<f>> has an applicative effect *)
  Lemma kcompose_dtm_55 : forall
      `(g : W * B -> T C) `(f : W * A -> T B),
    kcompose_dtm (G1 := fun A => A) (G2 := fun A => A) g f =
      kcompose_dm g f.
  Proof.
    reflexivity.
  Qed.

  (** Composition when neither <<g>> or <<f>> has an applicative effect or substitution *)
  Lemma kcompose_dtm_44 : forall
      `(g : W * B -> C) `(f : W * A -> B),
      kcompose_dtm (G1 := fun A => A) (G2 := fun A => A)
        (ret T ∘ g) (ret T ∘ f) = ret T ∘ (g co⋆ f).
  Proof.
    intros. rewrite kcompose_dtm_55.
    unfold kcompose_dm.
    ext [w a].
    intros. unfold_ops @Bindd_Binddt.
    unfold compose. compose near (f (w, a)).
    rewrite (kdtm_binddt0 W T _ _ (G := fun A => A)).
    cbv. now simpl_monoid.
  Qed.


  (** *** Composition when <<f>> has no applicative effect *)
  (******************************************************************************)

  (** Composition when <<f>> has no applicative effect *)
  Theorem dtm_kleisli_75 {A B C} : forall
      `{Applicative G2}
        (g : W * B -> G2 (T C)) (f : W * A -> T B),
      kcompose_dtm (G1 := fun A => A) g f = fun '(w, a) => binddt T G2 (prepromote w g) (f (w, a)).
  Proof.
    reflexivity.
  Qed.

  (** Composition when <<f>> has no applicative effect, substitution, or context-sensitivity *)
  Lemma kcompose_dtm_70 : forall
      `{Applicative G}
      `(g : W * B -> G (T C)) `(f : A -> B),
      kcompose_dtm (G1 := fun A => A) (G2 := G)
        g (ret T ∘ f ∘ extract (W ×)) = g ∘ fmap (W ×) f.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. unfold compose.
    cbn. compose near (f a) on left.
    change (fmap (fun A => A) ?f) with f.
    rewrite (kdtm_binddt0 W T _ _ (G := G)).
    now rewrite prepromote_ret.
  Qed.

  (** Composition when <<f>> is just a map *)
  Theorem dtm_kleisli_70 {A B C} : forall
      `{Applicative G2}
      (g : W * B -> G2 (T C)) (f : A -> B),
      kcompose_dtm (G1 := fun A => A) (G2 := G2) g
      (ret T ∘ f ∘ extract (W ×)) = g ∘ fmap (W ×) f.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. unfold compose. cbn.
    compose near (f a) on left.
    change (fmap (fun A => A) ?f) with f.
    rewrite (kdtm_binddt0 W T); auto.
    now rewrite (prepromote_ret).
  Qed.

  (** Composition when <<f>> has no applicative effect or substitution *)
  Lemma kcompose_dtm_74 : forall
      `{Applicative G}
      `(g : W * B -> G (T C)) `(f : W * A -> B),
      kcompose_dtm (G1 := fun A => A) (G2 := G)
        g (ret T ∘ f) = g co⋆ f.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. unfold compose.
    compose near (f (w, a)).
    change (fmap (fun A => A) ?f) with f.
    rewrite (kdtm_binddt0 W T _ _ (G := G)).
    now rewrite prepromote_ret.
  Qed.

  (** *** Others *)
  (******************************************************************************)

  (** Composition when <<f>> is context-agnostic *)
  Theorem dtm_kleisli_73 {A B C} : forall
      `{Applicative G1} `{Applicative G2}
      (g : W * B -> G2 (T C)) (f : A -> G1 (T B)),
      g ⋆dtm (f ∘ extract (W ×)) =
        ((fun '(w, t) => fmap G1 (binddt T G2 (prepromote w g)) t) ∘ fmap (W ×) f).
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. unfold compose. cbn.
    reflexivity.
  Qed.
  (** Composition when <<f>> has no substitution *)
  Theorem dtm_kleisli_76 {A B C} : forall
      `{Applicative G1} `{Applicative G2}
      (g : W * B -> G2 (T C)) (f : W * A -> G1 B),
      g ⋆dtm (fmap G1 (ret T) ∘ f) = g ⋆dt f.
  Proof.
    intros. unfold kcompose_dtm.
    ext [w a]. unfold kcompose_dt.
    unfold compose. cbn.
    compose near (f (w, a)).
    rewrite (fun_fmap_fmap G1).
    rewrite (fun_fmap_fmap G1).
    fequal.
    rewrite (kdtm_binddt0 W T); auto.
    now rewrite (prepromote_ret).
  Qed.

End kleisli_composition.

(** * Lesser Kleisli typeclass instances *)
(******************************************************************************)
Module Instances.

  Import Operations.
  #[local] Generalizable Variables A B F.

  Section instances.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Kleisli.DT.Monad.Monad W T}.

    (** ** Monad *)
    (******************************************************************************)
    Lemma kmon_bind0_T : forall (A B : Type) (f : A -> T B),
        bind T f ∘ ret T = f.
    Proof.
      intros. unfold_ops @Bind_Binddt.
      rewrite (kdtm_binddt0 W T _ _ _ (G := fun A => A)).
      reflexivity.
    Qed.

    Lemma kmon_bind1_T : forall A : Type,
        bind T (ret T) = @id (T A).
    Proof.
      intros. unfold_ops @Bind_Binddt.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma kmon_bind2_T : forall (B C : Type) (g : B -> T C) (A : Type) (f : A -> T B),
        bind T g ∘ bind T f = bind T (g ⋆ f).
    Proof.
      intros. unfold_ops @Bind_Binddt.
      change (binddt T (fun A0 : Type => A0) (g ∘ extract (prod W)))
        with (fmap (fun A => A)
                (binddt T (fun A0 : Type => A0) (g ∘ extract (prod W)))).
      rewrite (kdtm_binddt2 W T _ _ _ (G1 := fun A => A) (G2 := fun A => A)).
      fequal.
      - now rewrite Mult_compose_identity1.
      - change_left ((g ∘ extract (prod W)) ⋆dm (f ∘ extract (W ×))).
        unfold kcompose_dm. ext [w a]. unfold compose at 2. cbn.
        rewrite prepromote_extract.
        reflexivity.
    Qed.

    #[export] Instance KM_KDTM : Kleisli.Monad.Monad T :=
      {| kmon_bind0 := kmon_bind0_T;
         kmon_bind1 := kmon_bind1_T;
         kmon_bind2 := kmon_bind2_T;
      |}.

    (** ** Decorated monad *)
    (******************************************************************************)
    Lemma kmond_bindd0_T : forall (A B : Type) (f : W * A -> T B),
        bindd T f ∘ ret T = f ∘ ret (prod W).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      now rewrite (kdtm_binddt0 W T _ _ _ (G := fun A => A)).
    Qed.

    Lemma kmond_bindd1_T : forall A : Type,
        bindd T (ret T ∘ extract (prod W)) = @id (T A).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma kmond_bindd2_T : forall (B C : Type) (g : W * B -> T C) (A : Type) (f : W * A -> T B),
        bindd T g ∘ bindd T f = bindd T (g ⋆dm f).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      change (binddt T ?I g) with (fmap (fun A => A) (binddt T I g)).
      rewrite (kdtm_binddt2 W T _ _ _ (G1 := fun A => A) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    #[export] Instance KDM_KDTM: Kleisli.Decorated.Monad.Monad T :=
      {| kmond_bindd0 := kmond_bindd0_T;
         kmond_bindd1 := kmond_bindd1_T;
         kmond_bindd2 := kmond_bindd2_T;
      |}.

    (** ** Traversable monad *)
    (******************************************************************************)
    Lemma ktm_bindt0_T : forall
        (A B : Type) (G : Type -> Type) (H1 : Fmap G)
        (H2 : Pure G) (H3 : Mult G),
        Applicative G ->
        forall f : A -> G (T B), bindt T G f ∘ ret T = f.
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (kdtm_binddt0 W T); auto.
    Qed.

    Lemma ktm_bindt1_T : forall A : Type,
        bindt T (fun A : Type => A) (ret T) = @id (T A).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma ktm_bindt2_T : forall
        (A B C : Type) (G1 : Type -> Type) (H1 : Fmap G1)
        (H2 : Pure G1) (H3 : Mult G1),
        Applicative G1 ->
        forall (G2 : Type -> Type) (H5 : Fmap G2) (H6 : Pure G2) (H7 : Mult G2),
          Applicative G2 ->
          forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
            fmap G1 (bindt T G2 g) ∘ bindt T G1 f = bindt T (G1 ∘ G2) (g ⋆tm f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (kdtm_binddt2 W T); auto.
      fequal. rewrite (kcompose_dtm_33 W T).
      reflexivity.
    Qed.

    Lemma ktm_morph_T : forall
        (G1 G2 : Type -> Type) (H1 : Fmap G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Fmap G2)
        (H5 : Pure G2) (H6 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : A -> G1 (T B)),
          ϕ (T B) ∘ bindt T G1 f = bindt T G2 (ϕ (T B) ∘ f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      now rewrite (kdtm_morph W T G1 G2).
    Qed.

    #[export] Instance KTM_KDTM: Traversable.Monad.Monad T :=
      {| ktm_bindt0 := ktm_bindt0_T;
         ktm_bindt1 := ktm_bindt1_T;
         ktm_bindt2 := ktm_bindt2_T;
         ktm_morph := ktm_morph_T;
      |}.

    (** ** Decorated-traversable functor *)
    (******************************************************************************)
    Lemma kdtfun_fmapdt1_T : forall A : Type,
        fmapdt T (fun A0 : Type => A0) (extract (W ×)) = @id (T A).
    Proof.
      intros. unfold_ops @Fmapdt_Binddt.
      change (fmap (fun A => A) ?f) with f.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma kdtfun_fmapdt2_T :
      forall (G1 : Type -> Type) (H0 : Fmap G1) (H1 : Pure G1) (H2 : Mult G1) (H3 : Applicative G1)
        (G2 : Type -> Type) (H4 : Fmap G2) (H5 : Pure G2) (H6 : Mult G2) (H7 : Applicative G2)
        (B C : Type) (g : W * B -> G2 C) (A : Type) (f : W * A -> G1 B),
        fmap G1 (fmapdt T G2 g) ∘ fmapdt T G1 f = fmapdt T (G1 ∘ G2) (g ⋆dt f).
    Proof.
      intros. unfold_ops @Fmapdt_Binddt.
      rewrite (kdtm_binddt2 W T); auto.
      fequal. now rewrite (kcompose_dtm_66 W T).
    Qed.

    Lemma kdtfun_morph_T :
      forall (G1 G2 : Type -> Type) (H0 : Fmap G1) (H1 : Pure G1) (H2 : Mult G1)
        (H3 : Fmap G2) (H4 : Pure G2) (H5 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : W * A -> G1 B), fmapdt T G2 (ϕ B ∘ f) = ϕ (T B) ∘ fmapdt T G1 f.
    Proof.
      intros. unfold_ops @Fmapdt_Binddt.
      rewrite (kdtm_morph W T _ _ (ϕ := ϕ)).
      fequal. reassociate <-.
      unfold compose. ext [w a]. now rewrite (appmor_natural G1 G2).
    Qed.

    #[export] Instance KDT_KDTM: DT.Functor.DecoratedTraversableFunctor W T :=
      {| kdtfun_fmapdt1 := kdtfun_fmapdt1_T;
         kdtfun_fmapdt2 := kdtfun_fmapdt2_T;
         kdtfun_morph := kdtfun_morph_T;
      |}.

    (** ** Decorated functor *)
    (******************************************************************************)
    Lemma dfun_fmapd1_T : forall A : Type,
        fmapd T (extract (W ×)) = @id (T A).
    Proof.
      intros. unfold_ops @Fmapd_Binddt.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma dfun_fmapd2_T : forall (A B C : Type) (g : W * B -> C) (f : W * A -> B),
        fmapd T g ∘ fmapd T f = fmapd T (g ∘ cobind (W ×) f).
    Proof.
      intros. unfold_ops @Fmapd_Binddt.
      change (binddt T (fun A0 : Type => A0) ?g) with
        (fmap (fun A => A) (binddt T (fun A0 : Type => A0) g)) at 1.
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      now rewrite (kcompose_dtm_44 W T).
    Qed.

    #[export] Instance KD_KDTM: Kleisli.Decorated.Functor.DecoratedFunctor W T :=
      {| dfun_fmapd1 := dfun_fmapd1_T;
         dfun_fmapd2 := dfun_fmapd2_T;
      |}.

    (** ** Traversable functor *)
    (******************************************************************************)
    #[export] Instance KT_KDTM: Traversable.Functor.TraversableFunctor T.
    Admitted.

    (** ** Functor *)
    (******************************************************************************)

  End instances.

End Instances.

(** * Composition of <<binddt>> with lesser operations *)
(******************************************************************************)
Section derived_operations_composition.

  Import ToFunctor.Operation.
  Import ToFunctor.Instance.
  Import Instances.
  Import Operations.
  #[local] Generalizable Variables A B W G.

  Section binddt.

    Context
      (T : Type -> Type)
      `{DT.Monad.Monad W T}
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** ** <<binddt>> on the right *)
    (******************************************************************************)
    Lemma bindd_binddt: forall
        (g : W * B -> T C)
        (f : W * A -> G1 (T B)),
        fmap G1 (bindd T g) ∘ binddt T G1 f =
          binddt T G1 (fun '(w, a) => fmap G1 (bindd T (prepromote w g)) (f (w, a))).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    Lemma fmapdt_binddt: forall
        (g : W * B -> G2 C)
        (f : W * A -> G1 (T B)),
        fmap G1 (fmapdt T G2 g) ∘ binddt T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => fmap G1 (fmapdt T G2 (prepromote w g)) (f (w, a))).
    Proof.
      intros. unfold_ops @Fmapdt_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := G2)).
      reflexivity.
    Qed.

    Lemma bindt_binddt: forall
        (g : B -> G2 (T C))
        (f : W * A -> G1 (T B)),
        fmap G1 (bindt T G2 g) ∘ binddt T G1 f =
          binddt T (G1 ∘ G2) (fmap G1 (bindt T G2 g) ∘ f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := G2)).
      fequal. unfold kcompose_dtm. ext [w a].
      now rewrite prepromote_extract.
    Qed.

    Lemma bind_binddt: forall
        (g : B -> T C)
        (f : W * A -> G1 (T B)),
        fmap G1 (bind T g) ∘ binddt T G1 f =
          binddt T G1 (fmap G1 (bind T g) ∘ f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      unfold_ops @Bind_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := fun A => A)).
      fequal.
      - now rewrite Mult_compose_identity1.
      - ext [w a]. cbn. now rewrite (prepromote_extract).
    Qed.

    Lemma fmapd_binddt: forall
        (g : W * B -> C)
        (f : W * A -> G1 (T B)),
        fmap G1 (fmapd T g) ∘ binddt T G1 f =
          binddt T G1 (fun '(w, a) => fmap G1 (fmapd T (prepromote w g)) (f (w, a))).
    Proof.
      intros. unfold_ops @Fmapd_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    Lemma fmapt_binddt: forall
        (g : B -> G2 C)
        (f : W * A -> G1 (T B)),
        fmap G1 (traverse T G2 g) ∘ binddt T G1 f =
          binddt T (G1 ∘ G2) (fmap G1 (traverse T G2 g) ∘ f).
    Proof.
      intros.
      intros. unfold_ops @Traverse_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := G2)).
      fequal. ext [w a]. cbn.
      now rewrite prepromote_extract.
    Qed.

    (** ** <<binddt>> on the left *)
    (******************************************************************************)
    Lemma binddt_bindd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> T B),
        binddt T G2 g ∘ bindd T f =
          binddt T G2 (fun '(w, a) => binddt T G2 (prepromote w g) (f (w, a))).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      change (binddt T G2 g) with (fmap (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
    Qed.

    Lemma binddt_fmapdt: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> G1 B),
        fmap G1 (binddt T G2 g) ∘ fmapdt T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => fmap G1 (fun b => g (w, b)) (f (w, a))).
    Proof.
      intros. unfold_ops @Fmapdt_Binddt.
      rewrite (kdtm_binddt2 W T A B C).
      fequal. ext [w a]. unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite (fun_fmap_fmap G1).
      fequal. ext b. unfold compose; cbn.
      compose near b on left.
      rewrite (kdtm_binddt0 W T); auto.
      now rewrite prepromote_ret.
    Qed.

    Lemma binddt_bindt: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 (T B)),
        fmap G1 (binddt T G2 g) ∘ bindt T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => fmap G1 (binddt T G2 (prepromote w g)) (f a)).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      now rewrite (kdtm_binddt2 W T).
    Qed.

    Lemma binddt_bind: forall
        (g : W * B -> G2 (T C))
        (f : A -> T B),
        binddt T G2 g ∘ bind T f =
          binddt T G2 (fun '(w, a) => binddt T G2 (prepromote w g) (f a)).
    Proof.
      intros. unfold_ops @Bind_Binddt.
      change (binddt T G2 g) with (fmap (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
    Qed.

    Lemma binddt_fmapd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> B),
        binddt T G2 g ∘ fmapd T f =
          binddt T G2 (fun '(w, a) => g (w, f (w, a))).
    Proof.
      intros. unfold_ops @Fmapd_Binddt.
      change (binddt T G2 g) with (fmap (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      rewrite dtm_kleisli_75; auto.
      ext [w a]. unfold compose.
      compose near (f (w, a)).
      rewrite (kdtm_binddt0 W T); auto.
      now rewrite prepromote_ret.
    Qed.

    Lemma binddt_fmapt: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 B),
        fmap G1 (binddt T G2 g) ∘ traverse T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => fmap G1 (fun b => g (w, b)) (f a)).
    Proof.
      intros. unfold_ops @Traverse_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1)).
      fequal. unfold kcompose_dtm.
      ext [w a]. unfold compose. cbn.
      compose near (f a) on left.
      rewrite (fun_fmap_fmap G1).
      rewrite (kdtm_binddt0 W T); auto.
      rewrite prepromote_ret.
      reflexivity.
    Qed.

    Lemma binddt_fmap: forall
        (g : W * B -> G2 (T C))
        (f : A -> B),
        binddt T G2 g ∘ fmap T f =
          binddt T G2 (g ∘ fmap (W ×) f).
    Proof.
      intros. unfold_ops @Fmap_Binddt.
      change (binddt T G2 g) with (fmap (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G2 := G2) (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      ext [w a]. unfold compose. cbn.
      compose near (f a) on left.
      change (fmap (fun A => A) ?f) with f.
      rewrite (kdtm_binddt0 W T); auto.
      rewrite prepromote_ret.
      reflexivity.
    Qed.

  End binddt.

  (** ** <<bindd>>, <<fmapdt>>, <<bindt>> *)
  (******************************************************************************)
  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}
    `{Applicative G1}
    `{Applicative G2}
    {A B C : Type}.

  (* <<bindd_bindd>> is already given. *)
  (* bindt_bindt already given *)
  (* fmapdt_fmapdt already given *)

  Lemma bindd_fmapdt: forall
      (g : W * B -> T C)
      (f : W * A -> G1 B),
      fmap G1 (bindd T g) ∘ fmapdt T G1 f =
      binddt T G1 (fun '(w, a) => fmap G1 (g ∘ pair w) (f (w, a))).
  Proof.
    intros. unfold_ops @Bindd_Binddt.
    rewrite (binddt_fmapdt T (G2 := fun A => A)).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma fmapdt_bindd: forall
      (g : W * B -> G2 C)
      (f : W * A -> T B),
      fmapdt T G2 g ∘ bindd T f =
      binddt T G2 (fun '(w, a) => fmapdt T G2 (prepromote w g) (f (w, a))).
  Proof.
    intros. unfold_ops @Bindd_Binddt.
    change (fmapdt T G2 g) with (fmap (fun A => A) (fmapdt T G2 g)).
    rewrite (fmapdt_binddt T (G1 := fun A => A)).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma bindt_bindd: forall
      (g : B -> G2 (T C))
      (f : W * A -> T B),
      bindt T G2 g ∘ bindd T f =
      binddt T G2 (bindt T G2 g ∘ f).
  Proof.
    intros. unfold_ops @Bindt_Binddt.
    rewrite (binddt_bindd T).
    fequal. ext [w a].
    now rewrite (prepromote_extract).
  Qed.

  Lemma bindd_bindt: forall
      (g : W * B -> T C)
      (f : A -> G1 (T B)),
      fmap G1 (bindd T g) ∘ bindt T G1 f =
        binddt T G1 (fun '(w, a) => fmap G1 (bindd T (prepromote w g)) (f a)).
  Proof.
    intros. unfold_ops @Bindt_Binddt.
    rewrite (bindd_binddt T (G1 := G1)).
    reflexivity.
  Qed.

  Lemma fmapdt_bindt: forall
      (g : W * B -> G2 C)
      (f : A -> G1 (T B)),
      fmap G1 (fmapdt T G2 g) ∘ bindt T G1 f =
        binddt T (G1 ∘ G2) (fun '(w, a) => fmap G1 (fmapdt T G2 (prepromote w g)) (f a)).
  Proof.
    intros. unfold_ops @Bindt_Binddt.
    rewrite (fmapdt_binddt T).
    reflexivity.
  Qed.

  Lemma bindt_fmapdt: forall
      (g : B -> G2 (T C))
      (f : W * A -> G1 B),
      fmap G1 (bindt T G2 g) ∘ fmapdt T G1 f =
        binddt T (G1 ∘ G2) (fmap G1 g ∘ f).
  Proof.
    intros. unfold_ops @Bindt_Binddt.
    rewrite (binddt_fmapdt T).
    fequal. now ext [w a].
  Qed.

  (** ** <<bindd>> on the right *)
  (******************************************************************************)
  Lemma bind_bindd: forall
      (g : B -> T C)
      (f : W * A -> T B),
      bind T g ∘ bindd T f =
      bindd T (bind T g ∘ f).
  Proof.
    intros. rewrite (bind_to_bindd W T).
    rewrite (kmond_bindd2 T).
    fequal. unfold kcompose_dm.
    ext [w a]. now rewrite (prepromote_extract).
  Qed.

  Lemma fmapd_bindd: forall
      (g : W * B -> C)
      (f : W * A -> T B),
      fmapd T g ∘ bindd T f =
      bindd T (fun '(w, a) => fmapd T (prepromote w g) (f (w, a))).
  Proof.
    intros. rewrite (fmapd_to_bindd W T).
    rewrite (kmond_bindd2 T).
    reflexivity.
  Qed.

  (* traverse_bindd *)
  (* fmap_bindd *)

  (** ** <<bindd>> on the left *)
  (******************************************************************************)
  Lemma bindd_bind: forall
      (g : W * B -> T C)
      (f : A -> T B),
      bindd T g ∘ bind T f =
      bindd T (fun '(w, a) => bindd T (prepromote w g) (f a)).
  Proof.
    intros. rewrite (bind_to_bindd W T).
    rewrite (kmond_bindd2 T).
    reflexivity.
  Qed.

  Lemma bindd_fmapd: forall
      (g : W * B -> T C)
      (f : W * A -> B),
      bindd T g ∘ fmapd T f =
      bindd T (g co⋆ f).
  Proof.
    intros. rewrite (fmapd_to_bindd W T).
    rewrite (kmond_bindd2 T).
    fequal. ext [w a]. unfold kcompose_dm, compose.
    compose near (f (w, a)).
    rewrite (kmond_bindd0 T).
    now rewrite prepromote_ret.
  Qed.

  (* bindd_traverse *)
  (* bindd_fmap *)

  (** ** <<fmapdt>> on the right *)
  (******************************************************************************)
  (* bind_fmapdt *)
  (* fmapd_fmapdt *)
  (* traverse_fmapdt *)

  (* fmap_fmapdt *)

  (** ** <<fmapdt>> on the left *)
  (******************************************************************************)
  (* fmapdt_bind *)
  (* fmapdt_fmapd *)
  (* fmapdt_traverse *)

  (* fmapdt_fmap *)

  (** ** <<traverse>> on the right *)
  (******************************************************************************)
  (* bind_traverse *)
  (* fmapd_traverse *)
  (* traverse_traverse *)

  (* fmap_traverse *)

  (** ** <<traverse>> on the left *)
  (******************************************************************************)
  (* traverse_bind *)
  (* traverse_fmapd *)
  (* traverse_traverse *)

  (* traverse_fmap *)

  (** ** <<fmapd>> on the right *)
  (******************************************************************************)
  (* bind_fmapd *)
  (* fmapd_fmapd *)
  (* traverse_fmapd *)

  (* fmap_fmapd *)

  (** ** <<fmapd>> on the left *)
  (******************************************************************************)
  (* fmapd_bind *)
  (* fmapd_fmapd *)
  (* fmapd_traverse *)

  (* fmapd_fmap *)

End derived_operations_composition.

(*
(** * Expressing lesser operations with <<runSchedule>> *)
(******************************************************************************)
Section derived_operations_composition.

  Import ToFunctor.Operation.
  Import ToFunctor.Instance.
  Import Operations.
  #[local] Generalizable Variables A B W G.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}
    `{Applicative G1}
    `{Applicative G2}
    {A B C : Type}.

  Corollary bindd_to_runSchedule :
    forall (A B : Type) (t : T A)
      (f : W * A -> T B),
      bindd T f t = runSchedule T (fun A => A) f (iterate T B t).
  Proof.
    intros. rewrite bindd_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary bindt_to_runSchedule :
    forall `{Applicative G} (A B : Type) (t : T A)
      (f : A -> G (T B)),
      bindt T G f t = runSchedule T G (f ∘ extract (W ×)) (iterate T B t).
  Proof.
    intros. rewrite bindt_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary fmapdt_to_runSchedule  :
    forall `{Applicative G} (A B : Type) (t : T A)
      `(f : W * A -> G B),
      fmapdt T G f t = runSchedule T G (fmap G (ret T) ∘ f) (iterate T B t).
  Proof.
    intros. rewrite fmapdt_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary bind_to_runSchedule :
    forall (A B : Type) (t : T A)
      (f : A -> T B),
      bind T f t = runSchedule T (fun A => A) (f ∘ extract (W ×)) (iterate T B t).
  Proof.
    intros. rewrite bind_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary fmapd_to_runBatch `(f : W * A -> B) (t : T A) :
    fmapd T f t = runSchedule T (fun A => A) (ret T ∘ f) (iterate T B t).
  Proof.
    rewrite fmapd_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary fmapt_to_runBatch `{Applicative G} `(f : A -> G B) (t : T A) :
    traverse T G f t = runSchedule T G (fmap G (ret T) ∘ f ∘ extract (W ×)) (iterate T B t).
  Proof.
    rewrite fmapt_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary fmap_to_runBatch `(f : A -> B) (t : T A) :
    fmap T f t = runSchedule T (fun A => A) (ret T ∘ f ∘ extract (W ×)) (iterate T B t).
  Proof.
    rewrite fmap_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

End derived_operations_composition.
*)
