From Tealeaves Require Export
     Singlesorted.Classes.Functor
     Singlesorted.Classes.Applicative.

Import Product.Notations.
Import Functor.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

(** * Monads *)
(******************************************************************************)
Section monad_operations.

  Context
    (T : Type -> Type).

  Class Join := join : T ∘ T ⇒ T.

  Class Return := ret : (fun A => A) ⇒ T.

End monad_operations.

Section monad_class.

  Context
    (T : Type -> Type)
    `{Fmap T} `{Return T} `{Join T}.

  Class Monad :=
    { mon_functor :> Functor T;
      mon_ret_natural :> Natural (ret T);
      mon_join_natural :> Natural (join T);
      mon_join_fmap_ret :
        `(join T A ∘ fmap T (ret T A) = @id (T A));
      mon_join_ret :
        `(join T A ∘ ret T (T A) = @id (T A));
      mon_join_join :
        `(join T A ∘ join T (T A) = join T A ∘ fmap T (join T A));
    }.

End monad_class.

Arguments join _%function_scope {Join} {A}%type_scope.
Arguments ret _%function_scope {Return} {A}%type_scope.

(** ** Monad homomorphisms *)
(******************************************************************************)
Section monad_homomorphism.

  Context
    (T : Type -> Type)
    (U : Type -> Type)
    `{Monad T}
    `{Monad U}.

  Class Monad_Hom (ϕ : T ⇒ U) :=
    { mhom_domain : Monad T;
      mhom_codomain : Monad U;
      mhom_natural : Natural ϕ;
      mhom_ret :
        `(ϕ A ∘ ret T = ret U);
      mhom_join :
        `(ϕ A ∘ join T = join U ∘ ϕ (U A) ∘ fmap T (ϕ A));
    }.

End monad_homomorphism.

(** * The identity functor is a monad *)
(******************************************************************************)
Instance Return_I : Return (fun A => A) := (fun A (a : A) => a).

Instance Join_I : Join (fun A => A) := (fun A (a : A) => a).

#[program] Instance Monad_I : Monad (fun A => A).

Solve All Obligations with
    (constructor; try typeclasses eauto; intros; now ext t).

(** * Kleisli presentation of monads *)
(******************************************************************************)

(** ** Kleisli operations *)
(******************************************************************************)
Class Bind (T : Type -> Type) :=
  bind : forall {A B}, (A -> T B) -> T A -> T B.

Arguments bind T%function_scope {Bind} {A B}%type_scope _%function_scope.

Instance Bind_Join `{Fmap T} `{Join T} : Bind T :=
  fun `(f : A -> T B) => join T ∘ fmap T f.

Definition kcompose T `{Bind T} `(g : B -> T C) `(f : A -> T B) : (A -> T C) :=
  bind T g ∘ f.

#[local] Notation "g ⋆ f" := (kcompose _ g f) (at level 60) : tealeaves_scope.

(** ** Specifications for sub-operations  *)
(******************************************************************************)
Section monad_suboperations.

  Context
    (T : Type -> Type)
    `{Monad T}.

  (** *** [fmap] as a special case of [bind]. *)
  Corollary fmap_to_bind : forall `(f : A -> B),
      fmap T f = bind T (ret T ∘ f).
  Proof.
    intros. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap T).
    reassociate <- on right.
    now rewrite (mon_join_fmap_ret T).
  Qed.

End monad_suboperations.

(** ** Kleisli laws for [bind] *)
(******************************************************************************)
Section monad_kleisli_laws.

  Context
    (T : Type -> Type)
    `{Monad T}.

  (** *** Identity law *)
  Lemma bind_id :
    `(bind T (ret T) = @id (T A)).
  Proof.
    intros. unfold transparent tcs.
    now rewrite (mon_join_fmap_ret T).
  Qed.

  (** *** Composition law *)
  Lemma bind_bind : forall `(g : B -> T C) `(f : A -> T B),
      bind T g ∘ bind T f = bind T (g ⋆ f).
  Proof.
    introv. unfold transparent tcs. unfold kcompose.
    unfold_ops @Bind_Join.
    rewrite <- 2(fun_fmap_fmap T).
    reassociate <- on right.
    change (fmap ?T (fmap ?T g)) with (fmap (T ∘ T) g).
    reassociate <- on right.
    rewrite <- (mon_join_join T).
    reassociate -> near (fmap (T ∘ T) g).
    now rewrite <- (natural (ϕ := @join T _)).
  Qed.

  (** *** Unit law *)
  Lemma bind_comp_ret `(f : A -> T B) :
    bind T f ∘ ret T = f.
  Proof.
    intros. unfold transparent tcs.
    reassociate -> on left.
    unfold_compose_in_compose; (* these rewrites are not visible *)
      change (@compose A) with (@compose ((fun A => A) A)).
    rewrite natural.
    unfold transparent tcs. reassociate <- on left.
    now rewrite (mon_join_ret T).
  Qed.

End monad_kleisli_laws.

(** ** Kleisli category laws *)
(******************************************************************************)
Section monad_kleisli_category.

  Context
    `{Monad T}
    {A B C D : Type}.

  Theorem kleisli_id_r : forall (g : B -> T C),
      g ⋆ (@ret T _ B) = g.
  Proof.
    intros. unfold kcompose. now rewrite (bind_comp_ret T).
  Qed.

  Theorem kleisli_id_l : forall (f : A -> T B),
      (@ret T _ B) ⋆ f = f.
  Proof.
    intros. unfold kcompose. now rewrite (bind_id T).
  Qed.

  Theorem kleisli_comp : forall (h : C -> T D) (g : B -> T C) (f : A -> T B),
      h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f.
  Proof.
    intros. unfold kcompose at 3.
    now rewrite <- (bind_bind T).
  Qed.

End monad_kleisli_category.

(** ** Composition laws for suboperations *)
(******************************************************************************)
Section monad_suboperation_composition.

  Context
    (T : Type -> Type)
    `{Monad T}.

  Corollary bind_fmap : forall `(g : B -> T C) `(f : A -> B),
      bind T g ∘ fmap T f = bind T (g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

  Corollary fmap_bind : forall `(g : B -> C) `(f : A -> T B),
      fmap T g ∘ bind T f = bind T (fmap T g ∘ f).
  Proof.
    intros. unfold transparent tcs.
    reassociate <- on left.
    rewrite (natural). unfold_ops @Fmap_compose.
    now rewrite <- (fun_fmap_fmap T).
  Qed.

End monad_suboperation_composition.

(** ** Miscellaneous properties *)
(******************************************************************************)
Section tensor_laws.

  Context
    `{Monad T}
    {W : Type}.

  Theorem strength_return  {A B} (a : A) (b : B) :
    strength T (b, ret T a) = ret T (b, a).
  Proof.
    unfold strength. compose near a on left.
    change (@compose ?B) with (@compose ((fun A => A) B)).
    now rewrite natural.
  Qed.

End tensor_laws.

(** ** Equivalence between monads and Kleisli triples *)
(******************************************************************************)
Class KleisliMonad T `{Return T} `{Bind T} :=
  { kmon_bind_ret_r : forall `(f : A -> T B),
      bind T f ∘ ret T = f;
    kmon_bind_ret_l :
      `(bind T (ret T) = @id (T A));
    kmon_bind_bind : forall `(g : B -> T C) `(f : A -> T B),
        bind T g ∘ bind T f = bind T (bind T g ∘ f);
  }.

Section KleisliMonad_of_Monad.

  Context
    `{Monad T}.

  Instance KleisliMonad_Monad : KleisliMonad T :=
    {| kmon_bind_ret_l := mon_join_fmap_ret T;
       kmon_bind_ret_r := fun A B => bind_comp_ret T;
       kmon_bind_bind := fun B C => bind_bind T ;
    |}.

End KleisliMonad_of_Monad.

Section Monad_of_KleisliMonad.

  Context
    `{KleisliMonad T}.

  Instance Fmap_Kleisli : Fmap T :=
    fun A B (f : A -> B) => bind T (ret T ∘ f).

  Lemma fmap_id_Kleisli : forall A, fmap T (@id A) = @id (T A).
  Proof.
    intros. unfold_ops @Fmap_Kleisli.
    apply kmon_bind_ret_l.
  Qed.

  Lemma fmap_fmap_Kleisli : forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap T g ∘ fmap T f = fmap T (g ∘ f).
  Proof.
    intros. unfold_ops @Fmap_Kleisli.
    rewrite kmon_bind_bind. reassociate <- on left.
    now rewrite kmon_bind_ret_r.
  Qed.

  Instance Functor_Kleisli : Functor T :=
    {| Functor.fun_fmap_id := fmap_id_Kleisli;
       Functor.fun_fmap_fmap := fmap_fmap_Kleisli;
    |}.

  Instance Join_Kleisli : Join T := fun A => bind T (@id (T A)).

  Lemma join_ret_Kleisli : forall (A : Type), join T ∘ ret T = @id (T A).
  Proof.
    intros. unfold_ops @Join_Kleisli.
    unfold_compose_in_compose.
    now rewrite kmon_bind_ret_r.
  Qed.

  Lemma join_fmap_ret_Kleisli : forall (A : Type), join T ∘ fmap T (ret T) = @id (T A).
  Proof.
    intros. unfold_ops @Join_Kleisli @Fmap_Kleisli.
    unfold_compose_in_compose.
    rewrite kmon_bind_bind.
    rewrite <- kmon_bind_ret_l.
    reassociate <- on left.
    now do 2 rewrite kmon_bind_ret_r.
  Qed.

  Lemma join_fmap_join_Kleisli : forall (A : Type),
      join T ∘ join T = join T ∘ fmap T (join T) (A:=(T (T A))).
  Proof.
    intros. unfold_ops @Join_Kleisli @Fmap_Kleisli.
    unfold_compose_in_compose.
    do 2 rewrite kmon_bind_bind.
    reassociate <- on right.
    now rewrite kmon_bind_ret_r.
  Qed.

  Lemma Natural_Ret_Kleisli : Natural (fun A => ret T).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold_ops @Fmap_Kleisli.
    now rewrite kmon_bind_ret_r.
  Qed.

  Lemma Natural_Join_Kleisli : Natural (fun A => join (A:=A) T).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold_ops @Join_Kleisli @Fmap_compose @Fmap_Kleisli.
    unfold_compose_in_compose.
    unfold fmap. repeat rewrite kmon_bind_bind.
    reassociate <-. change (?f ∘ id) with f.
    now rewrite kmon_bind_ret_r.
  Qed.

  Instance Monad_Kleisli : Monad T :=
    {| mon_join_ret := join_ret_Kleisli;
       mon_join_fmap_ret := join_fmap_ret_Kleisli;
       mon_join_join := join_fmap_join_Kleisli;
       mon_ret_natural := Natural_Ret_Kleisli;
       mon_join_natural := Natural_Join_Kleisli;
    |}.

End Monad_of_KleisliMonad.

(** * Monadic applicative functors *)
(******************************************************************************)
Section Applicative_Monad.

  Context
    `{Monad T}.

  Existing Instance Bind_Join.

  #[global] Instance Pure_Monad : Pure T := @ret T _.

  #[global] Instance Mult_Monad : Mult T :=
    fun A B (p : T A * T B) =>
      match p with (ta, tb) =>
                   bind T (fun a => strength T (a, tb)) ta
      end.

  Theorem app_pure_natural_Monad : forall (A B : Type) (f : A -> B) (x : A),
      fmap T f (pure T x) = pure T (f x).
  Proof.
    intros. unfold_ops @Pure_Monad.
    compose near x. now rewrite (natural (ϕ := @ret T _)).
  Qed.

  Theorem app_mult_natural_Monad : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : T A) (y : T B),
      fmap T f x ⊗ fmap T g y = fmap T (map_tensor f g) (x ⊗ y).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x. rewrite (bind_fmap T), (fmap_bind T).
    fequal. ext c; unfold compose; cbn. compose near y.
    now rewrite 2(fun_fmap_fmap T).
  Qed.

  Theorem app_assoc_Monad : forall (A B C : Type) (x : T A) (y : T B) (z : T C),
      fmap T α ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. unfold_ops @Mult_Monad.
    compose near x on left. rewrite (bind_bind T).
    compose near x on left. rewrite (fmap_bind T).
    fequal. ext a; unfold compose; cbn.
    compose near y on right. rewrite (fmap_bind T).
    unfold compose; cbn. compose near z on right.
    unfold kcompose. unfold compose; cbn.
    compose near y on left.
    rewrite (bind_fmap T). compose near y on left.
    rewrite (fmap_bind T). fequal. ext b. unfold compose; cbn.
    compose near z. now do 2 (rewrite (fun_fmap_fmap T)).
  Qed.

  Theorem app_unital_l_Monad : forall (A : Type) (x : T A),
      fmap T left_unitor (pure T tt ⊗ x) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near tt. rewrite (bind_comp_ret T).
    unfold strength. compose near x.
    rewrite (fun_fmap_fmap T). change (left_unitor ∘ pair tt) with (@id A).
    now rewrite (fun_fmap_id T).
  Qed.

  Theorem app_unital_r_Monad : forall (A : Type) (x : T A),
      fmap T right_unitor (x ⊗ pure T tt) = x.
  Proof.
    intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near x. rewrite (fmap_bind T).
    replace (fmap T right_unitor ∘ (fun a : A => strength T (a, ret T tt)))
      with (ret T (A := A)).
    now rewrite (bind_id T).
    ext a; unfold compose; cbn. compose near (ret T tt).
    rewrite (fun_fmap_fmap T). compose near tt.
    rewrite (natural (ϕ := @ret T _ )). now unfold compose; cbn.
  Qed.

  Theorem app_mult_pure_Monad : forall (A B : Type) (a : A) (b : B),
      pure T a ⊗ pure T b = pure T (a, b).
  Proof.
    intros. intros. unfold_ops @Mult_Monad @Pure_Monad.
    compose near a. rewrite (bind_comp_ret T).
    now rewrite (strength_return).
  Qed.

  #[global] Instance Applicative_Monad : Applicative T :=
  { app_mult_pure := app_mult_pure_Monad;
    app_pure_natural := app_pure_natural_Monad;
    app_mult_natural := app_mult_natural_Monad;
    app_assoc := app_assoc_Monad;
    app_unital_l := app_unital_l_Monad;
    app_unital_r := app_unital_r_Monad;
  }.

End Applicative_Monad.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "g ⋆ f" := (kcompose _ g f) (at level 60) : tealeaves_scope.
  Notation "'μ'" := (join) : tealeaves_scope.
  Notation "'η'" := (ret) : tealeaves_scope.
End Notations.
