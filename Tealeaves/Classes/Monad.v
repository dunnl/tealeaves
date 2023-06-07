From Tealeaves Require Export
  Classes.Functor
  Functors.Identity.

Import Functor.Notations.

#[local] Generalizable Variables A B C D.

(** * Kleisli presentation of monads *)
(******************************************************************************)

(** ** <<Bind>> operation *)
(******************************************************************************)
Section kleisli_operations.

  Context
    (F T : Type -> Type).

  Class Return := ret : (fun A => A) ⇒ T.

  Class Bind :=
    bind : forall (A B : Type), (A -> T B) -> F A -> F B.

End kleisli_operations.

Definition kcompose
  (T : Type -> Type) `{Bind T T}
  `(g : B -> T C) `(f : A -> T B) : (A -> T C) :=
  bind T T B C g ∘ f.

#[local] Notation "g ⋆ f" := (kcompose _ g f) (at level 60) : tealeaves_scope.

#[local] Arguments ret T%function_scope {Return} A%type_scope _.

(** ** Monads *)
(******************************************************************************)

Section monad_class.

  Context
    (T : Type -> Type)
    `{Return T} `{Bind T T}.

  Class Monad :=
    { (* left unit law of the monoid *)
      kmon_bind0 : forall `(f : A -> T B),
        bind T T A B f  ∘ ret T A = f;
      (* right unit law of the monoid *)
      kmon_bind1 : forall (A : Type),
        bind T T A A (ret T A) = @id (T A);
      (* associativity of the monoid *)
      kmon_bind2 : forall `(g : B -> T C) `(f : A -> T B),
        bind T T B C g ∘ bind T T A B f = bind T T A C (g ⋆ f);
    }.

End monad_class.

(** ** Monad Homomorphisms *)
(******************************************************************************)
Section monad_hom.

  Context
    (T U : Type -> Type)
    `{Return T} `{Bind T T}
    `{Return U} `{Bind U U}
    (ϕ : forall (A : Type), T A -> U A).

  Class Monad_Hom :=
    { kmon_hom_bind : forall (A B : Type) (f : A -> T B),
        ϕ B ∘ bind T T A B f = bind U U A B (ϕ B ∘ f) ∘ ϕ A;
      kmon_hom_ret : forall (A : Type),
        ϕ A ∘ ret T A = ret U A;
    }.

End monad_hom.

(** ** Right modules *)
(******************************************************************************)
Section module_class.

  Context
    (F : Type -> Type)
    (T : Type -> Type)
    `{Return T} `{Bind F T} `{Bind T T}.

  Class RightModule :=
    { kmod_monad :> Monad T;
      kmod_bind1 : forall (A : Type),
        bind F T A A (ret T A) = @id (F A);
      kmod_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind F T B C g ∘ bind F T A B f = bind F T A C (g ⋆ f);
    }.

End module_class.

Arguments bind (F)%function_scope {T}%function_scope
  {Bind} {A B}%type_scope _%function_scope _.

Arguments ret (T)%function_scope {Return} {A}%type_scope _.

(** * Kleisli category laws *)
(** An interesting note here is that the left unit law of the monad
corresponds to the right identity law of the Kleisli category and vice versa. *)
(******************************************************************************)
Section Monad_kleisli_category.

  Context
    (T : Type -> Type)
    `{Monad T}
    {A B C D : Type}.

  (** ** Left identity law *)
  Theorem kleisli_id_l : forall (f : A -> T B),
      (@ret T _ B) ⋆ f = f.
  Proof.
    intros. unfold kcompose. now rewrite (kmon_bind1 T).
  Qed.

  (** ** Right identity law *)
  Theorem kleisli_id_r : forall (g : B -> T C),
      g ⋆ (@ret T _ B) = g.
  Proof.
    intros. unfold kcompose. now rewrite (kmon_bind0 T).
  Qed.

  (** ** Associativity law *)
  Theorem kleisli_assoc : forall (h : C -> T D) (g : B -> T C) (f : A -> T B),
      h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f.
  Proof.
    intros. unfold kcompose at 3.
    now rewrite <- (kmon_bind2 T).
  Qed.

End Monad_kleisli_category.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "g ⋆ f" := (kcompose _ g f) (at level 60) : tealeaves_scope.

End Notations.

(** * Derived functor instance *)
(******************************************************************************)
Module ToFunctor.

  Section operation.

    Context
      (T : Type -> Type)
      `{Return T}
      `{Bind T T}.

    #[export] Instance Fmap_Bind : Fmap T :=
      fun `(f : A -> B) => bind T (ret T ∘ f).

  End operation.

  Section to_functor.

    Context
      (T : Type -> Type)
      `{Monad T}.

    #[export] Instance: Functor T.
    Proof.
      constructor.
      - intros. unfold transparent tcs.
        unfold compose. now rewrite (kmon_bind1 T).
      - intros. unfold transparent tcs.
        rewrite (kmon_bind2 T).
        unfold kcompose. reassociate <- near (bind T (ret T ∘ g)).
        now rewrite (kmon_bind0 T).
    Qed.

    (** *** Composition with [fmap] *)
    (******************************************************************************)
    Lemma bind_fmap : forall `(g : B -> T C) `(f : A -> B),
        bind T g ∘ fmap T f = bind T (g ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite (kmon_bind2 T).
      fequal. unfold kcompose.
      reassociate <-. rewrite (kmon_bind0 T).
      reflexivity.
    Qed.

    Corollary fmap_bind : forall `(g : B -> C) `(f : A -> T B),
        fmap T g ∘ bind T f = bind T (fmap T g ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite (kmon_bind2 T).
      reflexivity.
    Qed.

  (** *** Special cases for Kleisli composition *)
  (******************************************************************************)
  Lemma kcompose_ret : forall `(g : B -> C) `(f : A -> B),
      (ret T ∘ g) ⋆ (ret T ∘ f) = ret T ∘ (g ∘ f).
  Proof.
    intros. unfold kcompose.
    reassociate <-. now rewrite (kmon_bind0 T).
  Qed.

  Lemma kcompose10 : forall `(g : B -> T C) `(f : A -> B),
      g ⋆ (ret T ∘ f) = g ∘ f.
  Proof.
    intros. unfold kcompose.
    reassociate <-. now rewrite (kmon_bind0 T).
  Qed.

  Lemma kcompose01 : forall `(g : B -> C) `(f : A -> T B),
      (ret T ∘ g) ⋆ f = fmap T g ∘ f.
  Proof.
    intros. unfold kcompose.
    reflexivity.
  Qed.

  (** *** Other rules for Kleisli composition *)
  (******************************************************************************)
  Lemma kcompose_asc1 : forall `(g : B -> C) `(h : C -> T D) `(f : A -> T B),
      (h ∘ g) ⋆ f = h ⋆ (fmap T g ∘ f).
  Proof.
    intros. unfold kcompose.
    reassociate <-.
    rewrite (bind_fmap).
    reflexivity.
  Qed.

  Lemma kcompose_asc2 : forall `(f : A -> B) `(g : B -> T C) `(h : C -> T D),
      h ⋆ (g ∘ f) = (h ⋆ g) ∘ f.
  Proof.
    intros. unfold kcompose.
    reflexivity.
  Qed.

  (** *** Naturality of <<ret>> *)
  (******************************************************************************)
  #[export] Instance mon_ret_natural : Natural (@ret T _).
  Proof.
    constructor; try typeclasses eauto.
    intros. unfold_ops @Fmap_Bind.
    rewrite (kmon_bind0 T).
    reflexivity.
  Qed.

  End to_functor.

End ToFunctor.
