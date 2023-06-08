From Tealeaves Require Export
  Classes.Functor
  Functors.Identity.

Import Functor.Notations.

#[local] Generalizable Variables A B C D.

(** * Kleisli presentation of monads *)
(******************************************************************************)

(** ** <<Bind>> operation *)
(******************************************************************************)
Class Return (T : Type -> Type) :=
  ret : (fun A => A) ⇒ T.

Class Bind (T U : Type -> Type) :=
  bind : forall (A B : Type), (A -> T B) -> U A -> U B.

#[local] Arguments ret T%function_scope {Return} A%type_scope _.
#[local] Arguments bind (T U)%function_scope {Bind} (A B C)%type_scope.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc1 (T : Type -> Type) `{Bind T T} {A B C : Type}
  (g : B -> T C) (f : A -> T B) : (A -> T C) :=
  bind T T B C g ∘ f.

#[local] Notation "g ⋆ f" := (kc1 _ g f) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class Monad (T : Type -> Type) `{Return T} `{Bind T T} :=
  { (* left unit law of the monoid *)
    kmon_bind0 : forall `(f : A -> T B),
      bind T T A B f ∘ ret T A = f;
    (* right unit law of the monoid *)
    kmon_bind1 : forall (A : Type),
      bind T T A A (ret T A) = @id (T A);
    (* associativity of the monoid *)
    kmon_bind2 : forall `(g : B -> T C) `(f : A -> T B),
      bind T T B C g ∘ bind T T A B f = bind T T A C (g ⋆ f);
  }.

(** ** Monad Homomorphisms *)
(******************************************************************************)
Class Monad_Hom
  (T U : Type -> Type)
  `{Return T} `{Bind T T}
  `{Return U} `{Bind U U}
  (ϕ : forall (A : Type), T A -> U A) :=
  { kmon_hom_bind : forall (A B : Type) (f : A -> T B),
      ϕ B ∘ bind T T A B f = bind U U A B (ϕ B ∘ f) ∘ ϕ A;
    kmon_hom_ret : forall (A : Type),
      ϕ A ∘ ret T A = ret U A;
  }.

(** ** Right modules *)
(******************************************************************************)
Class RightModule
  (T : Type -> Type)
  (U : Type -> Type)
  `{Return T} `{Bind T T} `{Bind T U} :=
  { kmod_monad :> Monad T;
    kmod_bind1 : forall (A : Type),
      bind T U A A (ret T A) = @id (U A);
    kmod_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
      bind T U B C g ∘ bind T U A B f = bind T U A C (g ⋆ f);
  }.

Arguments ret T%function_scope {Return} {A}%type_scope.
Arguments bind (T U)%function_scope {Bind} {A B}%type_scope.

(** ** Kleisli category laws *)
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
    intros. unfold kc1. now rewrite kmon_bind1.
  Qed.

  (** ** Right identity law *)
  Theorem kleisli_id_r : forall (g : B -> T C),
      g ⋆ (@ret T _ B) = g.
  Proof.
    intros. unfold kc1. now rewrite kmon_bind0.
  Qed.

  (** ** Associativity law *)
  Theorem kleisli_assoc : forall (h : C -> T D) (g : B -> T C) (f : A -> T B),
      h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f.
  Proof.
    intros. unfold kc1 at 3.
    now rewrite <- kmon_bind2.
  Qed.

End Monad_kleisli_category.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Notation "g ⋆ f" := (kc1 _ g f) (at level 60) : tealeaves_scope.

End Notations.

(** * Derived functor instance *)
(******************************************************************************)
Module DerivedInstances.

  #[export] Instance Fmap_Bind
    (T : Type -> Type)
    `{Return T}
    `{Bind T T} : Fmap T :=
  fun A B (f : A -> B) => bind T T (ret T ∘ f).

  Section with_monad.

    Context
      (T : Type -> Type)
        `{Monad T}.

    #[export] Instance: Functor T.
    Proof.
      constructor.
      - intros. unfold transparent tcs.
        unfold compose. now rewrite kmon_bind1.
      - intros. unfold transparent tcs.
        rewrite kmon_bind2.
        unfold kc1. reassociate <- near (bind T T (ret T ∘ g)).
        now rewrite kmon_bind0.
    Qed.

    (** *** Composition with [fmap] *)
    (******************************************************************************)
    Lemma bind_fmap : forall `(g : B -> T C) `(f : A -> B),
        bind T T g ∘ fmap T f = bind T T (g ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite kmon_bind2.
      fequal. unfold kc1.
      reassociate <-. now rewrite kmon_bind0.
    Qed.

    Corollary fmap_bind : forall `(g : B -> C) `(f : A -> T B),
        fmap T g ∘ bind T T f = bind T T (fmap T g ∘ f).
    Proof.
      intros. unfold transparent tcs.
      now rewrite kmon_bind2.
    Qed.

    (** *** Special cases for Kleisli composition *)
    (******************************************************************************)
    Lemma kc1_00 : forall `(g : B -> C) `(f : A -> B),
        (ret T ∘ g) ⋆ (ret T ∘ f) = ret T ∘ (g ∘ f).
    Proof.
      intros. unfold kc1.
      reassociate <-. now rewrite kmon_bind0.
    Qed.

    Lemma kc1_10 : forall `(g : B -> T C) `(f : A -> B),
        g ⋆ (ret T ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc1.
      reassociate <-. now rewrite kmon_bind0.
    Qed.

    Lemma kc1_01 : forall `(g : B -> C) `(f : A -> T B),
        (ret T ∘ g) ⋆ f = fmap T g ∘ f.
    Proof.
      intros. unfold kc1.
      reflexivity.
    Qed.

    (** *** Other rules for Kleisli composition *)
    (******************************************************************************)
    Lemma kc1_asc1 : forall `(g : B -> C) `(h : C -> T D) `(f : A -> T B),
        (h ∘ g) ⋆ f = h ⋆ (fmap T g ∘ f).
    Proof.
      intros. unfold kc1.
      reassociate <-.
      rewrite (bind_fmap).
      reflexivity.
    Qed.

    Lemma kc1_asc2 : forall `(f : A -> B) `(g : B -> T C) `(h : C -> T D),
        h ⋆ (g ∘ f) = (h ⋆ g) ∘ f.
    Proof.
      intros. unfold kc1.
      reflexivity.
    Qed.

    (** *** Naturality of <<ret>> *)
    (******************************************************************************)
    #[export] Instance mon_ret_natural : Natural (@ret T _).
    Proof.
      constructor; try typeclasses eauto.
      intros. unfold_ops @Fmap_Bind.
      rewrite kmon_bind0.
      reflexivity.
    Qed.

  End with_monad.

End DerivedInstances.
