(** This file defines typeclasses *)
From Tealeaves Require Export
  Prelude
  Classes.Functor
  Functors.Identity.

#[local] Generalizable Variables F G A B C D W T U ϕ.
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

Import Functor.Notations.

(** * Operational typeclasses for DTM hierarchy *)
(******************************************************************************)
Section operations.

  Context
    (T : Type -> Type)
    (U : Type -> Type).

    Class Return :=
      ret : (fun A => A) ⇒ T.

    Class Bind :=
      bind : forall (A B : Type), (A -> T B) -> U A -> U B.

End operations.

(** ** Monad *)
(******************************************************************************)

Section kc.

  Context
    (T : Type -> Type)
    `{Return T}
    `{Bind T T}.

  Definition kc1
    {A B C : Type}
    (g : B -> T C)
    (f : A -> T B) :
    (A -> T C) :=
    bind T T B C g ∘ f.

End kc.

#[local] Infix "⋆1" := (kc1 _) (at level 60) : tealeaves_scope.

Section class.

  Context
    (T : Type -> Type)
    `{Return T}
    `{Bind T T}.

  Class Monad :=
    { (* left unit law of the monoid *)
      kmon_bind0 : forall (A B : Type) (f : A -> T B),
        bind T T A B f ∘ ret T A = f;
      (* right unit law of the monoid *)
      kmon_bind1 : forall (A : Type),
        bind T T A A (ret T A) = @id (T A);
      (* associativity of the monoid *)
      kmon_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind T T B C g ∘ bind T T A B f = bind T T A C (g ⋆1 f);
    }.

End class.

(** *** Monad Homomorphisms *)
(******************************************************************************)
Section class.

  Context
    (T U : Type -> Type)
      `{Return T} `{Bind T T}
      `{Return U} `{Bind U U}.

  Class MonadHom (ϕ : forall (A : Type), T A -> U A) :=
    { kmon_hom_bind : forall (A B : Type) (f : A -> T B),
        ϕ B ∘ bind T T A B f = bind U U A B (ϕ B ∘ f) ∘ ϕ A;
      kmon_hom_ret : forall (A : Type),
        ϕ A ∘ ret T A = ret U A;
    }.

End class.

(** *** Right modules *)
(******************************************************************************)
Section class.

  Context
    (T : Type -> Type)
    (U : Type -> Type)
    `{Return T} `{Bind T T} `{Bind T U}.

  Class RightModule :=
    { kmod_monad :> Monad T;
      kmod_bind1 : forall (A : Type),
        bind T U A A (ret T A) = @id (U A);
      kmod_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind T U B C g ∘ bind T U A B f = bind T U A C (g ⋆1 f);
    }.

End class.

(** * Kleisli presentation of monads *)
(******************************************************************************)

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
      (@ret T _ B) ⋆1 f = f.
  Proof.
    intros. unfold kc1. now rewrite kmon_bind1.
  Qed.

  (** ** Right identity law *)
  Theorem kleisli_id_r : forall (g : B -> T C),
      g ⋆1 (@ret T _ B) = g.
  Proof.
    intros. unfold kc1. now rewrite (kmon_bind0 T).
  Qed.

  (** ** Associativity law *)
  Theorem kleisli_assoc : forall (h : C -> T D) (g : B -> T C) (f : A -> T B),
      h ⋆1 (g ⋆1 f) = (h ⋆1 g) ⋆1 f.
  Proof.
    intros. unfold kc1 at 3.
    now rewrite <- (kmon_bind2 T).
  Qed.

End Monad_kleisli_category.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Notation "g ⋆1 f" := (kc1 _ g f) (at level 60) : tealeaves_scope.

End Notations.

(** * Derived functor instance *)
(******************************************************************************)
Module DerivedInstances.

  #[export] Instance Map_Bind
    (T : Type -> Type)
    `{Return T}
    `{Bind T T} : Map T :=
  fun A B (f : A -> B) => bind T T A B (ret T B ∘ f).

  Section with_monad.

    Context
      (T : Type -> Type)
        `{Monad T}.

    #[export] Instance Monad_Functor: Functor T.
    Proof.
      constructor.
      - intros. unfold transparent tcs.
        unfold compose. now rewrite kmon_bind1.
      - intros. unfold transparent tcs.
        rewrite (kmon_bind2 T).
        unfold kc1. reassociate <- near (bind T T B C (ret T C ∘ g)).
        now rewrite (kmon_bind0 T).
    Qed.

    (** *** Composition with [map] *)
    (******************************************************************************)
    Lemma bind_map : forall `(g : B -> T C) `(f : A -> B),
        bind T T B C g ∘ map T A B f = bind T T A C (g ∘ f).
    Proof.
      intros. unfold transparent tcs.
      rewrite (kmon_bind2 T).
      fequal. unfold kc1.
      reassociate <-. now rewrite (kmon_bind0 T).
    Qed.

    Corollary map_bind : forall `(g : B -> C) `(f : A -> T B),
        map T _ _ g ∘ bind T T _ _ f = bind T T _ _ (map T _ _ g ∘ f).
    Proof.
      intros. unfold transparent tcs.
      now rewrite (kmon_bind2 T).
    Qed.

    (** *** Special cases for Kleisli composition *)
    (******************************************************************************)
    Lemma kc1_00 : forall `(g : B -> C) `(f : A -> B),
        (ret T C ∘ g) ⋆1 (ret T B ∘ f) = ret T C ∘ (g ∘ f).
    Proof.
      intros. unfold kc1.
      reassociate <-. now rewrite (kmon_bind0 T).
    Qed.

    Lemma kc1_10 : forall `(g : B -> T C) `(f : A -> B),
        g ⋆1 (ret T B ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc1.
      reassociate <-. now rewrite (kmon_bind0 T).
    Qed.

    Lemma kc1_01 : forall `(g : B -> C) `(f : A -> T B),
        (ret T C ∘ g) ⋆1 f = map T B C g ∘ f.
    Proof.
      intros. unfold kc1.
      reflexivity.
    Qed.

    (** *** Other rules for Kleisli composition *)
    (******************************************************************************)
    Lemma kc1_asc1 : forall `(g : B -> C) `(h : C -> T D) `(f : A -> T B),
        (h ∘ g) ⋆1 f = h ⋆1 (map T B C g ∘ f).
    Proof.
      intros. unfold kc1.
      reassociate <-.
      rewrite (bind_map).
      reflexivity.
    Qed.

    Lemma kc1_asc2 : forall `(f : A -> B) `(g : B -> T C) `(h : C -> T D),
        h ⋆1 (g ∘ f) = (h ⋆1 g) ∘ f.
    Proof.
      intros. unfold kc1.
      reflexivity.
    Qed.

    (** *** Naturality of <<ret>> *)
    (******************************************************************************)
    #[export] Instance mon_ret_natural : Natural (@ret T _).
    Proof.
      constructor; try typeclasses eauto.
      intros.
      unfold_ops @Map_Bind.
      rewrite (kmon_bind0 T).
      reflexivity.
    Qed.

  End with_monad.

End DerivedInstances.
