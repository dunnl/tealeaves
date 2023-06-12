From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Classes.Monad.

#[local] Generalizable Variables T G A B C ϕ M.

Section operations.

  Context
    (T : Type -> Type)
    (F : Type -> Type).

  Class Bindt :=
    bindt : forall (G : Type -> Type) (A B : Type) `{Fmap G} `{Pure G} `{Mult G},
        (A -> G (T B)) -> F A -> G (F B).

End operations.

Definition kcompose_tm
  {A B C : Type}
  `{Fmap G1} `{Pure G1} `{Mult G1}
  `{Fmap G2} `{Pure G2} `{Mult G2}
  `{Bindt T T} :
  (B -> G2 (T C)) ->
  (A -> G1 (T B)) ->
  (A -> G1 (G2 (T C))) :=
  fun g f => fmap G1 (bindt T T G2 B C g) ∘ f.

#[local] Infix "⋆tm" := kcompose_tm (at level 60) : tealeaves_scope.

Section class.

  Context
    (T : Type -> Type)
    `{Return T}
    `{Bindt T T}.

  Class Monad :=
    { ktm_bindt0 : forall (A B : Type) `{Applicative G} (f : A -> G (T B)),
        bindt T T G A B f ∘ ret T = f;
      ktm_bindt1 : forall (A : Type),
        bindt T T (fun A => A) A A (ret T) = @id (T A);
      ktm_bindt2 : forall (A B C : Type) `{Applicative G1} `{Applicative G2}
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        fmap G1 (bindt T T G2 B C g) ∘ bindt T T G1 A B f =
          bindt T T (G1 ∘ G2) A C (g ⋆tm f);
      ktm_morph : forall `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : A -> G1 (T B)),
          ϕ (T B) ∘ bindt T T G1 A B f = bindt T T G2 A B (ϕ (T B) ∘ f);
    }.

End class.

#[global] Arguments bindt {T}%function_scope (F)%function_scope
  {Bindt} G%function_scope {A B}%type_scope {H H0 H1} _%function_scope _.

Module Notations.

  Infix "⋆tm" := kcompose_tm (at level 60) : tealeaves_scope.

End Notations.

Section with_kleisli.

  Context
    (T : Type -> Type)
    `{Monad T}.

  Lemma kcompose_tm_ret : forall `{Applicative G1} `{Applicative G2} `(g : B -> G2 C) `(f : A -> G1 B),
      (fmap G2 (ret T) ∘ g) ⋆tm (fmap G1 (ret T) ∘ f) = fmap (G1 ∘ G2) (ret T) ∘ (fmap G1 g ∘ f).
  Proof.
    intros. unfold_ops @Fmap_compose.
    reassociate <- on right. unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G1).
    unfold kcompose_tm. reassociate <- on left.
    rewrite (fun_fmap_fmap G1).
    rewrite (ktm_bindt0 T); auto.
  Qed.

  Corollary kcompose_tm_ret_I : forall `(g : B -> C) `(f : A -> B),
      (ret T ∘ g) ⋆tm (ret T ∘ f) = ret T ∘ (g ∘ f).
  Proof.
    intros. change (@ret T _ C) with (fmap (fun A => A) (@ret T _ C)).
    change (@ret T _ B) with (fmap (fun A => A) (@ret T _ B)).
    rewrite (kcompose_tm_ret (G2 := fun A => A) (G1 := fun A => A)).
    reflexivity.
  Qed.

  Lemma kcompose_tm_ret2 : forall `{Applicative G2} `(g : B -> G2 (T C)) `(f : A -> B),
      g ⋆tm ret T ∘ f = g ∘ f.
  Proof.
    intros. unfold kcompose_tm.
    reassociate <- on left. change (fmap (fun A => A) ?g) with g.
    now rewrite (ktm_bindt0 T).
  Qed.

End with_kleisli.

From Tealeaves Require Import
  Kleisli.Monad
  Kleisli.Traversable.Functor.

Import Kleisli.Monad.Notations.

(** * Derived instances *)
(******************************************************************************)
Module Derived.

  Section operations.

    Context
      (T : Type -> Type)
      `{Bindt T T}
      `{Return T}.

    #[export] Instance Fmap_Bindt : Fmap T :=
      fun (A B : Type) (f : A -> B) => bindt T (fun A => A) (ret T ∘ f).
    #[export] Instance Bind_Bindt: Bind T T :=
      fun A B f => bindt T (fun A => A) f.
    #[export] Instance Traverse_Bindt: Traverse T :=
      fun G _ _ _ A B f => bindt T G (fmap G (ret T) ∘ f).

  End operations.

  Section special_cases.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Return T}
      `{Bindt T T}
      `{Applicative G}.

    (** *** Rewriting rules for special cases of <<bindt>> *)
    (******************************************************************************)
    Lemma bind_to_bindt `(f : A -> T B):
      bind T f = bindt T (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_bindt `(f : A -> G B):
      traverse T G f = bindt T G (fmap G (ret T) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma fmapt_to_bindt `(f : A -> G B):
      traverse T G f = bindt T G (fmap G (ret T) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma fmap_to_bindt `(f : A -> B):
      fmap T f = bindt T (fun A => A) (ret T ∘ f).
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

    (** *** Rewriting rules for special cases of <<bind>> *)
    (******************************************************************************)
    Lemma fmap_to_bind `(f : A -> B):
      fmap T f = bind T (ret T ∘ f).
    Proof.
      reflexivity.
    Qed.

  End special_cases.

  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Kleisli.Traversable.Monad.Monad T}.

    (** *** Functor instance *)
    (******************************************************************************)
    Lemma fmap_id : forall (A : Type),
        fmap T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Fmap_Bindt.
      change (?g ∘ id) with g.
      now rewrite (ktm_bindt1 T).
    Qed.

    Lemma fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Bindt.
      change (bindt T (fun A : Type => A) (ret T ∘ g))
        with (fmap (fun A => A) (bindt T (fun A => A) (ret T ∘ g))).
      rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A) (G2 := fun A => A));
        try typeclasses eauto.
      fequal. now rewrite Mult_compose_identity1.
      rewrite kcompose_tm_ret_I; auto.
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_fmap_id := fmap_id;
        fun_fmap_fmap := fmap_fmap;
      |}.

    (** *** Monad instance *)
    (******************************************************************************)
    #[export] Instance: Kleisli.Monad.Monad T.
    Proof.
      constructor; unfold_ops @Bind_Bindt.
      - intros. now rewrite (ktm_bindt0 T _ _ (G := fun A => A)).
      - intros. now rewrite (ktm_bindt1 T).
      - intros.
        change_left (fmap (fun A => A) (bindt T (fun A0 : Type => A0) g) ∘ bindt T (fun A0 : Type => A0) f).
        rewrite (ktm_bindt2 T _ _ _ (G2 := fun A => A) (G1 := fun A => A)).
        fequal. now rewrite Mult_compose_identity1.
    Qed.

    (** *** Traversable functor instance *)
    (******************************************************************************)
    #[export] Instance: Kleisli.Traversable.Functor.TraversableFunctor T.
    Proof.
      constructor; unfold_ops @Traverse_Bindt.
      - intros. change (?g ∘ id) with g.
        change (fmap (fun A => A) ?g) with g.
        now rewrite (ktm_bindt1 T).
      - intros. rewrite (ktm_bindt2 T); auto.
        rewrite kcompose_tm_ret; auto.
      - intros. rewrite (ktm_morph T); auto. reassociate <-.
        fequal. unfold compose. ext a. now rewrite (appmor_natural G1 G2).
    Qed.

  End with_kleisli.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Section Kleisli_composition.

    Context
     `{Traversable.Monad.Monad T}
      `{Applicative G2}
      `{Applicative G1}.
    (*
    t/m:
    00 0 no t or m
    01 1 no m
    10 2 no t
    11 3 everything
     *)

  Lemma kcompose_tm00 : forall `(g : B -> C) `(f : A -> B),
     kcompose_tm (G1 := fun A => A) (G2 := fun A => A) (ret T ∘ g) (ret T ∘ f) = ret T ∘ g ∘ f.
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    change (fmap (fun A => A) ?f) with f.
    rewrite (ktm_bindt0 T _ _ (G := fun A => A)); auto.
  Qed.

  Lemma kcompose_tm11 : forall `(g : B -> G2 C) `(f : A -> G1 B),
      (fmap G2 (ret T) ∘ g) ⋆tm (fmap G1 (ret T) ∘ f) = fmap (G1 ∘ G2) (ret T) ∘ (fmap G1 g ∘ f).
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    rewrite (fun_fmap_fmap G1). reassociate <-.
    unfold_ops @Fmap_compose.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap G1).
    rewrite (ktm_bindt0 T); auto.
  Qed.

  Lemma kcompose_tm22 : forall `(g : B -> T C) `(f : A -> T B),
      kcompose_tm (G1 := fun A => A) (G2 := fun A => A) g f = (g ⋆ f).
  Proof.
    intros. unfold kcompose_tm, kcompose.
    reflexivity.
  Qed.

  Lemma kcompose_tm12 : forall `(g : B -> G2 C) `(f : A -> T B),
      (fmap G2 (ret T) ∘ g) ⋆tm (f : A -> (fun A => A)(T B)) =
        traverse T G2 g ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm21 : forall `(g : B -> T C) `(f : A -> G1 B),
      kcompose_tm (G1 := G1) (G2 := fun A => A) g (fmap G1 (ret T) ∘ f) = (fmap G1 g ∘ f).
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    rewrite (fun_fmap_fmap G1). rewrite (ktm_bindt0 T _ _ (G := fun A => A)); auto.
  Qed.

  Lemma kcompose_tm31 : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
      g ⋆tm fmap G1 (ret T) ∘ f = fmap G1 g ∘ f.
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    rewrite (fun_fmap_fmap G1). rewrite (ktm_bindt0 T); auto.
  Qed.

  Lemma kcompose_tm32 : forall `(g : B -> G2 (T C)) `(f : A -> T B),
      kcompose_tm (G1 := fun A => A) g f = bindt T G2 g ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm30 : forall `(g : B -> G2 (T C)) `(f : A -> B),
      kcompose_tm (G1 := fun A => A) g (ret T ∘ f) = g ∘ f.
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    change (fmap (fun A => A) ?f) with f.
    rewrite (ktm_bindt0 T); auto.
  Qed.

  Lemma kcompose_tm13 : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
      (fmap G2 (ret T) ∘ g) ⋆tm f = fmap G1 (traverse T G2 g) ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm23 : forall `(g : B -> T C) `(f : A -> G1 (T B)),
      kcompose_tm (G2 := fun A => A) g f = fmap G1 (bind T g) ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm03 : forall `(g : B -> C) `(f : A -> G1 (T B)),
      kcompose_tm (G2 := fun A => A) (ret T ∘ g) f = fmap G1 (fmap T g) ∘ f.
  Proof.
    reflexivity.
  Qed.

  Lemma kcompose_tm_lunit : forall `(g : A -> G2 (T B)),
     kcompose_tm (G1 := fun A => A) g (ret T) = g.
  Proof.
    intros. change (ret T) with (ret T ∘ (@id A)).
    now rewrite (kcompose_tm30).
  Qed.

  Lemma kcompose_tm_runit : forall `(f : A -> G1 (T B)),
     kcompose_tm (G2 := fun A => A) (ret T) f = f.
  Proof.
    intros. change (ret T) with (ret T ∘ (@id B)).
    rewrite (kcompose_tm03).
    rewrite (fun_fmap_id T).
    now rewrite (fun_fmap_id G1).
  Qed.

  End Kleisli_composition.

  (** ** Composition with lesser Kleisli operations *)
  (******************************************************************************)
  Section Kleisli_composition.

    Context
      (T : Type -> Type)
     `{Traversable.Monad.Monad T}
      (G1 : Type -> Type)
      (G2 : Type -> Type)
      `{Applicative G2}
      `{Applicative G1}.

  (** *** Composition with <<fmap>> *)
  (******************************************************************************)
  Lemma fmap_bindt : forall `(g : B -> C) `(f : A -> G1 (T B)),
      fmap G1 (fmap T g) ∘ bindt T G1 f = bindt T G1 (fmap G1 (fmap T g) ∘ f).
  Proof.
    intros. unfold fmap at 2. unfold_ops @Fmap_Bindt.
    rewrite (ktm_bindt2 T _ _ _ (G1 := G1) (G2 := fun A => A)).
    fequal. rewrite Mult_compose_identity1.
    reflexivity.
  Qed.

  Lemma bindt_fmap : forall `(g : B -> G2 (T C)) `(f : A -> B),
      bindt T G2 g ∘ fmap T f = bindt T G2 (g ∘ f).
  Proof.
    intros. unfold fmap. unfold_ops @Fmap_Bindt.
    change_left (fmap (fun A => A) (bindt T G2 g) ∘ bindt T (fun A => A) (ret T ∘ f)).
    rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A) (G2 := G2)).
    fequal. now rewrite Mult_compose_identity2.
    rewrite kcompose_tm30; auto.
  Qed.

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma traverse_bindt : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
      fmap G1 (traverse T G2 g) ∘ bindt T G1 f =
        bindt T (G1 ∘ G2) (fmap G1 (traverse T G2 g) ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Bindt @Bind_Bindt.
    rewrite (ktm_bindt2 T); auto.
  Qed.

  Lemma bindt_traverse : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
      fmap G1 (bindt T G2 g) ∘ traverse T G1 f =
        bindt T (G1 ∘ G2) (fmap G1 g ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Bindt @Bind_Bindt.
    rewrite (ktm_bindt2 T); auto.
    fequal. rewrite kcompose_tm31; auto.
  Qed.

  (** *** Composition with <<bind>> *)
  (******************************************************************************)
  Lemma bind_bindt : forall `(g : B -> T C) `(f : A -> G1 (T B)),
      fmap G1 (bind T g) ∘ bindt T G1 f =
        bindt T G1 (fmap G1 (bind T g) ∘ f).
  Proof.
    intros. unfold_ops @Bind_Bindt @Bind_Bindt.
    rewrite (ktm_bindt2 T _ _ _ (G2 := fun A => A) (G1 := G1)); auto.
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma bindt_bind : forall `(g : B -> G2 (T C)) `(f : A -> T B),
      bindt T G2 g ∘ bind T f =
        bindt T G2 (bindt T G2 g ∘ f).
  Proof.
    intros. unfold_ops @Bind_Bindt @Bind_Bindt.
    change_left (fmap (fun A => A) (bindt T G2 g) ∘ (bindt T (fun A0 : Type => A0) f)).
    rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A) (G2 := G2)); auto.
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  (** *** Composition between <<traverse>> and <<bind>> *)
  (******************************************************************************)
  Lemma traverse_bind : forall `(g : B -> G2 C) `(f : A -> T B),
      traverse T G2 g ∘ bind T f =
        bindt T G2 (traverse T G2 g ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Bindt @Bind_Bindt.
    change_left (fmap (fun A => A) (bindt T G2 (fmap G2 (ret T) ∘ g)) ∘ bindt T (fun A0 : Type => A0) f).
    rewrite (ktm_bindt2 T _ _ _ (G1 := fun A => A)); auto.
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma bind_traverse : forall `(g : B -> T C) `(f : A -> G1 B),
      fmap G1 (bind T g) ∘ traverse T G1 f =
        bindt T G1 (fmap G1 g ∘ f).
  Proof.
    intros. unfold_ops @Traverse_Bindt @Bind_Bindt.
    rewrite (ktm_bindt2 T _ _ _ (G2 := fun A => A)); auto.
    fequal. now rewrite Mult_compose_identity1.
    now rewrite kcompose_tm31.
  Qed.

  (** *** Composition between <<traverse>> and <<fmap>> *)
  (******************************************************************************)
  Lemma fmap_traverse : forall (A B C : Type)
                          (g : B -> C)
                          (f : A -> G1 B),
      fmap G1 (fmap T g) ∘ traverse T G1 f =
        traverse T G1 (fmap G1 g ∘ f).
  Proof.
    intros.
    change (@Fmap_Bindt T H0 H) with (@ToFunctor.Fmap_Traverse T _).
    rewrite (ToFunctor.fmap_traverse T G1); try typeclasses eauto.
    reflexivity.
  Qed.

  Lemma traverse_fmap: forall (A B C : Type)
                         (g : B -> G2 C)
                         (f : A -> B),
      traverse T G2 g ∘ fmap T f =
        traverse T G2 (g ∘ f).
  Proof.
    intros.
    change (@Fmap_Bindt T H0 H) with (@ToFunctor.Fmap_Traverse T _).
    rewrite (ToFunctor.traverse_fmap T G2); try typeclasses eauto.
    reflexivity.
  Qed.

  (** *** Composition between <<bind>> and <<fmap>> *)
  (******************************************************************************)
  Lemma bind_fmap : forall (A B C : Type)
                          (g : B -> T C)
                          (f : A -> B),
      bind T g ∘ fmap T f = bind T (g ∘ f).
  Proof.
    intros.
    change (@Fmap_Bindt T H0 H) with (@ToFunctor.Fmap_Bind T _ _).
    now rewrite (ToFunctor.bind_fmap T).
  Qed.

  Lemma fmap_bind : forall (A B C : Type)
                         (g : B -> C)
                         (f : A -> T B),
      fmap T g ∘ bind T f = bind T (fmap T g ∘ f).
  Proof.
    intros.
    change (@Fmap_Bindt T H0 H) with (@ToFunctor.Fmap_Bind T _ _).
    now rewrite (ToFunctor.fmap_bind T).
  Qed.

  End Kleisli_composition.

End Derived.
