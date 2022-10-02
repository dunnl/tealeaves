From Tealeaves Require Export
  Classes.Kleisli.Monad
  Classes.Kleisli.Traversable.Monad
  Theory.Kleisli.Monad.ToFunctor
  Theory.Kleisli.Traversable.Functor.ToFunctor
  Theory.Kleisli.Traversable.Monad.Properties
  Theory.Kleisli.Traversable.Monad.ToFunctor
  Classes.Kleisli.Traversable.Functor.

Import Kleisli.Monad.Notations.
Import Traversable.Monad.Notations.

#[local] Generalizable Variables W G T A B C.

(** * Kleisli Traversble Monad: Derived Kleisli instances *)
(******************************************************************************)

(** ** Lesser Kleisli operations *)
(******************************************************************************)
Module Operations.
  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{Return T}
      `{Bindt T T}.

    #[export] Instance Bind_Bindt: Bind T T := fun A B f => bindt T (fun A => A) f.
    #[export] Instance Traverse_Bindt: Traverse T := fun G _ _ _ A B f => bindt T G (fmap G (ret T) ∘ f).

  End with_kleisli.
End Operations.

(** ** Specifications for lesser Kleisli operations *)
(******************************************************************************)
Section special_cases.

  Import Traversable.Monad.ToFunctor.Operation.
  Import Operations.

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

(** ** Lesser Kleisli instances *)
(******************************************************************************)
Module DerivedInstances.

  Import Traversable.Monad.ToFunctor.Operation.
  Import Operations.

  Section with_monad.

    Context
      (T : Type -> Type)
      `{Traversable.Monad.Monad T}.

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

  End with_monad.

End DerivedInstances.

(** ** Special cases for Kleisli composition *)
(******************************************************************************)
Section Kleisli_composition.

  Import Traversable.Monad.ToFunctor.Operation.
  Import Operations.

  Context
    (T : Type -> Type)
    `{Traversable.Monad.Monad T}
    (G1 : Type -> Type)
    (G2 : Type -> Type)
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
      (fmap G2 (ret T) ∘ g) ⋆tm f = traverse T G2 g ∘ f.
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
      g ⋆tm f = bindt T G2 g ∘ f.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma kcompose_tm30 : forall `(g : B -> G2 (T C)) `(f : A -> B),
      g ⋆tm (ret T ∘ f) = g ∘ f.
  Proof.
    intros. unfold kcompose_tm. reassociate <-.
    change (fmap (fun A => A) ?f) with f.
    rewrite (ktm_bindt0 T); auto.
  Qed.

  Lemma kcompose_tm13 : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
      (fmap G2 (ret T) ∘ g) ⋆tm f = fmap G1 (traverse T G2 g) ∘ f.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma kcompose_tm23 : forall `(g : B -> T C) `(f : A -> G1 (T B)),
      g ⋆tm f = fmap G1 (bind T g) ∘ f.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma kcompose_tm03 : forall `(g : B -> C) `(f : A -> G1 (T B)),
      (ret T ∘ g) ⋆tm f = fmap G1 (fmap T g) ∘ f.
  Proof.
    intros. reflexivity.
  Qed.

End Kleisli_composition.

(** ** Composition with lesser Kleisli operations *)
(******************************************************************************)
Section Kleisli_composition.

  Import Traversable.Monad.ToFunctor.Operation.
  Import Operations.
  Import DerivedInstances.

  Context
    (T : Type -> Type)
    `{Traversable.Monad.Monad T}
    (G1 : Type -> Type)
    (G2 : Type -> Type)
    `{Applicative G2}
    `{Applicative G1}.

  (** ** Composition with <<traverse>> *)
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

  (** ** Composition with <<bind>> *)
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

  (** ** Composition between <<traverse>> and <<bind>> *)
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
    rewrite kcompose_tm31; auto.
    typeclasses eauto.
  Qed.

  (** ** Composition between <<traverse>> and <<fmap>> *)
  (******************************************************************************)
  Lemma fmap_traverse : forall (A B C : Type)
                          (g : B -> C)
                          (f : A -> G1 B),
      fmap G1 (fmap T g) ∘ traverse T G1 f =
        traverse T G1 (fmap G1 g ∘ f).
  Proof.
    intros.
    change (@Fmap_Bindt T H0 H) with (@Operation.Fmap_Traverse T _).
    rewrite (fmap_traverse T G1); try typeclasses eauto.
    reflexivity.
  Qed.

  Lemma traverse_fmap: forall (A B C : Type)
                         (g : B -> G2 C)
                         (f : A -> B),
      traverse T G2 g ∘ fmap T f =
        traverse T G2 (g ∘ f).
  Proof.
    intros.
    change (@Fmap_Bindt T H0 H) with (@Operation.Fmap_Traverse T _).
    rewrite (traverse_fmap T G2); try typeclasses eauto.
    reflexivity.
  Qed.

  (** ** Composition between <<bind>> and <<fmap>> *)
  (******************************************************************************)
  Lemma bind_fmap : forall (A B C : Type)
                          (g : B -> T C)
                          (f : A -> B),
      bind T g ∘ fmap T f = bind T (g ∘ f).
  Proof.
    intros.
    change (@Fmap_Bindt T H0 H) with (@Operation.Fmap_Bind T _ _).
    now rewrite (ToFunctor.Instances.bind_fmap T).
  Qed.

  Lemma fmap_bind : forall (A B C : Type)
                         (g : B -> C)
                         (f : A -> T B),
      fmap T g ∘ bind T f = bind T (fmap T g ∘ f).
  Proof.
    intros.
    change (@Fmap_Bindt T H0 H) with (@Operation.Fmap_Bind T _ _).
    now rewrite (ToFunctor.Instances.fmap_bind T).
  Qed.

End Kleisli_composition.
