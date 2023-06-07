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

(** * Batch *)
(******************************************************************************)
Section with_functor.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  Lemma runBatch_batch : forall  `{Applicative G} (A B : Type) (f : A -> G (T B)),
      runBatch f ∘ (@batch A (T B)) = f.
  Proof.
    intros. ext a. cbn.
    now rewrite ap1.
  Qed.

  Definition toBatch_tm {A : Type} (B : Type) : T A -> @Batch A (T B) (T B) :=
    bindt T (Batch A (T B)) (batch (T B)).

End with_functor.

Import Derived.

(** * <<foldMap>> on monads *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  (** ** Composition with <<bindt>> *)
  (******************************************************************************)
  Lemma foldMap_bindt `{Applicative G} `{Monoid M} : forall `(g : B -> M) `(f : A -> G (T B)),
      fmap G (foldMap T g) ∘ bindt T G f =
        foldMap T (fmap G (foldMap T g) ∘ f).
  Proof.
    intros. unfold foldMap.
    rewrite (traverse_bindt T G (const M)).
    unfold_ops @Traverse_Bindt.
    fequal.
    - ext A' B' f' t. unfold_ops @Fmap_compose @Fmap_const.
      now rewrite (fun_fmap_id G).
    - ext A' B' [a b]. reflexivity.
  Qed.

  (** ** Composition with <<bind>> and <<ret>> *)
  (******************************************************************************)
  Lemma foldMap_bind `{Monoid M} : forall `(g : B -> M) `(f : A -> T B),
      foldMap T g ∘ bind T f =
        foldMap T (foldMap T g ∘ f).
  Proof.
    intros. unfold foldMap. rewrite (traverse_bind T (const M)).
    reflexivity.
  Qed.

  Lemma foldMap_ret `{Monoid M} : forall `(f : A -> M),
      foldMap T f ∘ ret T = f.
  Proof.
    intros. unfold foldMap. unfold_ops @Traverse_Bindt.
    rewrite (ktm_bindt0 T _ _ (G := const M)).
    reflexivity.
  Qed.

End with_monad.

Import Classes.Kleisli.Traversable.Functor.ToFunctor.

(** ** Expressing operations using <<runBatch>> *)
(******************************************************************************)
Section with_kleisli.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  Lemma bindt_to_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt T G f = runBatch f ∘ toBatch_tm T B.
  Proof.
    unfold toBatch_tm.
    rewrite (ktm_morph T (ϕ := @runBatch A G (T B) f _ _ _)).
    now rewrite (runBatch_batch T).
  Qed.

  Lemma traverse_to_runBatch `{Applicative G} `(f : A -> G B) :
    traverse T G f = runBatch f ∘ toBatch T B.
  Proof.
    now rewrite (traverse_to_runBatch T).
  Qed.

  Corollary fmap_to_runBatch `(f : A -> B) :
    fmap T f = runBatch f ∘ toBatch T B.
  Proof.
    change (@Fmap_Bindt T H0 H) with (ToFunctor.Fmap_Traverse T).
    rewrite (fmap_to_traverse T).
    now rewrite traverse_to_runBatch.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
    @id (T A) = runBatch (@id A) ∘ toBatch T A.
  Proof.
    intros. rewrite <- (trf_traverse_id T).
    rewrite traverse_to_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_to_runBatch : forall `{Monoid M} (fake : Type) `(f : A -> M),
      foldMap T f = runBatch f ∘ toBatch_tm T fake.
  Proof.
    intros.
    unfold foldMap.
    rewrite (traverse_constant_applicative2 T f False fake).
    rewrite (traverse_to_bindt).
    rewrite (bindt_to_runBatch).
    reflexivity.
  Qed.

End with_kleisli.

Import Sets.Notations.
Import Setlike.Functor.Notations.

(** * Characterizing <<∈>> *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{Kleisli.Traversable.Monad.Monad T}.

  #[export] Instance Monad_Hom_Toset : Kleisli.Monad.Monad_Hom T set (@toset T _).
  Proof.
    constructor.
    - intros.
      unfold_ops @Toset_Traverse.
      rewrite (foldMap_bind T (ret set) f).
      unfold_ops @Traverse_Bindt.
      rewrite (foldMap_morphism T).
      rewrite (kmon_bind0 set).
      reflexivity.
    - intros.
      unfold_ops @Toset_Traverse.
      rewrite (foldMap_ret T).
      reflexivity.
  Qed.

  Theorem in_ret_iff :
    forall (A : Type) (a1 a2 : A), a1 ∈ ret T a2 <-> a1 = a2.
  Proof.
    intros. unfold_ops @Toset_Traverse.
    compose near a2 on left. rewrite (foldMap_ret T).
    solve_basic_set.
  Qed.

  Theorem in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros. compose near t on left.
    rewrite (kmon_hom_bind T set); try typeclasses eauto.
    unfold compose. now rewrite bind_set_spec.
  Qed.

End with_monad.

(** * Respectfulness properties *)
(******************************************************************************)
Section respectfulness_properties.

  Context
    (T : Type -> Type)
    `{Traversable.Monad.Monad T}.

  Lemma bindt_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G (T B)) `(f2 : A -> G (T B)) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> bindt T G f1 t = bindt T G f2 t.
  Proof.
    introv ? hyp. do 2 (rewrite (bindt_to_runBatch T); auto).
    unfold toset, Toset_Traverse in hyp.
    rewrite (foldMap_to_runBatch T B) in hyp.
    unfold compose in *.
    induction (toBatch_tm T B t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros. apply hyp. now left.
      + apply hyp. now right.
  Qed.

  Lemma traverse_respectful : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse T G f1 t = traverse T G f2 t.
  Proof.
    apply (Traversable.Functor.traverse_respectful T).
  Qed.

  Lemma traverse_respectful_pure : forall (G : Type -> Type)
    `{Applicative G} `(f1 : A -> G A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = pure G a) -> traverse T G f1 t = pure G t.
  Proof.
    apply (Traversable.Functor.traverse_respectful_pure T).
  Qed.

  Lemma traverse_respectful_fmap {A B} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure G (g a)) -> traverse T G f t = pure G (fmap T g t).
  Proof.
    change (@Fmap_Bindt T H0 H) with (@ToFunctor.Fmap_Traverse T _).
    apply (Traversable.Functor.traverse_respectful_fmap T).
  Qed.

  Corollary traverse_respectful_id {A} : forall (G : Type -> Type)
    `{Applicative G} t (f : A -> G A),
      (forall a, a ∈ t -> f a = pure G a) -> traverse T G f t = pure G t.
  Proof.
    apply (Traversable.Functor.traverse_respectful_id T).
  Qed.

  Corollary fmap_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = f2 a) -> fmap T f1 t = fmap T f2 t.
  Proof.
    intros. change (@Fmap_Bindt T H0 H) with (@ToFunctor.Fmap_Traverse T _).
    now apply (Traversable.Functor.fmap_respectful T).
  Qed.

  Corollary fmap_respectful_id : forall `(f1 : A -> A) (t : T A),
    (forall (a : A), a ∈ t -> f1 a = a) -> fmap T f1 t = t.
  Proof.
    intros. change (@Fmap_Bindt T H0 H) with (@ToFunctor.Fmap_Traverse T _).
    now apply (Traversable.Functor.fmap_respectful_id T).
  Qed.

End respectfulness_properties.
