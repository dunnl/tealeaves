From Tealeaves Require Export
     Singlesorted.Classes.Comonad.

Import Functor.Notations.
Import Comonad.Notations.
#[local] Open Scope tealeaves_scope.

(** * Right Comodules *)
(******************************************************************************)

(** The sole operation of a right comodule is a right coaction: *)
Section RightComodule_operations.

  Context
    (F W : Type -> Type).

  Class RightCoaction := right_coaction : F ⇒ F ∘ W.

End RightComodule_operations.

Arguments right_coaction F {W}%function_scope {RightCoaction} {A}%type_scope.

Section RightComodule_class.

  Context
    (F W : Type -> Type)
    `{Comonad W}
    `{Functor F}.

  Class RightComodule `{RightCoaction F W} :=
    { rcom_comonad :> Comonad W;
      rcom_functor :> Functor F;
      rcom_coaction_natural :> Natural (@right_coaction F W _);
      rcom_fmap_extr_coaction :
        `(fmap F (extract W) ∘ right_coaction F = @id (F A));
      rcom_coaction_coaction :
        `(right_coaction F (A := W A) ∘ right_coaction F =
          fmap F (cojoin W (A := A)) ∘ right_coaction F);
    }.

End RightComodule_class.

(** ** Homomorphisms of right comodules *)
(******************************************************************************)
Section RightComoduleHomomorphism.

  Context
    (W F G : Type -> Type)
    `{Comonad W}
    `{Fmap F}
    `{Fmap G}
    `{RightCoaction F W}
    `{RightCoaction G W}
    `{! RightComodule F W}
    `{! RightComodule G W}.

  Class RightComoduleHom (ϕ : forall {A}, F A -> G A) :=
    { rcomh_natural :
        `{Natural (F := F) (G := G) (fun A => ϕ)};
      rcomh_morphism : forall A (x : F A),
          ϕ (right_coaction F x) = right_coaction G (ϕ x);
    }.

End RightComoduleHomomorphism.

(** * Kleisli presentation of right modules *)
(******************************************************************************)

(** ** Kleisli operations *)
(******************************************************************************)
Class Cosub (F W : Type -> Type) :=
  cosub : forall {A B}, (W A -> B) -> F A -> F B.

Arguments cosub F {W}%function_scope {Cosub} {A B}%type_scope _%function_scope.

Instance Cosub_RightCoaction `{Fmap F} `{RightCoaction F W} : Cosub F W :=
  fun `(f : W A -> B) => fmap F f ∘ right_coaction F.

(** ** Specifications for sub-operations  *)
(******************************************************************************)
Section RightComodule_suboperations.

  Context
    (F W : Type -> Type)
    `{RightComodule F W}
    {A B C : Type}.

  (** *** [fmap] as a special case of [cosub] *)
  Corollary fmap_to_cosub : forall (f : A -> B),
      fmap F f = cosub F (f ∘ extract W).
  Proof.
    introv. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap F).
    reassociate -> on right.
    now rewrite (rcom_fmap_extr_coaction F W).
  Qed.

End RightComodule_suboperations.

(** ** Functoriality of [cosub] *)
(******************************************************************************)
Section RightComodule_cosub.

  Context
    (F : Type -> Type)
    `{RightComodule F W}
    {A B C : Type}.

  (** *** [cosub] identity *)
  Theorem cosub_id :
      cosub F (extract W) = @id (F A).
  Proof.
    unfold transparent tcs.
    now rewrite (rcom_fmap_extr_coaction F W).
  Qed.

  (** *** [cosub] composition *)
  Theorem cosub_cosub : forall (g : W B -> C) (f : W A -> B),
      cosub F g ∘ cosub F f = cosub F (g co⋆ f).
  Proof.
    introv. unfold transparent tcs. unfold cokcompose.
    reassociate <- on left.
    reassociate -> near (fmap F f).
    rewrite <- natural.
    reassociate <- on left.
    unfold transparent tcs.
    reassociate -> on left.
    rewrite (rcom_coaction_coaction F W).
    now rewrite <- 2(fun_fmap_fmap F).
  Qed.

End RightComodule_cosub.

(** ** Other composition laws for [cosub] *)
(******************************************************************************)
Section RightComodule_composition.

  Context
    (F : Type -> Type)
    `{RightComodule F W}
    {A B C : Type}.

  (** *** Other composition laws *)
  Corollary fmap_cosub : forall (f : W A -> B) (g : B -> C),
      fmap F g ∘ cosub F f = cosub F (g ∘ f).
  Proof.
    introv. unfold transparent tcs.
    now rewrite <- (fun_fmap_fmap F).
  Qed.

  Corollary cosub_fmap : forall (f : A -> B) (g : W B -> C),
      cosub F g ∘ fmap F f = cosub F (g ∘ fmap W f).
  Proof.
    introv. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap F).
    reassociate -> on left.
    now rewrite <- (natural (ϕ := @right_coaction F W _) f).
  Qed.

End RightComodule_composition.

(** ** Comonad self-actions from the right *)
(******************************************************************************)
Section RightComodule_Comonad.

  Instance RightCoaction_Cojoin `{Cojoin W} : RightCoaction W W := @cojoin W _.

  #[program] Instance RightComodule_Comonad `{Comonad W} : RightComodule W W :=
  {| rcom_fmap_extr_coaction := com_fmap_extr_cojoin W;
     rcom_coaction_coaction := com_cojoin_cojoin W;
  |}.

End RightComodule_Comonad.
