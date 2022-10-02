From Tealeaves Require Export
  Classes.Algebraic.Comonad.

Import Functor.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables W A.

(** * Right Comodules *)
(******************************************************************************)
Section RightComodule_operations.

  Context
    (F W : Type -> Type).

  Class RightCoaction := right_coaction : F ⇒ F ∘ W.

End RightComodule_operations.

Section RightComodule_class.

  Context
    (F W : Type -> Type)
    `{Fmap W} `{Cojoin W} `{Extract W}
    `{Fmap F} `{RightCoaction F W}.

  Class RightComodule :=
    { rcom_comonad :> Comonad W;
      rcom_functor :> Functor F;
      rcom_coaction_natural :> Natural (@right_coaction F W _);
      rcom_fmap_extr_coaction :
        `(fmap F (extract W) ∘ right_coaction F W A = @id (F A));
      rcom_coaction_coaction :
        `(right_coaction F W (W A) ∘ right_coaction F W A =
          fmap F (cojoin W) ∘ right_coaction F W A);
    }.

End RightComodule_class.

Arguments right_coaction F {W}%function_scope {RightCoaction} {A}%type_scope.

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

(** ** Comonads form right co-modules *)
(******************************************************************************)
Section RightComodule_Comonad.

  Instance RightCoaction_Cojoin `{Cojoin W} : RightCoaction W W := @cojoin W _.

  #[program] Instance RightComodule_Comonad `{Comonad W} : RightComodule W W :=
  {| rcom_fmap_extr_coaction := com_fmap_extr_cojoin W;
     rcom_coaction_coaction := com_cojoin_cojoin W;
  |}.

End RightComodule_Comonad.
