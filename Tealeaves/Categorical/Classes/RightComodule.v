From Tealeaves Require Export
  Categorical.Classes.Comonad.

Import Functor.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables W A.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.

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
    `{Map W} `{Cojoin W} `{Extract W}
    `{Map F} `{RightCoaction F W}.

  Class RightComodule :=
    { rcom_comonad :> Comonad W;
      rcom_functor :> Functor F;
      rcom_coaction_natural :> Natural (@right_coaction F W _);
      rcom_map_extr_coaction :
        `(map F (extract W A) ∘ right_coaction F W A = @id (F A));
      rcom_coaction_coaction :
        `(right_coaction F W (W A) ∘ right_coaction F W A =
          map F (cojoin W) ∘ right_coaction F W A);
    }.

End RightComodule_class.

Arguments right_coaction F {W}%function_scope {RightCoaction} {A}%type_scope.

(** ** Homomorphisms of right comodules *)
(******************************************************************************)
Section RightComoduleHomomorphism.

  Context
    (W F G : Type -> Type)
    `{Comonad W}
    `{Map F}
    `{Map G}
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
  {| rcom_map_extr_coaction := com_map_extr_cojoin W;
     rcom_coaction_coaction := com_cojoin_cojoin W;
  |}.

End RightComodule_Comonad.
