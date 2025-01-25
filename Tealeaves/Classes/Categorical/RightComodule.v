From Tealeaves Require Export
  Classes.Categorical.Comonad.

Import Functor.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables W A.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments extract W%function_scope {Extract} (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin} {A}%type_scope _.

(** * Right Comodules *)
(**********************************************************************)
Class RightCoaction (F W: Type -> Type) := right_coaction: F ⇒ F ∘ W.

#[local] Arguments right_coaction (F W)%function_scope {RightCoaction}
  A%type_scope _.

Class RightComodule
  (F W: Type -> Type)
  `{Map W} `{Cojoin W} `{Extract W}
  `{Map F} `{RightCoaction F W} :=
  { rcom_comonad :> Comonad W;
    rcom_functor :> Functor F;
    rcom_coaction_natural :> Natural (@right_coaction F W _);
    rcom_map_extr_coaction:
    `(map F (extract W A) ∘ right_coaction F W A = @id (F A));
    rcom_coaction_coaction:
    `(right_coaction F W (W A) ∘ right_coaction F W A =
        map F (cojoin W) ∘ right_coaction F W A);
  }.

#[global] Arguments right_coaction F {W}%function_scope
  {RightCoaction} {A}%type_scope.

(** ** Homomorphisms of Right Comodules *)
(**********************************************************************)
Class RightComoduleHom
  (W F G: Type -> Type)
  `{Comonad W}
  `{Map F}
  `{Map G}
  `{RightCoaction F W}
  `{RightCoaction G W}
  `{! RightComodule F W}
  `{! RightComodule G W}
  (ϕ: forall {A}, F A -> G A) :=
  { rcomh_natural:
    `{Natural (F := F) (G := G) (fun A => ϕ)};
    rcomh_morphism: forall A (x: F A),
      ϕ (right_coaction F x) = right_coaction G (ϕ x);
  }.

(** ** Comonads Form Right Comodules *)
(**********************************************************************)
Section RightComodule_Comonad.

  Instance RightCoaction_Cojoin `{Cojoin W}:
    RightCoaction W W := @cojoin W _.

  #[program] Instance RightComodule_Comonad `{Comonad W}:
    RightComodule W W :=
  {| rcom_map_extr_coaction := com_map_extr_cojoin;
     rcom_coaction_coaction := com_cojoin_cojoin;
  |}.

End RightComodule_Comonad.
