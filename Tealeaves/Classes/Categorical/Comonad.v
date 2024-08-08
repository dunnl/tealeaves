From Tealeaves Require Export
  Classes.Functor
  Classes.Kleisli.Comonad (Extract, extract)
  Functors.Identity
  Functors.Compose.

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

(** * Comonads *)
(******************************************************************************)
Class Cojoin (W : Type -> Type) :=
  cojoin : W ⇒ W ∘ W.

#[global] Arguments cojoin {W}%function_scope {Cojoin} {A}%type_scope.

Class Comonad (W : Type -> Type)
  `{Map W} `{Cojoin W} `{Extract W} :=
  { com_functor :> Functor W;
    com_extract_natural :> Natural (@extract W _);
    com_cojoin_natural :> Natural (@cojoin W _);
    com_extract_cojoin :
    `(extract (A := W A) ∘ cojoin (A := A) = @id (W A));
    com_map_extr_cojoin :
    `(map (F := W) (extract (A := A)) ∘ cojoin (A := A) = @id (W A));
    com_cojoin_cojoin :
    `(cojoin (A := W A) ∘ cojoin (A := A) =
        map (F := W) (cojoin (A := A)) ∘ cojoin (A := A));
  }.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'coμ'" := cojoin : tealeaves_scope.
End Notations.

(** * Comonad to Kleisli comonad *)
(******************************************************************************)
Module ToKleisli.

  Import Tealeaves.Classes.Kleisli.Comonad.
  Import Kleisli.Comonad.Notations.

  #[local] Generalizable All Variables.

  #[export] Instance Cobind_Cojoin (W : Type -> Type)
    `{Map W} `{Cojoin W} : Cobind W :=
    fun {A B} (f : W A -> B) => map (F := W) f ∘ cojoin.

  Section with_monad.

    Context
      `{Comonad.Comonad W}.

    #[local] Arguments cobind W%function_scope {Cobind} (A B)%type_scope _%function_scope _.

    (** ** Identity law *)
    (******************************************************************************)
    Lemma kcom_bind_id :
      `(@cobind W _ A A (@extract W _ A) = @id (W A)).
    Proof.
      intros. unfold_ops @Cobind_Cojoin.
      now rewrite com_map_extr_cojoin.
    Qed.

    (** ** Composition law *)
    (******************************************************************************)
    Lemma kcom_bind_bind : forall (A B C : Type) (g : W B -> C) (f : W A -> B),
        cobind W B C g ∘ cobind W A B f = cobind W A C (g ⋆4 f).
    Proof.
      introv. unfold transparent tcs.
      unfold kc4.
      unfold_ops @Cobind_Cojoin.
      reassociate <- on left.
      reassociate -> near (map f).
      rewrite <- (natural (ϕ := @cojoin W _)).
      unfold_ops @Map_compose.
      reassociate -> on left.
      reassociate -> on left.
      rewrite (com_cojoin_cojoin (W := W)).
      do 2 reassociate <- on left.
      unfold_compose_in_compose.
      do 2 rewrite fun_map_map.
      reflexivity.
    Qed.

    (** ** Unit law *)
    (******************************************************************************)
    Lemma kcom_bind_comp_ret : forall (A B : Type) (f : W A -> B),
        extract ∘ cobind W A B f = f.
    Proof.
      intros. unfold transparent tcs.
      reassociate <- on left.
      rewrite <- (natural (ϕ := @extract W _)).
      reassociate -> on left.
      rewrite com_extract_cojoin.
      reflexivity.
    Qed.

    #[export] Instance Kleisli_Comonad : Kleisli.Comonad.Comonad W :=
      {| kcom_cobind0 := @kcom_bind_comp_ret;
        kcom_cobind1 := @kcom_bind_id;
        kcom_cobind2 := @kcom_bind_bind;
      |}.

  End with_monad.

End ToKleisli.
