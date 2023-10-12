From Tealeaves Require Export
  Classes.Functor
  Classes.Kleisli.Comonad (Extract, extract)
  Functors.Identity
  Functors.Compose.

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

(** * Comonads *)
(******************************************************************************)
Section comonad.

  Context
    (W : Type -> Type).

  Class Cojoin :=
    cojoin : W ⇒ W ∘ W.

  Context
    `{Map W}
    `{Cojoin}
    `{Extract W}.

  Class Comonad :=
    { com_functor :> Functor W;
      com_extract_natural :> Natural (extract W);
      com_cojoin_natural :> Natural (cojoin);
      com_extract_cojoin :
      `(extract W (W A) ∘ cojoin A = @id (W A));
      com_map_extr_cojoin :
      `(map W (W A) A (extract W A) ∘ cojoin A = @id (W A));
      com_cojoin_cojoin :
      `(cojoin (W A) ∘ cojoin A = map W (W A) (W (W A)) (cojoin A) ∘ cojoin A);
    }.

End comonad.

Arguments cojoin _%function_scope {Cojoin} {A}%type_scope.
(*
Arguments extract _%function_scope {Extract} {A}%type_scope.
*)

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "'coμ'" := (cojoin) : tealeaves_scope.
  (*Notation "'coη'" := (extract) : tealeaves_scope.*)
End Notations.

(** * Comonad to Kleisli comonad *)
(******************************************************************************)
Module ToKleisli.

  Import Tealeaves.Classes.Kleisli.Comonad.
  Import Kleisli.Comonad.Notations.

  #[local] Generalizable All Variables.

  Section operation.

    Context
      (W : Type -> Type)
      `{Map W} `{Cojoin W}.

    #[export] Instance Cobind_Cojoin : Cobind W :=
      fun {A B} (f : W A -> B) => map W (W A) B f ∘ cojoin W.

  End operation.

  Section with_monad.

    Context
      (W : Type -> Type)
      `{Categorical.Comonad.Comonad W}.

    #[local] Arguments cobind W%function_scope {Cobind} (A B)%type_scope _%function_scope _.

    (** *** Identity law *)
    (******************************************************************************)
    Lemma kcom_bind_id :
      `(cobind W A A (extract W A) = @id (W A)).
    Proof.
      intros. unfold_ops @Cobind_Cojoin.
      now rewrite (com_map_extr_cojoin W).
    Qed.

    (** *** Composition law *)
    (******************************************************************************)
    Lemma kcom_bind_bind : forall (A B C : Type) (g : W B -> C) (f : W A -> B),
        cobind W B C g ∘ cobind W A B f = cobind W A C (g ⋆4 f).
    Proof.
      introv. unfold transparent tcs.
      unfold kc4.
      unfold_ops @Cobind_Cojoin.
      reassociate <- on left.
      reassociate -> near (map W (W A) B f).
      rewrite <- (natural (ϕ := @cojoin W _)).
      unfold_ops @Map_compose.
      reassociate -> on left.
      reassociate -> on left.
      rewrite (com_cojoin_cojoin W).
      do 2 reassociate <- on left.
      unfold_compose_in_compose.
      do 2 rewrite (fun_map_map).
      reflexivity.
    Qed.

    (** *** Unit law *)
    (******************************************************************************)
    Lemma kcom_bind_comp_ret : forall (A B : Type) (f : W A -> B),
        extract W B ∘ cobind W A B f = f.
    Proof.
      intros. unfold transparent tcs.
      reassociate <- on left.
      rewrite <- (natural (ϕ := extract W)).
      reassociate -> on left.
      rewrite (com_extract_cojoin W).
      reflexivity.
    Qed.

    #[export] Instance Kleisli_Comonad : Kleisli.Comonad.Comonad W :=
      {| kcom_cobind0 := @kcom_bind_comp_ret;
        kcom_cobind1 := @kcom_bind_id;
        kcom_cobind2 := @kcom_bind_bind;
      |}.

  End with_monad.

End ToKleisli.
