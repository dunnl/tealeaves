From Tealeaves Require Import
  Classes.Categorical.Comonad
  Classes.Kleisli.Comonad.

(** * Comonad to Kleisli comonad *)
(**********************************************************************)

(** ** Derived <<cobind>> Operation *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Cobind_Categorical (W: Type -> Type)
    `{Map W} `{Cojoin W}: Cobind W :=
  fun {A B} (f: W A -> B) => map (F := W) f ∘ cojoin.

End DerivedOperations.

Module DerivedInstances.
  (* Alectryon doesn't like this
     Import CategoricalToKleisli.Comonad.DerivedOperations.
   *)
  Import DerivedOperations.
  Import Tealeaves.Classes.Kleisli.Comonad.
  Import Kleisli.Comonad.Notations.

  #[local] Generalizable All Variables.
  #[local] Arguments cobind W%function_scope {Cobind}
    (A B)%type_scope _%function_scope _.


  (** ** <<cojoin>> as <<id ⋆1 id>> *)
  (********************************************************************)
  Lemma cojoin_to_kc `{Categorical.Comonad.Comonad W}: forall (A: Type),
      cojoin (W := W) (A := A) = id ⋆1 id.
  Proof.
    intros. unfold kc1, cobind, Cobind_Categorical.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  (** ** Derived co-Kleisli Laws *)
  (********************************************************************)
  Section with_monad.

    Context
      `{Categorical.Comonad.Comonad W}.

    (** *** Identity law *)
    (******************************************************************)
    Lemma kcom_bind_id:
      `(@cobind W _ A A (@extract W _ A) = @id (W A)).
    Proof.
      intros. unfold_ops @DerivedOperations.Cobind_Categorical.
      rewrite com_map_extr_cojoin.
      reflexivity.
    Qed.

    (** *** Composition law *)
    (******************************************************************)
    Lemma kcom_bind_bind:
      forall (A B C: Type) (g: W B -> C) (f: W A -> B),
        cobind W B C g ∘ cobind W A B f = cobind W A C (g ⋆1 f).
    Proof.
      introv. unfold transparent tcs.
      unfold kc1.
      unfold_ops @Cobind_Categorical.
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

    (** *** Unit law *)
    (******************************************************************)
    Lemma kcom_bind_comp_ret:
      forall (A B: Type) (f: W A -> B),
        extract ∘ cobind W A B f = f.
    Proof.
      intros. unfold transparent tcs.
      reassociate <- on left.
      rewrite <- (natural (ϕ := @extract W _)).
      reassociate -> on left.
      rewrite com_extract_cojoin.
      reflexivity.
    Qed.

    (** ** Typeclass Instance *)
    (******************************************************************)
    #[export] Instance KleisliComonad_CategoricalComonad:
      Kleisli.Comonad.Comonad W :=
      {| kcom_cobind0 := @kcom_bind_comp_ret;
         kcom_cobind1 := @kcom_bind_id;
         kcom_cobind2 := @kcom_bind_bind;
      |}.

  End with_monad.

End DerivedInstances.
