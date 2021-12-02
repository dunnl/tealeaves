From Tealeaves Require Export
     Singlesorted.Classes.Functor.

Import Functor.Notations.
#[local] Open Scope tealeaves_scope.

(** * Comonads *)
(******************************************************************************)
Section Comonad_operations.

  Context
    (W : Type -> Type).

  Class Cojoin :=
    cojoin : W ⇒ W ∘ W.

  Class Extract :=
    extract : W ⇒ (fun A => A).

End Comonad_operations.

Section Comonad.

  Context
    `(W : Type -> Type)
    `{Fmap W}
    `{Cojoin W}
    `{Extract W}.

  Class Comonad :=
    { com_functor :> Functor W;
      com_extract_natural :> Natural (extract W);
      com_cojoin_natural :> Natural (cojoin W);
      com_extract_cojoin :
          `(extract W (W A) ∘ cojoin W A = @id (W A));
      com_fmap_extr_cojoin :
          `(fmap W (extract W A) ∘ cojoin W A = @id (W A));
      com_cojoin_cojoin :
        `(cojoin W (W A) ∘ cojoin W A = fmap W (cojoin W A) ∘ (cojoin W A));
    }.

End Comonad.

Arguments cojoin _%function_scope {Cojoin} {A}%type_scope.
Arguments extract _%function_scope {Extract} {A}%type_scope.

(** * Kleisli presentation of comonads *)
(******************************************************************************)

(** ** Lifting operation <<cobind>> *)
(******************************************************************************)
Class Cobind W := cobind : forall {A B : Type} (f : W A -> B), W A -> W B.

Arguments cobind W%function_scope {Cobind} {A B}%type_scope _%function_scope.

Instance Cobind_Cojoin `{Fmap W} `{Cojoin W} : @Cobind W :=
  fun {A B} {f : W A -> B} => fmap W f ∘ cojoin W.

Definition cokcompose `{Cojoin W} `{Fmap W} {A B C}
           (g : W B -> C) (f : W A -> B) : W A -> C := g ∘ cobind W f.

#[local] Notation "g 'co⋆' f" := (cokcompose g f) (at level 60) : tealeaves_scope.

(** ** Specification for <<fmap>> *)
(******************************************************************************)
Section comonad_kleisli_suboperations.

  Context
    (W : Type -> Type)
    `{Comonad W}.

  (** *** [fmap] as a special case of [cobind]. *)
  Corollary fmap_to_cobind : forall `(f : A -> B),
      fmap W f = cobind W (f ∘ extract W).
  Proof.
    introv. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap W).
    reassociate -> on right.
    now rewrite (com_fmap_extr_cojoin W).
  Qed.

End comonad_kleisli_suboperations.

(** ** Functor laws for <<cobind>> *)
(******************************************************************************)
Section comodule_cobind.

  Context
    (W : Type -> Type)
    `{Comonad W}.

  (** *** [cobind] functor laws *)
  Theorem cobind_id :
    `(cobind W (extract W) = @id (W A)).
  Proof.
    intros. unfold transparent tcs.
    now rewrite (com_fmap_extr_cojoin W).
  Qed.

  Theorem cobind_cobind : forall `(g : W B -> C) `(f : W A -> B),
      cobind W g ∘ cobind W f = cobind W (g co⋆ f).
  Proof.
    introv. unfold transparent tcs. unfold cokcompose.
    reassociate <- on left.
    reassociate -> near (fmap W f).
    rewrite <- natural.
    reassociate <- on left.
    unfold transparent tcs.
    reassociate -> on left.
    rewrite (com_cojoin_cojoin W).
    now rewrite <- 2(fun_fmap_fmap W).
  Qed.

  Theorem extract_cobind : forall `(f : W A -> B),
      extract W ∘ cobind W f = f.
  Proof.
    introv. unfold transparent tcs.
    reassociate <- on left. rewrite <- (natural (F := W) (ϕ := @extract W _)).
    unfold_ops @Fmap_I.
    reassociate -> on left.
    now rewrite (com_extract_cojoin W).
  Qed.

End comodule_cobind.

(** ** Co-kleisli category laws *)
(******************************************************************************)
Section comonad_cokleisli_category.

  Context
    `{Comonad W}
    {A B C D : Type}.

  Theorem cokleisli_id_r : forall (g : W B -> C),
      g co⋆ (extract W) = g.
  Proof.
    intros. unfold cokcompose. now rewrite (cobind_id W).
  Qed.

  Theorem kleisli_id_l : forall (f : W A -> B),
      (extract W) co⋆ f = f.
  Proof.
    intros. unfold cokcompose. now rewrite (extract_cobind W).
  Qed.

  Theorem kleisli_comp : forall (h : W C -> D) (g : W B -> C) (f : W A -> B),
      h co⋆ (g co⋆ f) = (h co⋆ g) co⋆ f.
  Proof.
    intros. unfold cokcompose at 1.
    now rewrite <- (cobind_cobind W).
  Qed.

End comonad_cokleisli_category.

(** ** Composition laws for <<cobind>>/<<fmap>>*)
(******************************************************************************)
Section comodule_cobind.

  Context
    (W : Type -> Type)
    `{Comonad W}.

  Corollary fmap_cobind : forall `(f : W A -> B) `(g : B -> C),
      fmap W g ∘ cobind W f = cobind W (g ∘ f).
  Proof.
    introv. unfold transparent tcs.
    now rewrite <- (fun_fmap_fmap W).
  Qed.

  Corollary cobind_fmap : forall `(f : A -> B) `(g : W B -> C),
      cobind W g ∘ fmap W f = cobind W (g ∘ fmap W f).
  Proof.
    introv. unfold transparent tcs.
    rewrite <- (fun_fmap_fmap W).
    reassociate -> on left.
    now rewrite <- (natural (ϕ := @cojoin W _) f).
  Qed.

End comodule_cobind.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "g 'co⋆' f" := (cokcompose g f) (at level 60) : tealeaves_scope.
  Notation "'coμ'" := (cojoin) : tealeaves_scope.
  (*Notation "'coη'" := (extract) : tealeaves_scope.*)
End Notations.
