From Tealeaves.Backends Require Import
  DB.DB
  DB.Simplification.
From Autosubst Require
  Autosubst.

Import DecoratedTraversableMonad.UsefulInstances.

#[local] Generalizable Variables W T U.

Module Autosubst_Instances.
  Import Autosubst.

  Section DTM_to_Autosubst.
    Context
      `{DecoratedTraversableMonad
       (op := Monoid_op_plus) (unit := Monoid_unit_zero) nat T}.

    #[export] Instance Ids_DTM: Ids (T nat) :=
      @ret T _ nat.
    #[export] Instance Rename_DTM: Rename (T nat) :=
      @DB.rename T _.
    #[export] Instance Subst_DTM: Subst (T nat) :=
      @DB.subst T _ _ _ _.

    Lemma rename_subst_DTM:
      forall (xi: nat -> nat) (s: T nat), rename xi s = s.[ren xi].
    Proof.
      intros.
      unfold_ops @Rename_DTM @Subst_DTM.
      tealeaves_unfold.
      reflexivity.
    Qed.

    Lemma subst_id_DTM:
      forall s: T nat, s.[ids] = s.
    Proof.
      intros.
      unfold_ops @Ids_DTM @Subst_DTM.
      simplify_db.
      reflexivity.
    Qed.

    Lemma id_subst_DTM: forall (sigma: nat -> T nat) (x: nat),
        (ids x).[sigma] = sigma x.
    Proof.
      intros.
      unfold_ops @Ids_DTM @Subst_DTM.
      simplify_db.
      conclude.
    Qed.

    Lemma subst_comp_DTM:
      forall (sigma tau: nat -> T nat) (s: T nat),
        s.[sigma].[tau] = s.[scomp sigma tau].
    Proof.
      intros.
      unfold_ops @Subst_DTM.
      compose near s on left.
      rewrite subst_subst.
      reflexivity.
    Qed.

    #[export] Instance SubstLemmas_term: SubstLemmas (T nat) :=
      {| rename_subst := rename_subst_DTM;
        subst_id := subst_id_DTM;
        id_subst := id_subst_DTM;
        subst_comp := subst_comp_DTM;
      |}.

  End DTM_to_Autosubst.

  Lemma cons_eq {X:Type}:
    @DB.scons X = Autosubst_Basics.scons.
  Proof.
    reflexivity.
  Qed.

  Lemma upren_eq {X:Type}:
    up__ren = upren.
  Proof.
    reflexivity.
  Qed.

  Lemma up_eq `{Return T} `{Binddt nat T T} {X:Type}:
    up__sub (T := T) = up.
  Proof.
    ext σ ix.
    unfold up, up__sub.
    rewrite cons_eq.
    reflexivity.
  Qed.

End Autosubst_Instances.

(** * Autosubst-compatible notations *)
(******************************************************************************)
Module Notations.
  Notation "( + x )" := (lift x) (format "( + x )"): tealeaves_scope.
  Notation "f >>> g" :=
    (compose g f)
      (at level 56, left associativity): tealeaves_scope.
  Notation "s .: sigma" :=
    (scons s sigma)
      (at level 55, sigma at level 56, right associativity): tealeaves_scope.
  Notation "s .[ sigma ]" :=
    (subst sigma s)
      (at level 2, sigma at level 200, left associativity,
        format "s .[ sigma ]" ): tealeaves_scope.
  Notation "s .[ t /]" := (subst (t .: ret) s)
                            (at level 2, t at level 200, left associativity,
                              format "s .[ t /]"): tealeaves_scope.
  Notation "s .[ t1 , t2 , .. , tn /]" :=
    (subst (scons t1 (scons t2 .. (scons tn ret) .. )) s)
      (at level 2, left associativity,
        format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'"): tealeaves_scope.
End Notations.
