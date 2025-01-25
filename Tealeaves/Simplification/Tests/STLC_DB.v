From Tealeaves Require Export
  Examples.STLC.Syntax
  Backends.DB.

Import STLC.Syntax.TermNotations.
Import DB.Simplification.
Import DB.AutosubstShim.Notations.

(** * Simplification Tests for the De Bruijn Backend *)
(**********************************************************************)

(** ** Rewriting Lemmas for <<rename>> *)
(**********************************************************************)
Section rename.

  Context (ρ: nat -> nat).

  Theorem term_rename1: forall n,
      rename ρ (tvar n: Lam nat) = tvar (ρ n).
  Proof.
    intros.
    simplify_rename.
    conclude.
  Qed.

  Theorem term_rename2: forall (t1 t2: Lam nat) (n: nat),
      rename ρ (app t1 t2: Lam nat) = app (rename ρ t1) (rename ρ t2).
  Proof.
    intros.
    simplify_rename.
    conclude.
  Qed.

  Theorem term_rename3: forall (τ: typ) (t: Lam nat),
      rename ρ (lam τ t: Lam nat) = lam τ (rename (up__ren ρ) t).
  Proof.
    intros.
    simplify_rename.
    conclude.
  Qed.

End rename.

Section subst.

  Context (σ: nat -> Lam nat).

  Theorem term_subst1: forall n,
      subst σ (tvar n: Lam nat) = σ n.
  Proof.
    intros.
    simplify_subst.
    conclude.
  Qed.

  Theorem term_subst2: forall (t1 t2: Lam nat),
      subst σ (app t1 t2: Lam nat) = app (subst σ t1) (subst σ t2).
  Proof.
    intros.
    simplify_subst.
    conclude.
  Qed.

  Theorem term_subst3: forall (τ: typ) (t: Lam nat),
      subst σ (lam τ t: Lam nat) = lam τ (subst (up__sub σ) t).
  Proof.
    intros.
    simplify_subst.
    conclude.
  Qed.

End subst.

(** ** Rewriting Lemmas for <<subst>> *)
(**********************************************************************)
Section subst.

  Context (σ: nat -> Lam nat).

  Goal subst ret = id.
  Proof.
    simplify_db.
    conclude.
  Qed.

  Goal forall t, subst ret t = t.
  Proof.
    intros.
    simplify_db.
    conclude.
  Qed.

  Goal forall (t1 t2: Lam nat),
      subst σ (app t1 t2) =
        app (subst σ t1) (subst σ t2).
  Proof.
    intros.
    simplify_db.
    conclude.
  Qed.

  Goal forall (τ: typ) (t: Lam nat),
      subst σ (lam τ t: Lam nat) = lam τ (subst (up__sub σ) t).
  Proof.
    intros.
    simplify_db_like_autosubst.
    conclude.
  Qed.

End subst.
