From Tealeaves Require Export
  Examples.STLC.Syntax
  Simplification.Tests.Support.

Import STLC.Syntax.TermNotations.

(** * Simplification tests for categorical operations *)
(******************************************************************************)
Section test.

  Context (G: Type -> Type) `{Mult G} `{Map G} `{Pure G}
    `{Applicative G} (v1 v2: Type).

  Implicit Types (t body: Lam v1) (v: v1) (τ: typ).
  Generalizable Variables t v τ body.

  (** ** Binddt *)
  (******************************************************************************)
  Section binddt.

    (* Interestingly, these goals won't be accepted even if we add
       Generalizable Variable f.
       Implicit Type (f: nat * v1 -> G (Lam v2)).
       I think because binddt is typechecked
       before the universal generalization of f
       affects anything *)
    Context (f: nat * v1 -> G (Lam v2)).

    Ltac test := intros; assert_different; simplify_binddt; conclude.
    Ltac test_fail := intros; simplify_binddt; reject.

    Goal `(binddt f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      assert_different.
      simplify_match_binddt_ret.
      conclude.
    Qed.

    Goal `(binddt f (ret v) = f (0, v)).
    Proof.
      intros.
      simplify_match_binddt_ret.
      reject.
    Qed.

    Goal `(binddt f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_binddt_core.
      reject.
    Qed.

    Goal `(binddt f (ret v) = f (0, v)).
    Proof.
      intros.
      simplify_binddt_core.
      conclude.
    Qed.

    Goal `(binddt f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_binddt.
      conclude.
    Qed.

    Goal `(binddt f (ret v) = f (0, v)).
    Proof.
      intros.
      simplify_binddt.
      reject.
    Qed.

    Goal `(binddt f (ret v) = binddt f (tvar v)).
    Proof.
      intros.
      assert_different.
      normalize_all_binddt_ret.
      conclude.
    Qed.

    Lemma lam_binddt_11:
      `(binddt f (ret v) = f (0, v)).
    Proof.
      try test.
      intros. cbn_binddt.
      conclude.
    Qed.

    Lemma lam_binddt_2:
      `(binddt f (app t1 t2) = pure (app (V:=v2)) <⋆> binddt f t1 <⋆> binddt f t2).
    Proof.
      test.
    Qed.

    Lemma lam_binddt_3:
      `(binddt f (lam τ body) = pure (lam τ) <⋆> binddt (f ⦿ 1) body).
    Proof.
      test.
    Qed.

  End binddt.

  (** ** Bindd *)
  (******************************************************************************)
  Section bindd.

    Context (f: nat * v1 -> Lam v2).

    Goal `(bindd f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Goal `(bindd f (tvar v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Goal `(bindd f (ret v) = bindd f (tvar v)).
    Proof.
      dup. {
        intros.
        rewrite bindd_to_binddt.
        simplify_binddt.
        simplify_binddt.
        conclude.
      }
      intros.
      simplify_bindd.
      simplify_bindd.
      conclude.
    Qed.

    Lemma lam_bindd_11:
      `(bindd f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Lemma lam_bindd_2:
      `(bindd f (app t1 t2) = app (V:=v2) (bindd f t1) (bindd f t2)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Lemma lam_bindd_3:
      `(bindd f (lam τ body) = lam τ (bindd (f ⦿ 1) body)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

  End bindd.

End test.
