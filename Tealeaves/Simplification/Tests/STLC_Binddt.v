From Tealeaves Require Export
  Examples.STLC.Syntax
  Simplification.Tests.Support.

Import STLC.Syntax.TermNotations.

Ltac simplify_extract :=
  first [ change ((?f ∘ extract) (?dec, ?var)) with (f var)
        | change ((?g ∘ (?f ∘ extract)) (?dev, ?var)) with ((g ∘ f) var)
    ].

Ltac simplify_map_ret :=
  change ((map ret ∘ ?f) ?leaf) with (map ret (f leaf));
  rewrite map_to_ap.

Ltac simplify_ret :=
  change ((ret ∘ ?f) ?leaf) with (ret (f leaf)).

Ltac simplify_leaf :=
  try simplify_extract;
  try simplify_map_ret;
  try simplify_ret;
  unfold_all_transparent_tcs.

(** * Simplification tests for categorical operations *)
(******************************************************************************)
Section test.

  Context (G: Type -> Type) `{Mult G} `{Map G} `{Pure G}
    `{Applicative G} (v1 v2: Type).

  Implicit Types (t body: Lam v1) (v: v1) (τ: typ).
  Generalizable Variables t v τ body.

  (** ** <<binddt>> and <<ret>> *)
  (******************************************************************************)
  Section binddt_ret.

    (* Interestingly, these goals won't be accepted even if we add
       Generalizable Variable f.
       Implicit Type (f: nat * v1 -> G (Lam v2)).
       I think because binddt is typechecked
       before the universal generalization of f
       affects anything *)
    Context (f: nat * v1 -> G (Lam v2)).

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

  End binddt_ret.

  (** ** Binddt *)
  (******************************************************************************)
  Section binddt.

    Context (f: nat * v1 -> G (Lam v2)).

    Ltac test := intros; assert_different; simplify_binddt; conclude.
    Ltac test_fail := intros; simplify_binddt; reject.

    Lemma lam_binddt_1:
      `(binddt f (ret v) = f (0, v)).
    Proof.
      intros.
      simplify_binddt.
      change 0 with (Ƶ: nat).
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

    Lemma lam_bindd_1:
      `(bindd f (ret v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Lemma lam_bindd_1':
      `(bindd f (tvar v) = f (Ƶ, v)).
    Proof.
      intros.
      simplify_bindd.
      conclude.
    Qed.

    Lemma lam_bindd_2:
      `(bindd f (app t1 t2) = app (bindd f t1) (bindd f t2)).
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

  (** ** Bind *)
  (******************************************************************************)
  Section bind.

    Context (f: v1 -> Lam v2).

    Lemma lam_bind_1:
      `(bind f (ret v) = f v).
    Proof.
      intros.
      simplify_bind.
    Abort.

    Lemma lam_bind_1':
      `(bind f (tvar v) = f v).
    Proof.
      intros.
      simplify_bind.
      conclude.
    Qed.

    Lemma lam_bind_2:
      `(bind f (app t1 t2) = app (bind f t1) (bind f t2)).
    Proof.
      intros.
      simplify_bind.
      conclude.
    Qed.

    Lemma lam_bind_3:
      `(bind f (lam τ body) = lam τ (bind f body)).
    Proof.
      intros.
      simplify_bind.
      conclude.
    Qed.

  End bind.

  (** ** Mapdt *)
  (******************************************************************************)
  Section mapdt.

    Context (f: nat * v1 -> G v2).

    Lemma lam_mapdt_1:
      `(mapdt f (ret v) = pure ret <⋆> (f (0, v))).
    Proof.
      intros.
      progress simplify_mapdt.
      progress simplify_leaf.
      conclude.
    Qed.

    Lemma lam_mapdt_2:
      `(mapdt f (app t1 t2) = pure (app (V:=v2)) <⋆> mapdt f t1 <⋆> mapdt f t2).
    Proof.
      intros.
      progress simplify_mapdt.
      conclude.
    Qed.

    Lemma lam_mapdt_3:
      `(mapdt f (lam τ body) = pure (lam τ) <⋆> mapdt (f ⦿ 1) body).
    Proof.
      intros.
      progress simplify_mapdt.
      conclude.
    Qed.

  End mapdt.

  (** ** Mapd *)
  (******************************************************************************)
  Section mapd.

    Context (f: nat * v1 -> v2).

    Lemma lam_mapd_1:
      `(mapd f (ret (T := Lam) v) = ret (f (0, v))).
    Proof.
      intros.
      progress simplify_mapd.
      progress simplify_leaf.
      conclude.
    Qed.

    Lemma lam_mapd_2:
      `(mapd f (app t1 t2) = app (V:=v2) (mapd f t1) (mapd f t2)).
    Proof.
      intros.
      progress simplify_mapd.
      conclude.
    Qed.

    Lemma lam_mapd_3:
      `(mapd f (lam τ body) = lam τ (mapd (f ⦿ 1) body)).
    Proof.
      intros.
      progress simplify_mapd.
      conclude.
    Qed.

  End mapd.

  (** ** Map *)
  (******************************************************************************)
  Section map.

    Context (f: v1 -> v2).

    Lemma lam_map_1:
      `(map f (ret (T := Lam) v) = ret (f v)).
    Proof.
      intros.
      progress simplify_map.
      simplify_leaf.
      reflexivity.
    Qed.

    Lemma lam_map_1':
      `(map f (tvar v) = tvar (f v)).
    Proof.
      intros.
      progress simplify_map.
      reflexivity.
    Qed.

    Lemma lam_map_2:
      `(map f (app t1 t2) = app (map f t1) (map f t2)).
    Proof.
      intros.
      simplify_map.
      conclude.
    Qed.

    Lemma lam_map_3:
      `(map f (lam τ body) = lam τ (map f body)).
    Proof.
      intros.
      simplify_map.
      conclude.
    Qed.

  End map.

End test.
