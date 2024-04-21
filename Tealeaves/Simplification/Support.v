From Tealeaves Require Export
  Theory.DecoratedTraversableMonad
  Tactics.Debug.

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.

(*|
========================================
Extra lemmas for simplification support
========================================
|*)
Import Monoid.Notations.

Lemma pure_const_rw: forall {A} {a:A} {M} {unit:Monoid_unit M},
    pure (F := const M) (Pure := @Pure_const _ unit) a = Ƶ.
  reflexivity.
Qed.

Lemma ap_const_rw: forall {M} `{Monoid_op M} {A B} (x: const M (A -> B)) (y: const M A),
    ap (const M) x y = (x ● y).
  reflexivity.
Qed.

Lemma map_const_rw: forall A B (f: A -> B) X,
    map (F := const X) f = @id X.
Proof.
  reflexivity.
Qed.

Lemma eq_pair_preincr: forall (n: nat) {A} (a: A),
    eq (S n, a) ⦿ 1 = eq (n, a).
Proof.
  intros.
  ext [n' a'].
  unfold preincr, compose, incr.
  apply propositional_extensionality.
  rewrite pair_equal_spec.
  rewrite pair_equal_spec.
  intuition.
Qed.

Section section.

  Context {E : Type} {T : Type -> Type} `{Mapdt E T}.

  Lemma Forall_ctx_to_foldMapd :
    forall {A t} (f: E * A -> Prop),
      Forall_ctx f t = foldMapd f t.
  Proof.
    reflexivity.
  Qed.
  Lemma foldMapd_to_Forall_ctx :
    forall {A t} (f: E * A -> Prop),
      foldMapd f t = Forall_ctx f t.
  Proof.
    reflexivity.
  Qed.

  Lemma exists_false_false
    `{DecoratedTraversableFunctor E T}:
    forall {A} (t: T A),
      foldMapd (op := Monoid_op_or) (unit := Monoid_unit_false)
        (const False) t = False.
  Proof.
    intros.
    rewrite foldMapd_through_toctxlist.
    unfold compose. induction (toctxlist t).
    - reflexivity.
    - cbn. rewrite IHe. do 2 unfold transparent tcs. propext;
                        intuition.
  Qed.

End section.

Lemma binddt_ret:
  forall {W : Type} {T G : Type -> Type}
    `{DecoratedTraversableMonad W T}
    `{Applicative G},
      forall (A B : Type) (f : W * A -> G (T B)) (a: A),
        binddt f (ret a) = f (Ƶ, a).
Proof.
  intros.
  compose near a.
  rewrite kdtm_binddt0.
  reflexivity.
Qed.

(** * Basic rewriting lemmas *)
(******************************************************************************)
Module Basics.

  Ltac rewrite_with_any :=
    match goal with
    | [H : _ = _ |- _] => rewrite H
    | [H : forall _, _ |- _] => progress rewrite H by now trivial
    end.

  Ltac normalize_fns :=
    ltac_trace "normalize_fns";
    match goal with
    | |- context[?f ∘ id] =>
        change (f ∘ id) with f
    | |- context[(id ∘ ?f)] =>
        change (id ∘ f) with f
    end.

  Ltac normalize_fns_in H :=
    match goal with
    | H: context[?f ∘ id] |- _ =>
        change (f ∘ id) with f in H
    | H: context[(id ∘ ?f)] |- _ =>
        change (id ∘ f) with f in H
    end.

  Ltac normalize_id :=
    ltac_trace "normalize_id";
    match goal with
    | |- context[id ?t] =>
        change (id t) with t
    end.

  Ltac normalize_id_in :=
    match goal with
    | H: context[id ?t] |- _ =>
        change (id t) with t in H
    end.

  Ltac simplify_monoid_units :=
    ltac_trace "simplify_monoid_units";
    match goal with
    | |- context[Ƶ ● ?m] =>
        rewrite (monoid_id_r m)
    | |- context[?m ● Ƶ] =>
        rewrite (monoid_id_l m)
    end.

  Ltac simplify_monoid_units_in H :=
    match goal with
    | H: context[Ƶ ● ?m] |- _ =>
        rewrite (monoid_id_r m) in H
    | H: context[?m ● Ƶ] |- _ =>
        rewrite (monoid_id_l m) in H
    end.

  Ltac simplify_preincr_zero :=
    ltac_trace "simplify_preincr_zero";
    match goal with
    | |- context[(?f ⦿ Ƶ)] =>
        rewrite (preincr_zero f)
    | |- context[(?f ⦿ ?x)] =>
        (* test whether x can be resolved as some Ƶ *)
        let T := type of x in
        change x with (Ƶ:T);
        rewrite preincr_zero
    end.

End Basics.

(** * Simplifying applicative functors *)
(******************************************************************************)
Module SimplApplicative.

  Ltac find_functor_instance G :=
    match goal with
    | H: Functor G |- _ => idtac
    | |- _ => fail
    end.

  Ltac find_applicative_instance G :=
    match goal with
    | H: Applicative G |- _ => idtac
    | |- _ => fail
    end.

  Ltac infer_applicative_functors :=
    repeat match goal with
      | H: Applicative ?G |- _ =>
          (* See coq refman 8.20 Note about assert_fails *)
          assert_fails (idtac; find_functor_instance G);
          assert (Functor G) by (now inversion H)
      | H: ApplicativeMorphism ?G1 ?G2 ?ϕ |- _ =>
          (assert_fails (idtac; find_applicative_instance G1);
           assert (Applicative G1) by now inversion H)
          || (assert_fails (idtac; find_applicative_instance G2);
             assert (Applicative G2) by now inversion H)
      end.

  (** ** Constant applicatives *)
  (******************************************************************************)
  Ltac simplify_applicative_const :=
    ltac_trace "simplify_applicative_const";
    match goal with
    | |- context [pure (F := const ?W) ?x] =>
        rewrite pure_const_rw
    | |- context[(ap (const ?W) ?x ?y)] =>
        rewrite ap_const_rw
    end.

  Ltac simplify_applicative_const_in :=
    match goal with
    | H: context [pure (F := const ?W) ?x] |- _ =>
        rewrite pure_const_rw in H
    | H: context[(ap (const ?W) ?x ?y)] |- _ =>
        rewrite ap_const_rw in H
    end.

  (** ** Constant maps *)
  (******************************************************************************)
  Ltac simplify_map_const :=
    ltac_trace "simplify_map_const";
    match goal with
    | |- context[map (F := const ?X) ?f] =>
        rewrite map_const_rw
    end.

  Ltac simplify_map_const_in :=
    match goal with
    | H: context[map (F := const ?X) ?f] |- _ =>
        rewrite map_const_rw in H
    end.

  (** ** Identity applicative *)
  (******************************************************************************)
  Ltac simplify_applicative_I :=
    ltac_trace "simplify_applicative_I";
    match goal with
    | |- context[pure (F := fun A => A) ?x] =>
        change (pure (F := fun A => A) x) with x
    | |- context[ap (fun A => A) ?x ?y] =>
        change (ap (fun A => A) x y) with (x y)
    end.

  Ltac simplify_applicative_I_in :=
    match goal with
    | H: context[pure (F := fun A => A) ?x] |- _ =>
        change (pure (F := fun A => A) x) with x
    | H: context[ap (fun A => A) ?x ?y] |- _ =>
        change (ap (fun A => A) x y) with (x y)
    end.

  (** ** Identity maps *)
  (******************************************************************************)
  Ltac simplify_map_I :=
    ltac_trace "simplify_map_I";
    match goal with
    | |- context[map (F := fun A => A) ?f] =>
        unfold_ops @Map_I
    end.

  Ltac simplify_map_I_in :=
    match goal with
    | H: context[map (F := fun A => A) ?f] |- _ =>
        unfold map in H;
        unfold Map_I in H
    end.

End SimplApplicative.

Export Basics.
Export SimplApplicative.
