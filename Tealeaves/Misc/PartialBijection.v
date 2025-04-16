From Tealeaves Require Import
  Functors.Option.

#[local] Generalizable Variables A B f g.

(** * Partial Bijections *)
(**********************************************************************)
Class PartialBijection {A B: Type}
  (f: A -> option B)
  (g: B -> option A) :=
  { pb_fwd: forall (a: A) (b: B),
      f a = Some b -> g b = Some a;
    pb_bwd: forall (b: B) (a: A),
      g b = Some a -> f a = Some b;

  }.

Lemma pb_iff `{PartialBijection A B f g}:
  forall (a: A) (b: B),
    f a = Some b <-> g b = Some a.
Proof.
  intros. split.
  apply pb_fwd.
  apply pb_bwd.
Qed.

Lemma pb_fwd_None `{PartialBijection A B f g}:
  forall (a: A),
    f a = None -> forall b, g b = Some a -> False.
Proof.
  introv H1 H2.
  apply pb_bwd in H2.
  congruence.
Qed.


Lemma pb_bwd_None `{PartialBijection A B f g}:
  forall (b: B),
    g b = None -> forall a, f a = Some b -> False.
Proof.
  introv H1 H2.
  apply pb_fwd in H2.
  congruence.
Qed.


Lemma pb_iff_None `{PartialBijection A B f g}:
  forall (a: A),
    f a = None <-> forall (b: B), ~ (g b = Some a).
Proof.
  intros. remember (f a) as fa.
  symmetry in Heqfa.
  destruct fa.
  - apply pb_fwd in Heqfa.
    split.
    inversion 1.
    intros contra.
    specialize (contra b Heqfa).
    contradiction.
  - specialize (pb_fwd_None a Heqfa).
    split; auto.
Qed.


(** ** Characterizing Partial Bijections *)
(**********************************************************************)
Theorem partial_bijection_spec1:
  forall (A B: Type) (f: A -> option B) (g: B -> option A),
    (forall (a: A), f a = None \/ map g (f a) = Some (Some a)) ->
    (forall (b: B), g b = None \/ map f (g b) = Some (Some b)) ->
    (forall (a: A) (b: B), f a = Some b <-> g b = Some a).
Proof.
  introv HA HB.
  intros a b.
  split.
  - intros Hf.
    specialize (HA a).
    rewrite Hf in HA.
    cbn in HA.
    inversion HA.
    + inversion H.
    + inversion H.
      reflexivity.
  - intros Hg.
    specialize (HB b).
    rewrite Hg in HB.
    cbn in HB.
    inversion HB.
    + inversion H.
    + inversion H.
      reflexivity.
Qed.

Theorem partial_bijection_spec2:
  forall (A B: Type) (f: A -> option B) (g: B -> option A),
    (forall (a: A) (b: B), f a = Some b <-> g b = Some a) ->
    (forall (a: A), f a = None \/ map g (f a) = Some (Some a)).
Proof.
  introv H. intro a.
  specialize (H a).
  destruct (f a) as [b|].
  - right.
    destruct (H b) as [H1 _].
    specialize (H1 ltac:(reflexivity)).
    cbn. fequal.
    assumption.
  - now left.
Qed.

Theorem partial_bijection_spec3:
  forall (A B: Type) (f: A -> option B) (g: B -> option A),
    (forall (a: A) (b: B), f a = Some b <-> g b = Some a) ->
    (forall (b: B), g b = None \/ map f (g b) = Some (Some b)).
Proof.
  introv H. intro b.
  remember (g b) as gb.
  destruct gb as [a|].
  - right.
    cbn.
    fequal.
    apply H.
    symmetry.
    assumption.
  - now left.
Qed.

(** ** Specification *)
(**********************************************************************)
Theorem partial_bijection_spec:
  forall (A B: Type) (f: A -> option B) (g: B -> option A),
    (forall (a: A) (b: B), f a = Some b <-> g b = Some a) <->
      (forall (b: B), g b = None \/ map f (g b) = Some (Some b)) /\
        (forall (a: A), f a = None \/ map g (f a) = Some (Some a)).
Proof.
  intros. split.
  - intros. split.
    now apply partial_bijection_spec2.
    now apply partial_bijection_spec3.
  - intros [H1 H2].
    apply partial_bijection_spec1.
    assumption.
    assumption.
Qed.

(** * Partial Bijections with Domain Specifications *)
(**********************************************************************)
Class PartialBijectionSpec
  (A B: Type)
  (P: A -> Prop) (Q: B -> Prop)
  (f: A -> option B)
  (g: B -> option A) :=
  { pb_spec_iff: forall (a: A) (b: B),
      f a = Some b <-> g b = Some a;
    pb_P: forall (a: A), f a = None <-> ~ (P a);
    pb_Q: forall (b: B), g b = None <-> ~ (Q b);
  }.
