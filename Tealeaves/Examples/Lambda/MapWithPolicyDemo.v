From Tealeaves Require Import
  Examples.Lambda.Confluence
  Classes.Monoid
  Simplification.Binddt.

Import Monoid.Notations.
Import DecoratedTraversableMonad.UsefulInstances.

Fixpoint mwp {A B: Type} (P: (A -> B) -> (A -> B)) (f: A -> B) (t: lam A): lam B :=
  match t with
  | tvar a    => tvar (f a)
  | abs body  => abs (mwp P (P f) body)
  | app t1 t2 => app (mwp P f t1) (mwp P f t2)
  end.

Fixpoint bwp {A B: Type} (P: (A -> lam B) -> (A -> lam B)) (f: A -> lam B) (t: lam A): lam B :=
  match t with
  | tvar a    => f a
  | abs body  => abs (bwp P (P f) body)
  | app t1 t2 => app (bwp P f t1) (bwp P f t2)
  end.

Lemma mwp_equiv: forall A B (f: nat * A -> B) (t: lam A),
    mapd f t = mwp (fun f => f ⦿ 1) f (mwp id (fun a => (0, a)) t).
Proof.
  intros.
  generalize dependent f.
  induction t; intro f.
  - reflexivity.
  - simplify_mapd.
    cbn. fequal.
    rewrite IHt.
    reflexivity.
  - simplify_mapd.
    cbn. fequal; auto.
Qed.

Lemma bwp_equiv: forall A B (f: nat * A -> lam B) (t: lam A),
    bindd f t = bwp (fun f => f ⦿ 1) f (bwp id (fun a => ret (0, a)) t).
Proof.
  intros.
  generalize dependent f.
  induction t; intro f.
  - reflexivity.
  - simplify_bindd.
    cbn. fequal.
    rewrite IHt.
    reflexivity.
  - simplify_bindd.
    cbn. fequal; auto.
Qed.

