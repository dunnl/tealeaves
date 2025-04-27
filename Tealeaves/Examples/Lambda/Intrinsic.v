From Coq Require Import
  Relations.Relations
  Classes.RelationClasses.
From Tealeaves Require Import
  Backends.DB.




Import DecoratedTraversableMonad.UsefulInstances.

#[local] Set Implicit Arguments.

Import DB.Notations.

Open Scope nat_scope.
Open Scope nat_scope.

Definition incr {A}: (nat -> A) -> nat -> (nat -> A) :=
  fun f n m => f (n + m).

Inductive lam (V: nat -> Type) :=
| tvar: V 0 -> lam V
| abs: lam (incr V 1) -> lam V
| app: lam V -> lam V -> lam V.

Definition closed_terms := lam (Fin.t).


Definition level_terms {n:nat} := lam (incr Fin.t n).

Fixpoint binddt_lam (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2: Type} (f: nat * v1 -> G (lam v2)) (t: lam v1): G (lam v2) :=
  match t with
  | tvar v    => f (0, v)
  | abs body  => pure (@abs v2) <⋆> binddt_lam (f ⦿ 1) body
  | app t1 t2 => pure (@app v2) <⋆> binddt_lam f t1 <⋆> binddt_lam f t2
  end.

#[export] Instance Return_Lam: Return lam := tvar.
#[export] Instance Binddt_Lam: Binddt nat lam lam := @binddt_lam.
#[export] Instance DTM_Lam: DecoratedTraversableMonad nat lam.
Proof.
  derive_dtm.
Qed.

#[export] Instance DTM_Lam_Explicit: DecoratedTraversableMonad nat lam.
Proof.
  constructor.
  - typeclasses eauto.
  - intros.
    reflexivity.
  - constructor.
    + intros. ext t.
      induction t as [v | t | t1 IHt1 t2 IHt2 ].
      * reflexivity.
      * cbn.
        unfold id.
        simplify_applicative_I.
