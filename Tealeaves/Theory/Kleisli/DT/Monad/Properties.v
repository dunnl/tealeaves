From Tealeaves Require Export
  Classes.Kleisli.DT.Monad
  Theory.Kleisli.DT.Monad.ToFunctor
  Functors.Schedule.

Import Product.Notations.
Import Applicative.Notations.
Import Schedule.Notations.
#[local] Generalizable Variables W F M A B.

(*
(** * <<Schedule>> *)
(******************************************************************************)
Section schedule_operation.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Definition schedule {A : Type} (B : Type) : W * A -> @Schedule T W A B (T B) :=
    fun '(w, a) => Go (T B -> T B) (@id (T B)) ⧆ (w, a).

  Definition iterate {A : Type} (B : Type) : T A -> @Schedule T W A B (T B) :=
    binddt T (@Schedule T W A B) (schedule B).

End schedule_operation.

(** ** Representing <<binddt>> with <<runSchedule>> *)
(******************************************************************************)
Section binddt_to_runSchedule.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Theorem binddt_to_runSchedule :
    forall `{Applicative F} (A B : Type) (t : T A)
      (f : W * A -> F (T B)),
      binddt T F f t = runSchedule T F  f (iterate T B t).
  Proof.
    intros. unfold iterate.
    compose near t on right.
    rewrite (kdtm_morph W T Schedule F).
    fequal. ext [w a]. cbn.
    now rewrite ap1.
  Qed.

  Theorem id_to_runSchedule `(t : T A) :
    t = runSchedule T (fun A => A) (ret T ∘ extract (W ×)) (iterate T A t).
  Proof.
    change t with (id t) at 1.
    rewrite <- (kdtm_binddt1 W T).
    rewrite binddt_to_runSchedule.
    reflexivity.
  Qed.

End binddt_to_runSchedule.
*)

(** * Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import ToFunctor.Operation.
  Import ToFunctor.Instance.

  Lemma binddt_constant_applicative1
        `{Monoid M} {B : Type}
        `(f : W * A -> const M (T B)) :
    binddt (B := B) T (const M) f =
    binddt (B := False) T (const M) (f : W * A -> const M (T False)).
  Proof.
    change_right (fmap (B := T B) (const M) (fmap T exfalso)
                    ∘ (binddt (B := False) T (const M) (f : W * A -> const M (T False)))).
    rewrite (fmap_binddt T (const M)).
    - reflexivity.
    - typeclasses eauto.
  Qed.

  Lemma binddt_constant_applicative2 (fake1 fake2 : Type) `{Monoid M}
        `(f : W * A -> const M (T B)) :
    binddt (B := fake1) T (const M)
            (f : W * A -> const M (T fake1))
    = binddt (B := fake2) T (const M)
              (f : W * A -> const M (T fake2)).
  Proof.
    intros. rewrite (binddt_constant_applicative1 (B := fake1)).
    rewrite (binddt_constant_applicative1 (B := fake2)). easy.
  Qed.

End lemmas.
