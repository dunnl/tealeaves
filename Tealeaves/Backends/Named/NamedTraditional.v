From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.List_Telescoping_General
  Backends.Named.Names
  Backends.Named.Common
  Backends.Named.Named (FV)
  Functors.Constant
  Functors.Subset.

Export Backends.Named.Names.
Export Backends.Named.Common.
Export Backends.Named.Named (FV).

Import Subset.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import List.ListNotations.
Import Product.Notations.
Import ContainerFunctor.Notations.

Lemma destruct_in: forall (a: name) (l: list name),
    a ∈ l \/ ~ (a ∈ l).
Proof.
  intros.
  rewrite <- SmartAtom.name_inb_iff.
  destruct (SmartAtom.name_inb a l); auto.
Qed.

Ltac step_set_test :=
  match goal with
  | H: ~ ?x ∈ ?t |- _ =>
      let Hf := fresh "H" in
      pose H as Hf;
      rewrite <- SmartAtom.name_inb_iff_false in Hf;
      progress (repeat rewrite Hf)
  | H: ?x ∈ ?t |- _ =>
      let Hf := fresh "H" in
      pose H as Hf;
      rewrite <- SmartAtom.name_inb_iff in Hf;
      progress (repeat rewrite Hf)
  end.

Section ops.

  Context
    {T: Type -> Type -> Type}
    `{forall W, Return (T W)}
    `{Substitute T T}.

  Import DecoratedTraversableMonadPoly.DerivedOperations.

  Section rename_local.

    Context
      (x: name)
      (u: T name name).

    Context
      (conflicts: list name)  (* Top level conflicts, intuitively {{x}} \cup FV t \cup FV u *).

    Definition rename_binder_from_history: list name * name -> name :=
      fun '(history, b) => fresh (conflicts ++ history).

    Definition context_to_history (ctx : list name): list name :=
      fold_with_history rename_binder_from_history ctx.

    Definition rename_binder_from_context: list name * name -> name :=
      fun '(ctx, v) => rename_binder_from_history (context_to_history ctx, v).

    Definition subst_from_ctx:
      list name * name -> T name name :=
      fun '(ctx, v) =>
        match get_binding ctx v with
        | Unbound _ =>
            (* v is a free variable *)
            if v == x
            then u
            else ret v
        | Bound prefix _ post =>
            (* v is a bound variable, give it the name of whatever it was bound to *)
            ret (rename_binder_from_context (prefix, v))
        end.

  End rename_local.

  Definition subst_top
    (x: name) (u: T name name)
    (conflicts: list name)
    (t: T name name): T name name :=
   substitute (G := fun A => A) (U := T)
     (rename_binder_from_context conflicts)
     (subst_from_ctx x u conflicts) t.

  Definition subst
    (x: name) (u: T name name)
    (t: T name name): T name name :=

    subst_top x u ([x] ++ FV T t ++ FV T u) t.

End ops.
