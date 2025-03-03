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

    (* X is the var being substituted, fv_u is FV u *)
    Context
      (x: name)
      (u: T name name).

    Context
      (conflicts: list name)  (* Top level conflicts, intuitively FV t \cup FV u *)
      (fv_u: list name).  (* Intuitively FV u *)

    Definition rename_binder_one (hist: list name) (b: name) :=
      if b == x
      then b
      else if SmartAtom.name_inb b (fv_u)
           then fresh ([x] ++ conflicts ++ hist ++ [b])
           else if SmartAtom.name_inb b (hist)
                then fresh ([x] ++ conflicts ++ hist ++ [b])
                else b.

    Fixpoint rename_binder_from_ctx_rec
      (ctx: list name)
      (hist: list name) (b: name): name :=
      match ctx with
      | nil =>
          rename_binder_one hist b

      | cons y rest =>
          if y == x
          then b
          else let z := rename_binder_one hist y in
               rename_binder_from_ctx_rec rest (hist ++ [z]) b
      end.

    Lemma rename_binder_from_ctx_rec_rw_nil: forall hist b,
        rename_binder_from_ctx_rec nil hist b =
          rename_binder_one hist b.
    Proof.
      intros. reflexivity.
    Qed.

    Lemma rename_binder_from_ctx_rec_rw_cons_neq: forall (y: name) (ctx: list name) hist b,
        y <> x ->
        rename_binder_from_ctx_rec (y :: ctx) hist b =
          rename_binder_from_ctx_rec ctx (hist ++ [rename_binder_one hist y]) b.
    Proof.
      intros.
      cbn.
      destruct_eq_args y x.
    Qed.


    Lemma rename_binder_from_ctx_rec_rw_cons_eq: forall (y: name) (ctx: list name) hist b,
        y = x ->
        rename_binder_from_ctx_rec (y :: ctx) hist b = b.
    Proof.
      intros.
      cbn.
      destruct_eq_args y x.
    Qed.


    Definition rename_binder_from_ctx:
      list name * name -> name :=
      fun '(ctx, b) =>
        rename_binder_from_ctx_rec ctx [] b.

    Definition context_to_renamed:
      list name -> list name :=
      fold_with_history rename_binder_from_ctx.

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
            ret (rename_binder_from_ctx (prefix, v))
        end.

  End rename_local.


  Definition subst_top
    (x: name) (u: T name name)
    (conflicts fv_u: list name)
   (t: T name name): T name name :=
   substitute (G := fun A => A) (U := T)
     (rename_binder_from_ctx x conflicts fv_u)
     (subst_from_ctx x u conflicts fv_u) t.

  Definition subst
    (x: name) (u: T name name)
    (t: T name name): T name name :=

    subst_top x u (FV T t ++ FV T u) (FV T u) t.

End ops.
