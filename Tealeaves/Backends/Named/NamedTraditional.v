From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Functors.List_Telescoping_General
  Backends.Named.Names
  Backends.Named.Named
  Functors.Constant
  Functors.Subset.

Import Subset.Notations.
Import Monoid.Notations.
Import Applicative.Notations.
Import List.ListNotations.
Import Product.Notations.
Import ContainerFunctor.Notations.

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

Section alt.

  Context
    {T: Type -> Type -> Type}
    `{forall W, Return (T W)}
    `{Substitute T T}.

  Import DecoratedTraversableMonadPoly.DerivedOperations.

  Section rename_local.

    Context (conflicts: list name). (* Top level conflicts *)

    (* X is the var being substituted, fv_u is FV u *)
    Context (x: name) (fv_u: list name) (u: T name name).


    (* Given a substitution of x by u, encode the logic of what happens at <<current>> if <<history>> is the set of names
       given to the binders so far *)
    Definition rename_binder_local_history:
      list name * name -> name :=
      fun '(history, b) =>
        if x == b
        then b
        else if SmartAtom.name_inb b (fv_u)
             then fresh (conflicts ++ history ++ [b])
             else b.

    Lemma rename_binder_local_history_rw1 {hist b}:
      b = x ->
      rename_binder_local_history (hist, b) = b.
    Proof.
      intros.
      unfold rename_binder_local_history.
      destruct_eq_args x b.
    Qed.

    Lemma rename_binder_local_history_rw2 {hist b}:
      b <> x ->
      (b ∈ fv_u) ->
      rename_binder_local_history (hist, b) = fresh (conflicts ++ hist ++ [b]).
    Proof.
      introv BneqX BinFVu.
      unfold rename_binder_local_history.
      destruct_eq_args x b.
      rewrite <- SmartAtom.name_inb_iff in BinFVu.
      rewrite BinFVu.
      reflexivity.
    Qed.

    Lemma rename_binder_local_history_rw2' {b}:
      b <> x ->
      b ∈ fv_u ->
      rename_binder_local_history (nil, b) = fresh (conflicts ++ [b]).
    Proof.
      intros.
      rewrite rename_binder_local_history_rw2; auto.
    Qed.

    Lemma rename_binder_local_history_rw3 {hist b}:
      b <> x ->
      ~ (b ∈ fv_u) ->
      rename_binder_local_history (hist, b) = b.
    Proof.
      introv BneqX BinFVu.
      unfold rename_binder_local_history.
      destruct_eq_args x b.
      rewrite <- SmartAtom.name_inb_iff_false in BinFVu.
      rewrite BinFVu.
      reflexivity.
    Qed.

    Definition ctx_to_history: list name -> list name :=
      fold_with_history rename_binder_local_history.


    Lemma ctx_to_history_nil: ctx_to_history [] = [].
    Proof.
      intros.
      reflexivity.
    Qed.

    Lemma ctx_to_history_cons1 {nm l}:
      x = nm ->
      ctx_to_history (nm :: l) =
        nm :: fold_with_history (rename_binder_local_history ⦿ [nm]) l.
    Proof.
      intros.
      unfold ctx_to_history.
      rewrite fold_with_history_cons.
      rewrite rename_binder_local_history_rw1; auto.
    Qed.


    Lemma ctx_to_history_cons_cons2 {nm l}:
      x <> nm ->
      (nm ∈ fv_u) ->
      ctx_to_history (nm :: l) =
        fresh (conflicts ++ [nm]) :: fold_with_history (rename_binder_local_history ⦿ [fresh (conflicts ++ [nm])]) l.
    Proof.
      intros.
      unfold ctx_to_history.
      rewrite fold_with_history_cons.
      rewrite rename_binder_local_history_rw2'; auto.
    Qed.

    Lemma ctx_to_history_cons_rw3 {nm l}:
      x <> nm ->
      ~ (nm ∈ fv_u) ->
      ctx_to_history (nm :: l) =
        nm :: fold_with_history (rename_binder_local_history ⦿ [nm]) l.
    Proof.
      intros.
      unfold ctx_to_history.
      rewrite fold_with_history_cons.
      rewrite rename_binder_local_history_rw3; auto.
    Qed.


    Lemma ctx_to_history_app: forall l1 l2,
        ctx_to_history (l1 ++ l2) =
          ctx_to_history l1 ++
            (fold_with_history (rename_binder_local_history ⦿ fold_with_history rename_binder_local_history l1) l2).
    Proof.
      intros.
      unfold ctx_to_history.
      rewrite fold_with_history_app.
      reflexivity.
    Qed.


    (* Name a binder to something else during substitution *)
    Definition rename_binder_local:
      list name * name -> name :=
      fun '(ctx, b) =>
        if SmartAtom.name_inb x ctx (* Halt substitution early, we didn't recurse where x appears in ctx *)
        then b
        else if x == b (* Else check if halt now *)
             then b (* This binder is the name of the free variable we're substituting, halt and leave binder alone *)
             else if SmartAtom.name_inb b fv_u (* Else check if need to rename *)
                  then (rename_binder_local_history (ctx_to_history ctx, b))
                  else b.

    (* This binder is under an abstraction of the substituted variable, do nothing (subst halted earlier) *)
    Lemma rename_binder_local_rw1: forall ctx b,
        x ∈ ctx ->
        rename_binder_local (ctx, b) = b.
    Proof.
      intros.
      unfold rename_binder_local.
      step_set_test.
      reflexivity.
    Qed.

    (* This binder is equal to the variable begin substituted (subst is halting now) *)
    Lemma rename_binder_local_rw2: forall ctx b,
        ~ (x ∈ ctx) ->
        x = b ->
        rename_binder_local (ctx, b) = b.
    Proof.
      intros.
      unfold rename_binder_local.
      destruct_eq_args x b.
      now step_set_test.
    Qed.

    (* This binder conflicts with the free variables of u, rename after computing its history from its context *)
    Lemma rename_binder_local_rw3: forall ctx b,
        ~ (x ∈ ctx) ->
        x <> b ->
        b ∈ fv_u ->
        rename_binder_local (ctx, b) = (rename_binder_local_history (ctx_to_history ctx, b)).
    Proof.
      intros.
      unfold rename_binder_local.
      step_set_test.
      destruct_eq_args x b.
      step_set_test.
      reflexivity.
    Qed.

    (* This is a bound variable that doesn't cause any conflicts, do nothing *)
    Lemma rename_binder_local_rw4: forall ctx b,
        ~ (x ∈ ctx) ->
        x <> b ->
        ~ (b ∈ fv_u) ->
        rename_binder_local (ctx, b) = b.
    Proof.
      intros.
      subst.
      unfold rename_binder_local.
      destruct (SmartAtom.name_inb x ctx); auto.
      destruct_eq_args x b.
      step_set_test.
      reflexivity.
    Qed.

    Corollary rename_binder_local_rw5: forall ctx b,
        ~ (b ∈ fv_u) ->
        rename_binder_local (ctx, b) = b.
    Proof.
      intros.
      unfold rename_binder_local.
      destruct (SmartAtom.name_inb x ctx).
      - reflexivity.
      - destruct_eq_args x b.
        step_set_test.
        reflexivity.
    Qed.

    Definition subst_local:
      list name * name -> T name name :=
      fun '(ctx, v) =>
        if SmartAtom.name_inb x ctx (* Halt substitution early *)
        then ret (T := T name) v
        else
          match (get_binding ctx v) with
          | Unbound _ =>
              if v == x
              then u
              else ret (T := T name) v
          | Bound prefix _ _ =>
              if v == x
              then ret (T := T name) v
              else if SmartAtom.name_inb v (fv_u)
                   then ret (T := T name) (rename_binder_local_history (prefix, v))
                   else ret (T := T name) (rename_binder_local_history (prefix, v))
                            (*
                   else ret (T := T name) v
                             *)
          end.


    (* This variable is under an abstraction of the substituted variable, do nothing (subst halted earlier) *)
    Lemma subst_local_rw1: forall ctx v,
        x ∈ ctx ->
        subst_local (ctx, v) = ret v.
    Proof.
      intros.
      unfold subst_local.
      step_set_test.
      reflexivity.
    Qed.

    (* This variable is equal to the variable begin substituted, replace it *)
    Lemma subst_local_rw2: forall ctx v,
        ~ (x ∈ ctx) ->
        x = v ->
        subst_local (ctx, v) = u.
    Proof.
      intros.
      unfold subst_local.
      destruct_eq_args x v.
      step_set_test.
      rewrite get_binding1; auto.
    Qed.

    Lemma hmmm:forall ctx v,
        ~ v ∈ ctx ->
        v = (rename_binder_local_history (ctx_to_history ctx, v)).
    Proof.
      intros.
    Abort.


    (* This is a bound variable that  conflicts with the free variables of u,
       rename it to match its binder *)
    Lemma subst_local_rw3: forall ctx v,
        ~ (x ∈ ctx) ->
        x <> v ->
        v ∈ fv_u ->
        subst_local (ctx, v) = ret (rename_binder_local_history (ctx_to_history ctx, v)).
    Proof.
      intros.
      unfold subst_local.
      step_set_test.
      destruct (get_binding_spec ctx v) as [Case1 | Case2].
      { destruct Case1 as [hyp1 hyp2].
        rewrite hyp1.
        destruct_eq_args v x.
        destruct_eq_args v x.
        step_set_test.
        fequal.

      rewrite get_binding1.
      destruct_eq_args x v.
      step_set_test.
      reflexivity.
    Qed.

    (* This is a bound variable that doesn't cause any conflicts, do nothing *)
    Lemma subst_local_rw4: forall ctx v,
        ~ (x ∈ ctx) ->
        x <> v ->
        ~ (v ∈ fv_u) ->
        suvst_local (ctx, v) = v.
    Proof.
      intros.
      subst.
      unfold subst_local.
      destruct (SmartAtom.name_inb x ctx); auto.
      destruct_eq_args x b.
      step_set_test.
      reflexivity.
    Qed.


    Definition subst_top
      (t: T name name): T name name :=
      substitute (G := fun A => A) (U := T)
        rename_binder_local
        subst_local t.

  End rename_local.

  Definition subst
    (x: name) (u: T name name)
    (t: T name name): T name name :=
    subst_top (FV T t ++ FV T u) x (FV T u) u t.

End alt.
