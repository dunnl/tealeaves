






























    (* Given a substitution of x by u, encode the logic of what happens at <<current>> if <<history>> is the set of names
       given to the binders so far *)
    Definition rename_binder_local_history:
      list name * name -> name :=
      fun '(history, b) =>
        if x == b
        then b
        else if SmartAtom.name_inb b (fv_u)
             then fresh (conflicts ++ history ++ [b])
             else if SmartAtom.name_inb b (conflicts ++ history)
                  then fresh (conflicts ++ history ++ [b])
                  else b.

    Definition ctx_to_history: list name -> list name :=
      fold_with_history rename_binder_local_history.

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
      (b ∈ (conflicts ++ hist)) ->
      rename_binder_local_history (hist, b) = fresh (conflicts ++ hist ++ [b]).
    Proof.
      introv BneqX BinFVu BninHist.
      unfold rename_binder_local_history.
      destruct_eq_args x b.
      rewrite <- SmartAtom.name_inb_iff_false in BinFVu.
      rewrite BinFVu.
      step_set_test.
      reflexivity.
    Qed.


    Lemma rename_binder_local_history_rw4 {hist b}:
      b <> x ->
      ~ (b ∈ fv_u) ->
      ~ (b ∈ (conflicts ++ hist)) ->
      rename_binder_local_history (hist, b) = b.
    Proof.
      introv BneqX BinFVu BninHist.
      unfold rename_binder_local_history.
      destruct_eq_args x b.
      rewrite <- SmartAtom.name_inb_iff_false in BinFVu.
      rewrite BinFVu.
      step_set_test.
      reflexivity.
    Qed.


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
      nm ∈ (conflicts) ->
      ctx_to_history (nm :: l) =
        fresh (conflicts ++ [nm]) :: fold_with_history (rename_binder_local_history ⦿ [fresh (conflicts ++ [nm])]) l.
    Proof.
      intros.
      unfold ctx_to_history.
      rewrite fold_with_history_cons.
      rewrite rename_binder_local_history_rw3; auto.
      rewrite List.app_nil_r.
      assumption.
    Qed.

    Lemma ctx_to_history_cons_rw4 {nm l}:
      x <> nm ->
      ~ (nm ∈ fv_u) ->
      ~ nm ∈ (conflicts) ->
      ctx_to_history (nm :: l) =
        nm :: fold_with_history (rename_binder_local_history ⦿ [nm]) l.
    Proof.
      intros.
      unfold ctx_to_history.
      rewrite fold_with_history_cons.
      rewrite rename_binder_local_history_rw4; auto.
      rewrite List.app_nil_r.
      assumption.
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


    (*

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

    Lemma rename_binder_local_spec:
      forall '(ctx, b),
        rename_binder_local (ctx, b) = rename_binder_local_history (ctx_to_history ctx, b).
    Proof.
      intros [ctx b].
      destruct (destruct_in x ctx).
      rewrite rename_binder_local_rw1.
      rewrite rename_binder_local_history_rw1.

      step_set_test.
      rewrite rename_binder_local_history_rw2.

     *)

 Definition rename_binder_local:
      list name * name -> name :=
   fun '(ctx, b) =>
     rename_binder_local_history (ctx_to_history ctx, b).

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
           ret (T := T name) (rename_binder_local (prefix, v))
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
 Lemma subst_local_rw3: forall pre post ctx v,
     ~ (x ∈ ctx) ->
     x <> v ->
     get_binding ctx v = Bound pre v post ->
     subst_local (ctx, v) = ret (rename_binder_local_history (ctx_to_history pre, v)).
 Proof.
   intros.
   unfold subst_local.
   step_set_test.
   rewrite H3.
   unfold rename_binder_local.
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
