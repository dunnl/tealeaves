From Tealeaves Require Export
  Backends.LN
  Simplification.Simplification.

Import LN.Simplification.
Export LN.Notations.

#[local] Generalizable Variables G A B C.
#[local] Set Implicit Arguments.

(* TODO: this is needed because <<list>> has no other instance *)
#[export] Existing Instance ToBatch_Traverse.

(** * Language definition *)
(******************************************************************************)
Inductive term (v : Type) :=
| tvar : v -> term v
| letin : list (term v) -> term v -> term v
| app : term v -> term v -> term v.

#[export] Instance Return_Lam: Return term := tvar.

Section term_mut_ind1.

  Variables
    (v : Type)
    (P : term v -> Prop).

  Hypotheses
    (tvar_case : forall v, P (tvar v))
      (letin_nil_case :  forall t, P t -> P (letin nil t))
      (letin_cons_case : forall (u: term v) (l : list (term v)) (t: term v)
                           (IHu: P u) (IHl: List.Forall P l)
                           (IHt: P t), P (letin (u :: l) t))
      (app_case : forall t: term v, P t -> forall u: term v, P u -> P (app t u)).

  Definition term_mut_ind: forall t, P t :=
    fix F t :=
      match t with
      | tvar v => tvar_case v
      | letin defs body =>
          match defs with
          | nil => @letin_nil_case body (F body)
          | cons u rest =>
              @letin_cons_case u rest body
                (F u)
                ((fix G l : List.Forall P l
                  := match l with
                     | nil =>
                         List.Forall_nil P
                     | cons x xs =>
                         List.Forall_cons x (l := xs) (F x) (G xs)
                     end) rest)
                (F body)
          end
      | app t1 t2 =>
          @app_case t1 (F t1) t2 (F t2)
      end.

End term_mut_ind1.

Lemma Forall_compat_list: forall (A: Type) (l : list A) (P: A -> Prop),
    List.Forall P l <-> Forall_List P l.
Proof.
  intros.
  induction l.
  - split.
    + intros _. exact I.
    + intros. apply List.Forall_nil.
  - split.
    + intro H.
      inversion H; subst.
      cbn. split. assumption. now apply IHl.
    + intro H.
      inversion H.
      apply List.Forall_cons. assumption. now apply IHl.
Qed.

Section term_mut_ind2.

  Variables
    (v : Type)
    (P : term v -> Prop).

  Hypotheses
    (tvar_case : forall v, P (tvar v))
    (letin_case : forall (defs: list (term v))
                      (body: term v)
                      (IHdefs: forall (t : term v), t ∈ defs -> P t)
                      (IHbody: P body),
          P (letin defs body))
    (app_case : forall t: term v, P t -> forall u: term v, P u -> P (app t u)).

  Definition term_mut_ind2: forall t, P t.
  Proof.
    intros.
    induction t using term_mut_ind.
    - auto.
    - apply letin_case.
      + inversion 1.
      + assumption.
    - apply letin_case.
      + introv Hin.
        autorewrite with tea_list in Hin.
        inversion Hin.
        * now subst.
        * rewrite Forall_compat_list in IHl.
          rewrite List.forall_iff in IHl.
          now apply IHl.
      + assumption.
    - auto.
  Qed.

End term_mut_ind2.

#[global] Ltac derive_dtm_custom_IH ::=
  constr:(term_mut_ind2).
