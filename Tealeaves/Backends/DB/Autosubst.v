(*
(** ** Autosubst *)
(******************************************************************************)
Section Autosubst.

  Inductive term (var : Type) : Type :=
  | tvar (x : var)
  | app (s t : term var)
  | lam (s : {bind (term var)}).

  #[export] Instance Ids_term : Ids (term var). derive. Defined.
  #[export] Instance Rename_term : Rename (term var). derive. Defined.
  #[export] Instance Subst_term : Subst (term var). derive. Defined.

End Autosubst.

Export DT.Functor.Notations. (* ∈d *)
Import Monoid.Notations. (* Ƶ and ● *)
Export Classes.Kleisli.DT.Monad.Derived. (* DTM sub-instances *)
Export Applicative.Notations. (* <⋆> *)
Export DT.Monad.Notations. (* ⋆dtm *)
Export List.ListNotations. (* [] :: *)
Export Product.Notations. (* × *)
Export Setlike.Functor.Notations. (* ∈ *)

Fixpoint binddt_term (G : Type -> Type) `{Fmap G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (term v2)) (t : term v1) : G (term v2) :=
  match t with
  | tvar _ v => f (0, v)
  | lam _ body => pure G (@lam v2) <⋆> binddt_term G (preincr 1 f) body
  | app _ t1 t2 => pure G (@app v2) <⋆> binddt_term G f t1 <⋆> binddt_term G f t2
  end.

#[export] Instance: Return term := @tvar.
#[export] Instance: Binddt nat term term := @binddt_term.
#[export] Instance: DT.Monad.Monad nat term. Admitted. (* We've done this before *)
 *)

Lemma DB2_matches_Autosubst : forall (t : term nat) (σ : nat -> term nat), subst σ t = DB2.open σ t.
Proof.
  intros. generalize dependent σ. induction t; intros σ.
  - cbn. rewrite DB2.shift_zero.
    rewrite (dfun_fmapd1 nat term).
    unfold id. fequal. lia.
  - cbn. fequal; eauto.
  - cbn. fequal. specialize (IHt (up σ)).
    change var with nat in *.
    change (@subst (term nat) Subst_term) with Subst_term.
    rewrite IHt.
    unfold DB2.open. fequal. ext [depth ix].
    cbn. admit.
Abort.

(** ** De Bruijn operations, more faithful to Autosubst *)
(*
  Definition up (n : nat) : term nat := tvar (S n).

  Fixpoint instantiation (σ : nat -> term nat) (t : term nat) {struct t} :=
    match t with
    | tvar n => σ n
    | app t1 t2 => app (instantiation σ t1) (instantiation σ t2)
    | lam body => lam (instantiation (lift σ) body)
    end
  with lift (σ : nat -> term nat) : nat -> term nat :=
         cons (tvar 0) (composition up σ)
  with composition (σ1 σ2 : nat -> term nat) : nat -> term nat :=
         fun n => instantiation σ2 (σ1 n).
*)
