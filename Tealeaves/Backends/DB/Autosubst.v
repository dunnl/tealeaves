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



(*
(** ** De Bruijn operations as defined by Autosubst? *)
(******************************************************************************)
Module DB2.
  Section ops.

  Context
    `{ret_inst : Return T}
    `{Map_T_inst : Map T}
    `{Mapd_T_inst : Mapd nat T}
    `{Traverse_T_inst : Traverse T}
    `{Bind_T_inst : Bind T T}
    `{Mapdt_T_inst : Mapdt nat T}
    `{Bindd_T_inst : Bindd nat T T}
    `{Bindt_T_inst : Bindt T T}
    `{Binddt_T_inst : Binddt nat T T}
    `{! Compat_Map_Binddt nat T T}
    `{! Compat_Mapd_Binddt nat T T}
    `{! Compat_Traverse_Binddt nat T T}
    `{! Compat_Bind_Binddt nat T T}
    `{! Compat_Mapdt_Binddt nat T T}
    `{! Compat_Bindd_Binddt nat T T}
    `{! Compat_Bindt_Binddt nat T T}
    `{Monad_inst : ! DecoratedTraversableMonad nat T}
    `{Map_U_inst : Map U}
    `{Mapd_U_inst : Mapd nat U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Mapdt_U_inst : Mapdt nat U}
    `{Bindd_U_inst : Bindd nat T U}
    `{Bindt_U_inst : Bindt T U}
    `{Binddt_U_inst : Binddt nat T U}
    `{! Compat_Map_Binddt nat T U}
    `{! Compat_Mapd_Binddt nat T U}
    `{! Compat_Traverse_Binddt nat T U}
    `{! Compat_Bind_Binddt nat T U}
    `{! Compat_Mapdt_Binddt nat T U}
    `{! Compat_Bindd_Binddt nat T U}
    `{! Compat_Bindt_Binddt nat T U}
    `{Module_inst : ! DecoratedTraversableRightPreModule nat T U
     (unit := Monoid_unit_zero)
     (op := Monoid_op_plus)}.

    Notation "↑" := shift.
    Notation "f '✪' g" := (kc1 g f) (at level 30).
    Infix "⋅" := (DB1.cons) (at level 10).

  (*
    Definition cons (X : Type) : X -> (nat -> X) -> (nat -> X)  :=
      fun new sub n => match n with
                    | O => new
                    | S n' => sub n'
                    end.
as above
   *)

    Definition renup (σ : nat -> nat) : nat -> nat :=
      0 ⋅ (S ∘ σ).

    Definition rename (σ : nat -> nat) : T nat -> T nat :=
      mapd (fun '(depth, ix) => iterate depth renup σ ix).

    Definition up (σ : nat -> T nat) : nat -> T nat :=
      cons (T nat) (ret 0) (rename S ∘ σ).

    Definition inst (σ : nat -> T nat) : T nat -> T nat :=
      bindd (fun '(depth, ix) => iterate depth up σ ix).

  End ops.
End DB1.
*)

