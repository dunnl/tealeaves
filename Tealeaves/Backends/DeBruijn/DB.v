From Tealeaves Require Import
  Classes.Kleisli.DT.Monad
  Classes.Kleisli.Decorated.Functor
  Data.Natural.

From Autosubst Require Import
  Autosubst.

From Coq Require Import
  Init.Datatypes
  Lists.List.

Import Kleisli.DT.Functor.Notations.
Import Kleisli.DT.Monad.Derived.
Import Monoid.Notations.
Import DT.Monad.Notations.

#[local] Generalizable Variables W T.

(* Iterate an endofunction <<n>> times *)
Fixpoint iterate (n : nat) {A : Type} (f : A -> A) :=
  match n with
  | 0 => @id A
  | S n' => f ∘ iterate n' f
  end.

(** ** De Bruijn operations as defined by Tealeaves *)
(******************************************************************************)
Module DB1.
  Section ops.

    Context
      `{Return T}
      `{Classes.Kleisli.DT.Monad.Monad nat T}.

    Definition cons (X : Type) : X -> (nat -> X) -> (nat -> X)  :=
      fun new sub n => match n with
                    | O => new
                    | S n' => sub n'
                    end.

    Definition renup (σ : nat -> nat) : nat -> nat :=
      cons nat 0 (S ∘ σ).

    Definition rename (σ : nat -> nat) : T nat -> T nat :=
      fmapd T (fun '(depth, ix) => iterate depth renup σ ix).

    Definition up (σ : nat -> T nat) : nat -> T nat :=
      cons (T nat) (ret T 0) (rename S ∘ σ).

    Definition inst (σ : nat -> T nat) : T nat -> T nat :=
      binddt T (fun A => A) (fun '(depth, ix) => iterate depth up σ ix).

  End ops.
End DB1.

(** ** De Bruijn operations as defined by Tealeaves *)
(******************************************************************************)
Module DB2.
  Section ops.

    Context
      `{Return T}
      `{Classes.Kleisli.DT.Monad.Monad nat T}.

    (* Increase free variables by a given amount. *)
    Definition shift (n : nat) (p : nat * nat) : nat :=
      match p with
      | pair depth ix => if Nat.ltb ix depth then ix else ix + n
      end.

    Lemma shift_zero : shift 0 = extract (prod nat).
    Proof.
      ext [a b]. unfold shift. destruct (Nat.ltb b a).
      - reflexivity.
      - cbn. lia.
    Qed.

    Definition scoot : nat -> (nat -> T nat) -> (nat -> T nat)  :=
      fun watermark sub ix =>
        if Nat.ltb ix watermark then ret T ix
        else fmapd T (shift watermark) (sub (ix - watermark)).

    Definition open (sub : nat -> T nat) (t : T nat) : T nat :=
      binddt T (fun A => A) (fun '(depth, ix) => scoot depth sub ix) t.

  End ops.
End DB2.

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

Lemma DB1_matches_DB2 : forall (t : term nat) (σ : nat -> term nat), DB1.inst σ t = DB2.open σ t.
Proof.
  intros. generalize dependent σ. induction t; intros σ.
  - cbn. rewrite DB2.shift_zero.
    rewrite (dfun_fmapd1 nat term).
    unfold id. fequal. lia.
  - cbn. fequal; eauto.
  - cbn. fequal. fequal.
    ext [depth ix]. cbn.
    unfold DB1.up, DB1.cons.
    unfold compose.
    unfold DB2.scoot. destruct ix.
    + reflexivity.
    + induction depth.
      * cbn. admit.
      * cbn. admit.
Abort.

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

Lemma key_lemma :
  forall (σ : nat -> term nat) (depth : nat) (ix : nat),
    iterate depth DB1.up σ ix =
      DB2.scoot depth σ ix.
Proof.
  intros. unfold DB1.up, DB2.scoot.
  induction depth.
  - remember (Nat.ltb ix 0).
    symmetry in Heqb.
    destruct b.
    + exfalso. rewrite PeanoNat.Nat.ltb_lt in Heqb. lia.
    + cbn. rewrite DB2.shift_zero.
      rewrite (dfun_fmapd1 nat term).
      unfold id. fequal. lia.
  - unfold iterate. unfold compose.
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
