From Tealeaves Require Export
  Backends.LN
  Misc.NaturalNumbers
  Functors.List
  Theory.DecoratedTraversableMonad
  Examples.STLC.Syntax.

Export Kleisli.DecoratedTraversableMonad.Notations. (* ∈d *)
Import Monoid.Notations. (* Ƶ and ● *)
Import Misc.Subset.Notations. (* ∪ *)
Export Applicative.Notations. (* <⋆> *)
Export List.ListNotations. (* [] :: *)
Export LN.Notations. (* operations *)
Export LN.AtomSet.Notations.
Export LN.AssocList.Notations. (* one, ~ *)
Export Product.Notations. (* × *)
Export ContainerFunctor.Notations. (* ∈ *)
Export DecoratedContainerFunctor.Notations. (* ∈d *)

#[local] Generalizable Variables G.

#[local] Set Implicit Arguments.

Inductive typ := Mktyp.

(** * Language definition *)
(******************************************************************************)
Inductive term :=
| atm : atom -> term
| ix  : nat -> term
| lam : typ -> term -> term
| app : term -> term -> term.

(** ** Instantiate Tealeaves *)
(******************************************************************************)
Fixpoint to_T (t: term) : Syntax.term LN :=
  match t with
  | atm a => Syntax.tvar (Fr a)
  | ix n => Syntax.tvar (Bd n)
  | lam τ t => Syntax.lam τ (to_T t)
  | app t1 t2 => Syntax.app (to_T t1) (to_T t2)
  end.

Fixpoint to_T_inv (t: Syntax.term LN) : term :=
  match t with
  | tvar (Fr a) => atm a
  | tvar (Bd n) => ix n
  | Syntax.lam τ t => lam τ (to_T_inv t)
  | Syntax.app t1 t2 => app (to_T_inv t1) (to_T_inv t2)
  end.

Lemma to_T_iso: forall (t : term), to_T_inv (to_T t) = t.
Proof.
  intros.
  induction t.
  - reflexivity.
  - reflexivity.
  - cbn. now rewrite IHt.
  - cbn. now rewrite IHt1, IHt2.
Qed.

Lemma to_T_iso_inv: forall (t : Syntax.term LN), to_T (to_T_inv t) = t.
Proof.
  intros.
  induction t.
  - cbn. destruct v; reflexivity.
  - cbn. now rewrite IHt.
  - cbn. now rewrite IHt1, IHt2.
Qed.

Module STLC_SIG <: SyntaxSIG with Definition term := term.

  Definition term : Type := term.
  Definition T := Syntax.term.
  Definition ret_inst := Syntax.Return_STLC.
  Definition binddt_inst := Syntax.Binddt_STLC.
  Definition monad_inst := Syntax.DTM_STLC.

  Definition to_T := to_T.
  Definition to_T_inv := to_T_inv.
  Definition to_T_iso := to_T_iso.
  Definition to_T_iso_inv := to_T_iso_inv.

  Definition from_atom := atm.
  Definition from_ix := ix.

  Definition from_atom_Ret:
    from_atom = to_T_inv ○ @ret T ret_inst LN ○ Fr :=
    ltac:(reflexivity).
  Definition from_ix_Ret:
    from_ix = to_T_inv ○ @ret T ret_inst LN ○ Bd :=
    ltac:(reflexivity).

End STLC_SIG.

Module Theory <: TheorySIG
  := MakeTheory STLC_SIG.
Import Theory.
Import Theory.Notations.

(** ** Deeper Instantiate Tealeaves *)
(******************************************************************************)

(** ** Use Tealeaves *)
(******************************************************************************)
Reserved Notation "Γ ⊢ t : S" (at level 90, t at level 99).

Inductive Judgment : ctx -> term -> typ -> Prop :=
| j_var :
    forall (Γ : ctx) (x : atom) (A : typ),
      uniq Γ ->
      (x, A) ∈ Γ ->
      Γ ⊢ (atm x) : A
| j_abs :
    forall (L : AtomSet.t) Γ (τ1 τ2: typ) (t: term),
      (forall x : atom, ~ AtomSet.In x L -> Γ ++ x ~ τ1 ⊢ t '(atm x) : τ2) ->
      Γ ⊢ fun τ1 t : τ1 ⟹ τ2
| j_app :
    forall Γ (t1 t2 : term) (A B : typ),
      Γ ⊢ t1 : A ⟹ B ->
      Γ ⊢ t2 : A ->
      Γ ⊢ [t1]@[t2] : B
where "Γ ⊢ t : A" := (Judgment Γ t A).
