From Tealeaves.Backends.LN Require Export
  Atom AtomSet AssocList LN.

From Tealeaves.Misc Require Import
  NaturalNumbers.
From Tealeaves.Theory Require Import
  DecoratedTraversableMonad.

Module Type SyntaxSIGHetero.
  Parameter (iterm oterm : Type).
  Parameter (T U : Type -> Type).
  Parameter ret_inst: Return T.
  Parameter binddt_T_inst: Binddt nat T T.
  Parameter binddt_U_inst: Binddt nat T U.
  Parameter module_inst:
    DecoratedTraversableRightModule nat T U
      (Return_inst := ret_inst)
      (Bindd_T_inst := binddt_T_inst)
      (Bindd_U_inst := binddt_U_inst)
      (unit := Monoid_unit_zero)
      (op := Monoid_op_plus).
  Parameter to_T:  iterm -> T LN.
  Parameter to_T_inv: T LN -> iterm.
  Parameter to_U: oterm -> U LN.
  Parameter to_U_inv: U LN -> oterm.
  Parameter to_T_iso : forall (t : iterm), to_T_inv (to_T t) = t.
  Parameter to_U_iso : forall (t : oterm), to_U_inv (to_U t) = t.
  Parameter to_T_iso_inv : forall (t : T LN), to_T (to_T_inv t) = t.
  Parameter to_U_iso_inv : forall (t : U LN), to_U (to_U_inv t) = t.
  Parameter from_atom: atom -> iterm.
  Parameter from_ix: nat -> iterm.
  Parameter from_atom_Ret:
    from_atom = to_T_inv ○ @ret T ret_inst LN ○ Fr.
  Parameter from_ix_Ret:
    from_ix = to_T_inv ○ @ret T ret_inst LN ○ Bd.
End SyntaxSIGHetero.

Module Type TheorySIG.
  Parameters iterm oterm : Type.
  Parameters
    (open : iterm -> oterm -> oterm)
    (close : atom -> oterm -> oterm)
    (subst : atom -> iterm -> oterm -> oterm)
    (locally_closed_bool : oterm -> bool).
End TheorySIG.

Module MakeTheory_Hetero
  (Syntax: SyntaxSIGHetero) <: TheorySIG.
  Import Syntax.

  Definition iterm := Syntax.iterm.
  Definition oterm := Syntax.oterm.

  #[local] Existing Instance Syntax.ret_inst.
  #[local] Existing Instance Syntax.binddt_T_inst.
  #[local] Existing Instance Syntax.binddt_U_inst.
  #[local] Existing Instance Syntax.module_inst.
  #[local] Existing Instance Map_Binddt.
  #[local] Existing Instance Mapd_Binddt.
  #[local] Existing Instance Traverse_Binddt.
  #[local] Existing Instance Mapdt_Binddt.
  #[local] Existing Instance Bind_Binddt.
  #[local] Existing Instance Bindt_Binddt.
  #[local] Existing Instance Bindd_Binddt.
  #[local] Existing Instance ToBatch_Traverse.
  #[local] Existing Instance ToSubset_Traverse.

  Import AtomSet.Notations.

  Coercion to_T : Syntax.iterm >-> T.
  Coercion to_U : Syntax.oterm >-> U.

  Definition open : iterm -> oterm -> oterm :=
    fun t u => to_U_inv (open (T := T) (U := U) t u).

  Definition close : atom -> oterm -> oterm :=
    fun x u => to_U_inv (close (T := U) x u).

  Definition subst : atom -> iterm -> oterm -> oterm :=
    fun x t u => to_U_inv (subst (T := T) (U := U) x t u).

  Definition free : oterm -> list atom :=
    fun u => free (T := U) u.

  Definition freeset : oterm -> AtomSet.t :=
    fun u => freeset (T := U) u.

  Definition locally_closed : oterm -> Prop :=
    fun u => locally_closed (U := U) u.

  Definition locally_closed_bool : oterm -> bool :=
    fun u => locally_closed_bool (U := U) u.

  Definition scoped : oterm -> AtomSet.t -> Prop :=
    fun t γ => freeset t ⊆ γ.

  Definition subst_i : atom -> iterm -> iterm -> iterm :=
    fun x t u => to_T_inv (LN.subst (T := T) (U := T) x t u).

  Definition freeset_i : iterm -> AtomSet.t :=
    fun t => LN.freeset (T := T) t.

  Definition locally_closed_i : iterm -> Prop :=
    fun u => LN.locally_closed (U := T) u.

  Module Notations.
    Notation "t '{ x ~> u }" := (subst x u t) (at level 35).
    Notation "t '( u )" := (open u t) (at level 35).
    Notation "'[ x ] t" := (close x t) (at level 35).
  End Notations.

  Import Notations.

  Coercion from_atom : atom >-> Syntax.iterm.
  Coercion from_ix : nat >-> Syntax.iterm.

  Implicit Types (x y: atom) (t: iterm) (u: oterm).

  Theorem open_lc: forall t u,
      locally_closed u -> u '(t) = u.
  Proof.
    intros.
    unfold locally_closed.
    unfold open.
    rewrite open_lc.
    - apply to_U_iso.
    - assumption.
  Qed.

  Theorem freeset_subst_upper: forall x t u,
      freeset (u '{x ~> t}) ⊆ freeset u \\ {{x}} ∪ freeset_i t.
  Proof.
    intros.
    unfold freeset, freeset_i, subst.
    rewrite to_U_iso_inv.
    rewrite freeset_subst_upper.
    reflexivity.
  Qed.

  Theorem freeset_subst_lower: forall t u x,
      freeset u \\ {{ x }} ⊆ freeset (u '{x ~> t}).
  Proof.
    intros.
    unfold freeset, freeset_i, subst.
    rewrite to_U_iso_inv.
    apply freeset_subst_lower.
  Qed.

  Theorem close_open : forall x u,
      ~ x ∈@ freeset u ->
      '[x] (u '(from_atom x)) = u.
  Proof.
    intros.
    unfold close, open.
    rewrite from_atom_Ret.
    rewrite to_U_iso_inv.
    rewrite to_T_iso_inv.
    rewrite close_open.
    - rewrite to_U_iso.
      reflexivity.
    - rewrite free_iff_freeset.
      assumption.
  Qed.

  Theorem open_close : forall x u,
      ('[x] u) '(x) = u.
  Proof.
    intros.
    unfold close, open.
    rewrite from_atom_Ret.
    rewrite to_U_iso_inv.
    rewrite to_T_iso_inv.
    rewrite open_close.
    rewrite to_U_iso.
    reflexivity.
  Qed.

  Theorem subst_open_var : forall u t x y,
      x <> y ->
      locally_closed_i t ->
      u '(from_atom y) '{x ~> t} =
        u '{x ~> t} '(from_atom y).
  Proof.
    intros.
    unfold close, open, subst.
    rewrite to_U_iso_inv.
    rewrite to_U_iso_inv.
    rewrite from_atom_Ret.
    rewrite to_T_iso_inv.
    rewrite subst_open_var.
    - reflexivity.
    - assumption.
    - assumption.
  Qed.

  Theorem open_spec_eq : forall u t x,
      ~ x ∈@ freeset u ->
      u '(t) = u '(from_atom x) '{x ~> t}.
  Proof.
    intros.
    unfold close, open, subst.
    rewrite to_U_iso_inv.
    erewrite open_spec_eq.
    - rewrite from_atom_Ret.
      rewrite to_T_iso_inv.
      reflexivity.
    - assumption.
  Qed.

  Theorem subst_open :  forall t1 t2 u x,
      locally_closed_i t2 ->
      u '(t1) '{x ~> t2} =
        open (subst_i x t2 t1) (u '{x ~> t2}).
  Proof.
    intros.
    unfold close, open, subst, subst_i.
    rewrite to_U_iso_inv.
    rewrite subst_open.
    - rewrite to_U_iso_inv.
      rewrite to_T_iso_inv.
      reflexivity.
    - assumption.
  Qed.

  Theorem freeset_open_upper : forall u t,
      freeset (u '(t)) ⊆ freeset u ∪ freeset_i t.
  Proof.
    intros.
    unfold freeset, open.
    rewrite to_U_iso_inv.
    rewrite freeset_open_upper.
    reflexivity.
  Qed.

  Theorem freeset_open_lower : forall t u,
      freeset u ⊆ freeset (u '(t)).
  Proof.
    intros.
    unfold freeset, open.
    rewrite to_U_iso_inv.
    rewrite freeset_open_lower.
    reflexivity.
  Qed.

  Theorem freeset_close : forall u x,
      freeset ('[x] u) [=] freeset u \\ {{ x }}.
  Proof.
    intros.
    unfold freeset, close.
    rewrite to_U_iso_inv.
    rewrite freeset_close.
    reflexivity.
  Qed.

  Theorem nin_freeset_close : forall u x,
      ~ x ∈@ freeset ('[x] u).
  Proof.
    intros.
    unfold freeset, close.
    rewrite to_U_iso_inv.
    apply nin_freeset_close.
  Qed.

  Theorem freeset_close1 : forall u x y,
      y <> x ->
      y ∈@ freeset ('[x] u) <-> y ∈@ freeset u.
  Proof.
    intros.
    unfold close, freeset.
    rewrite to_U_iso_inv.
    rewrite <- free_iff_freeset.
    rewrite in_free_close_iff.
    rewrite <- free_iff_freeset.
    intuition.
  Qed.

End MakeTheory_Hetero.

Module Type SyntaxSIG.
  Parameter (term : Type).
  Parameter (T : Type -> Type).
  Parameter
    (ret_inst : Return T)
    (binddt_inst : Binddt nat T T)
    (monad_inst : DecoratedTraversableMonad nat T
              (unit := Monoid_unit_zero)
              (op := Monoid_op_plus)).
  Parameter to_T:  term -> T LN.
  Parameter to_T_inv: T LN -> term.
  Parameter to_T_iso : forall (t : term), to_T_inv (to_T t) = t.
  Parameter to_T_iso_inv : forall (t : T LN), to_T (to_T_inv t) = t.
  Parameter from_atom: atom -> term.
  Parameter from_ix: nat -> term.
  Parameter from_atom_Ret:
    from_atom = to_T_inv ○ @ret T ret_inst LN ○ Fr.
  Parameter from_ix_Ret:
    from_ix = to_T_inv ○ @ret T ret_inst LN ○ Bd.
End SyntaxSIG.

Module Adapter (M1: SyntaxSIG) <: SyntaxSIGHetero.

  Definition iterm := M1.term.
  Definition oterm := M1.term.
  Definition T := M1.T.
  Definition U := M1.T.
  Definition ret_inst := M1.ret_inst.
  Definition binddt_T_inst := M1.binddt_inst.
  Definition binddt_U_inst := M1.binddt_inst.
  Definition module_inst :=
    @DecoratedTraversableRightModule_DecoratedTraversableMonad
      nat T _ _ M1.ret_inst M1.binddt_inst M1.monad_inst.
  Definition to_T := M1.to_T.
  Definition to_T_inv := M1.to_T_inv.
  Definition to_T_iso := M1.to_T_iso.
  Definition to_T_iso_inv := M1.to_T_iso_inv.
  Definition to_U := M1.to_T.
  Definition to_U_inv := M1.to_T_inv.
  Definition to_U_iso := M1.to_T_iso.
  Definition to_U_iso_inv := M1.to_T_iso_inv.
  Definition from_atom := M1.from_atom.
  Definition from_ix := M1.from_ix.
  Definition from_atom_Ret := M1.from_atom_Ret.
  Definition from_ix_Ret := M1.from_ix_Ret.

End Adapter.

Module MakeTheory (Syntax: SyntaxSIG) <:
    (TheorySIG with Definition iterm := Syntax.term
     with Definition oterm := Syntax.term).

  Module Syntax_Hetero <: SyntaxSIGHetero
  := Adapter Syntax.

  Module Theory <:
    (TheorySIG with Definition iterm := Syntax.term
     with Definition oterm := Syntax.term)
    := MakeTheory_Hetero Syntax_Hetero.

  Include Theory.

End MakeTheory.
