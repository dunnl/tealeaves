From Tealeaves.Theory Require Export
  DecoratedTraversableMonad.
From Tealeaves.Backends.Common Require Export
  Names AtomSet AssocList.
From Tealeaves.Backends.LN Require Export
  LN Simplification.
Print Instances Traverse.

From Tealeaves.Simplification Require Export
  Simplification.

Import DecoratedTraversableMonad.UsefulInstances.
Import Classes.Kleisli.Theory.DecoratedTraversableMonad.

Module Notations.
  Export Categorical.Applicative.Notations. (* <⋆> *)
  Export Kleisli.Comonad.Notations.
  (* Export Kleisli.DecoratedFunctor.Notations. *)
  Export Kleisli.DecoratedMonad.Notations.
  Export Kleisli.TraversableFunctor.Notations.
  Export Kleisli.TraversableMonad.Notations.
  Export Kleisli.DecoratedTraversableFunctor.Notations.
  Export Kleisli.DecoratedTraversableMonad.Notations.
  Export Kleisli.DecoratedContainerFunctor.Notations. (* ∈d *)
  (* Export Kleisli.DecoratedContainerMonad.Notations. *)
  Export Categorical.ContainerFunctor.Notations. (* ∈ *)

  Export Product.Notations. (* × *)
  Export Monoid.Notations. (* Ƶ and ● *)
  Export Subset.Notations. (* ∪ *)
  Export List.ListNotations. (* [] :: *)

  (* Export LN.OpNotations. (* operations *) *)
  Export Common.AtomSet.Notations.
  Export Common.AssocList.Notations. (* one, ~ *)
End Notations.


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
    (LCb : oterm -> bool).
End TheorySIG.

Module MakeTheory_Hetero
  (Syntax: SyntaxSIGHetero) <: TheorySIG.
  Import Syntax.

  Definition iterm := Syntax.iterm.
  Definition oterm := Syntax.oterm.

  Import DecoratedTraversableMonad.UsefulInstances.

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
    fun x u => to_U_inv (close (U := U) x u).

  Definition subst : atom -> iterm -> oterm -> oterm :=
    fun x t u => to_U_inv (subst (T := T) (U := U) x t u).

  Definition free : oterm -> list atom :=
    fun u => free (U := U) u.

  Definition FV : oterm -> AtomSet.t :=
    fun u => FV (U := U) u.

  Definition LC : oterm -> Prop :=
    fun u => LC (U := U) u.

  Definition LCb : oterm -> bool :=
    fun u => LCb (U := U) u.

  Definition scoped : oterm -> AtomSet.t -> Prop :=
    fun t γ => FV t ⊆ γ.

  Definition subst_i : atom -> iterm -> iterm -> iterm :=
    fun x t u => to_T_inv (LN.subst (T := T) (U := T) x t u).

  Definition FV_i : iterm -> AtomSet.t :=
    fun t => LN.FV (U := T) t.

  Definition LC_i : iterm -> Prop :=
    fun u => LN.LC (U := T) u.

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
    LC u -> u '(t) = u.
  Proof.
    intros.
    unfold LC.
    unfold open.
    rewrite open_lc.
    - apply to_U_iso.
    - assumption.
  Qed.

  Theorem FV_subst_upper: forall x t u,
      FV (u '{x ~> t}) ⊆ FV u \\ {{x}} ∪ FV_i t.
  Proof.
    intros.
    unfold FV, FV_i, subst.
    rewrite to_U_iso_inv.
    rewrite FV_subst_upper.
    reflexivity.
  Qed.

  Theorem FV_subst_lower: forall t u x,
      FV u \\ {{ x }} ⊆ FV (u '{x ~> t}).
  Proof.
    intros.
    unfold FV, FV_i, subst.
    rewrite to_U_iso_inv.
    apply FV_subst_lower.
  Qed.

  Theorem close_open : forall x u,
      ~ x `in` FV u ->
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
    - rewrite free_iff_FV.
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
      LC_i t ->
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

  Theorem open_spec : forall u t x,
      ~ x `in` FV u ->
      u '(t) = u '(from_atom x) '{x ~> t}.
  Proof.
    intros.
    unfold close, open, subst.
    rewrite to_U_iso_inv.
    erewrite open_spec.
    - rewrite from_atom_Ret.
      rewrite to_T_iso_inv.
      reflexivity.
    - assumption.
  Qed.

  Theorem subst_open :  forall t1 t2 u x,
      LC_i t2 ->
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

  Theorem FV_open_upper : forall u t,
      FV (u '(t)) ⊆ FV u ∪ FV_i t.
  Proof.
    intros.
    unfold FV, open.
    rewrite to_U_iso_inv.
    rewrite FV_open_upper.
    reflexivity.
  Qed.

  Theorem FV_open_lower : forall t u,
      FV u ⊆ FV (u '(t)).
  Proof.
    intros.
    unfold FV, open.
    rewrite to_U_iso_inv.
    rewrite FV_open_lower.
    reflexivity.
  Qed.

  Theorem FV_close : forall u x,
      FV ('[x] u) [=] FV u \\ {{ x }}.
  Proof.
    intros.
    unfold FV, close.
    rewrite to_U_iso_inv.
    rewrite FV_close.
    reflexivity.
  Qed.

  Theorem nin_FV_close : forall u x,
      ~ x `in` FV ('[x] u).
  Proof.
    intros.
    unfold FV, close.
    rewrite to_U_iso_inv.
    apply nin_FV_close.
  Qed.

  Theorem FV_close1 : forall u x y,
      y <> x ->
      y `in` FV ('[x] u) <-> y `in` FV u.
  Proof.
    intros.
    unfold close, FV.
    rewrite to_U_iso_inv.
    rewrite <- free_iff_FV.
    rewrite in_free_close_iff.
    rewrite <- free_iff_FV.
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
    @DerivedInstances.DecoratedTraversableRightModule_DecoratedTraversableMonad
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
