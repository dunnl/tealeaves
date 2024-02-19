From Tealeaves.Misc Require Import
  NaturalNumbers.
From Tealeaves.Theory Require Import
  TraversableFunctor
  DecoratedTraversableMonad.

Import
  Product.Notations
  Monoid.Notations
  Batch.Notations
  List.ListNotations
  Subset.Notations
  Kleisli.Monad.Notations
  Kleisli.Comonad.Notations
  ContainerFunctor.Notations
  DecoratedMonad.Notations
  DecoratedContainerFunctor.Notations
  DecoratedTraversableMonad.Notations.

#[local] Generalizable Variables W T U.

Open Scope nat_scope.

(* Iterate an endofunction <<n>> times *)
Fixpoint iterate (n : nat) {A : Type} (f : A -> A) :=
  match n with
  | 0 => @id A
  | S n' => iterate n' f ∘ f
  end.

Lemma iterate_rw1 : forall (n : nat) {A : Type} (f : A -> A),
    iterate (S n) f = (iterate n f) ∘ f.
Proof.
  intros.
  cbn.
  reflexivity.
Qed.

(** ** De Bruijn operations as defined by Tealeaves *)
(******************************************************************************)
Module DB1.
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

    Definition cons (X : Type) : X -> (nat -> X) -> (nat -> X)  :=
      fun new sub n => match n with
                    | O => new
                    | S n' => sub n'
                    end.

    Definition renup (σ : nat -> nat) : nat -> nat :=
      cons nat 0 (S ∘ σ).

    Definition rename (σ : nat -> nat) : T nat -> T nat :=
      mapd (fun '(depth, ix) => iterate depth renup σ ix).

    Definition up (σ : nat -> T nat) : nat -> T nat :=
      cons (T nat) (ret 0) (rename S ∘ σ).

    Definition inst (σ : nat -> T nat) : T nat -> T nat :=
      bindd (fun '(depth, ix) => iterate depth up σ ix).

  End ops.
End DB1.

(** ** De Bruijn operations as defined by Tealeaves *)
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

    (* Increase free variables by a given amount. *)
    Definition shift (n : nat) (p : nat * nat) : nat :=
      match p with
      | pair depth ix => if Nat.ltb ix depth then ix else ix + n
      end.

    Definition scoot : nat -> (nat -> T nat) -> (nat -> T nat)  :=
      fun watermark sub ix =>
        if Nat.ltb ix watermark then ret ix
        else mapd (shift watermark) (sub (ix - watermark)).

    Definition open (sub : nat -> T nat) (t : T nat) : T nat :=
      bindd (fun '(depth, ix) => scoot depth sub ix) t.

    Lemma shift_zero : shift 0 = extract (W := (nat ×)).
    Proof.
      ext [a b]. unfold shift. destruct (Nat.ltb b a).
      - reflexivity.
      - cbn. lia.
    Qed.

  End ops.
End DB2.

Section equivalence.

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

  Lemma DB1_matches_DB2 : forall (t : T nat) (σ : nat -> T nat), DB1.inst σ t = DB2.open σ t.
  Proof.
    intros.
    unfold DB1.inst.
    unfold DB2.open.
    apply bindd_respectful.
    introv H_in.
    unfold DB2.scoot.
    compare naturals a and w.
    - pose (rw := PeanoNat.Nat.ltb_lt a w).
      rewrite <- rw in ineqp.
      rewrite ineqp.
  Admitted.

End equivalence.

  (*
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
*)


(** ** De Bruijn operations as defined by Tealeaves *)
(******************************************************************************)
Module DB3.
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

    Definition cons {X : Type} : X -> (nat -> X) -> (nat -> X)  :=
      fun new sub n => match n with
                    | O => new
                    | S n' => sub n'
                    end.

    Definition shift: nat -> T nat :=
      fun n => ret (T := T) (n + 1).

    Definition subst (σ : nat -> T nat) : T nat -> T nat :=
      bind σ.

    Lemma test: forall (a : T nat) (σ : nat -> T nat),
        (cons a σ) ⋆1 shift = σ.
    Proof.
      intros.
      unfold kc1.
      unfold shift.
      ext n.
      unfold compose.
      compose near (n + 1) on left.
      rewrite (kmon_bind0).
      unfold cons.
      remember (n + 1) as m.
      destruct m.
      + lia.
      + assert (n = m). lia.
        now subst.
    Qed.

    Lemma test2: forall (a : T nat) (σ ρ : nat -> T nat),
        ρ ⋆1 (cons a σ) = cons (subst ρ a) (ρ ⋆1 σ).
    Proof.
      intros.
      unfold kc1.
      ext n.
      unfold compose, cons.
      destruct n.
      - reflexivity.
      - reflexivity.
    Qed.

  End ops.
End DB3.
