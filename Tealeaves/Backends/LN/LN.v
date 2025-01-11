(** This files contains metatheorems for the locally nameless variables
 that closely parallel those of LNgen. *)
From Tealeaves.Backends.LN Require Export
  Atom AtomSet.
From Tealeaves.Misc Require Export
  NaturalNumbers.
From Tealeaves.Theory Require Import
  DecoratedTraversableMonad.

Import Coq.Init.Nat. (* Notation <? *)

Import
  List.ListNotations
  Product.Notations
  Monoid.Notations
  Batch.Notations
  Subset.Notations
  Kleisli.Monad.Notations
  Kleisli.Comonad.Notations
  ContainerFunctor.Notations
  DecoratedMonad.Notations
  DecoratedContainerFunctor.Notations
  DecoratedTraversableMonad.Notations
  LN.AtomSet.Notations.

#[local] Generalizable Variables T U.

(** * Locally nameless variables *)
(******************************************************************************)
Inductive LN :=
| Fr : atom -> LN
| Bd : nat -> LN.

Theorem eq_dec_LN : forall l1 l2 : LN, {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
  - compare values a and a0; auto.
  - compare values n and n0; auto.
Qed.

#[export] Instance EqDec_LN : EquivDec.EqDec LN eq := eq_dec_LN.

(** [compare_to_atom] is an induction principle for leaves that splits
      the <<Fr x>> case into subcases <<x = y>> and <<x <> y>> for
      some user-specified atom <<y>>. *)
Lemma compare_to_atom : forall x l (P : LN -> Prop),
    P (Fr x) ->
    (forall a : atom, a <> x -> P (Fr a)) ->
    (forall n : nat, P (Bd n)) ->
    P l.
Proof.
  introv case1 case2 case3. destruct l.
  - destruct_eq_args x a. auto.
  - auto.
Qed.

Tactic Notation "compare" constr(l) "to" "atom" constr(x) :=
  (induction l using (compare_to_atom x)).

(** * Locally nameless operations *)
(******************************************************************************)

(** ** Localized operations *)
(******************************************************************************)
Section locally_nameless_local_operations.

  Context
    `{Return T}.

  #[local] Arguments ret (T)%function_scope {Return} {A}%type_scope _.

  Definition free_loc : LN -> list atom :=
    fun l => match l with
          | Fr x => cons x List.nil
          | _ => List.nil
          end.

  Definition subst_loc (x : atom) (u : T LN) : LN -> T LN :=
    fun l => match l with
          | Fr y => if x == y then u else ret T (Fr y)
          | Bd n => ret T (Bd n)
          end.

  Definition open_loc (u : T LN) : nat * LN -> T LN :=
    fun p => match p with
          | (w, l) =>
              match l with
              | Fr x => ret T (Fr x)
              | Bd n =>
                  match Nat.compare n w with
                  | Gt => ret T (Bd (n - 1))
                  | Eq => u
                  | Lt => ret T (Bd n)
                  end
              end
          end.

  Definition is_opened : nat * LN -> Prop :=
    fun p =>
      match p with
      | (ctx, l) =>
          match l with
          | Fr y => False
          | Bd n => n = ctx
          end
      end.

  Definition close_loc (x : atom ) : nat * LN -> LN :=
    fun p => match p with
          | (w, l) =>
              match l with
              | Fr y => if x == y then Bd w else Fr y
              | Bd n =>
                  match n ?= w with
                  | Gt => Bd (S n)
                  | Eq => Bd (S n)
                  | Lt => Bd n
                  end
              end
          end.

  (** The argument <<n>> is appended the context---to define local
      closure we will take <<n = 0>>, but we can also consider more
      notions like ``local closure within a gap of 1 binder,'' which
      is useful for backend reasoning. **)
  Definition lc_loc (gap : nat) : nat * LN -> Prop :=
    fun p => match p with
          | (w, l) =>
              match l with
              | Fr x => True
              | Bd n => n < w + gap
              end
          end.

  Definition lcb_loc (gap : nat) : nat * LN -> bool :=
    fun p => match p with
          | (w, l) =>
              match l with
              | Fr x => true
              | Bd n => n <? w + gap
              end
          end.

  Definition level_loc: nat * LN -> nat :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => 0
            | Bd n => n + 1 - w
            end
          end.

End locally_nameless_local_operations.

(** ** Extended operations *)
(******************************************************************************)
Section locally_nameless_operations.

  Context
    `{DecoratedTraversableRightModuleFull nat T U}.

  Definition open (u : T LN) : U LN -> U LN  :=
    bindd (open_loc u).

  Definition close x : T LN -> T LN :=
    mapd (close_loc x).

  Definition subst x (u : T LN) : U LN -> U LN :=
    bind (subst_loc x u).

  Definition free : T LN -> list atom :=
    foldMap free_loc.

  Definition FV : T LN -> AtomSet.t :=
    LN.AtomSet.atoms ○ free.

  Definition LCnb (gap : nat) : U LN -> bool :=
    foldMapd (lcb_loc gap).

  Definition LCb : U LN -> bool :=
    LCnb 0.

  Definition LCn (gap : nat) : U LN -> Prop :=
    fun t => forall w l, (w, l) ∈d t -> lc_loc gap (w, l).

  Definition LC : U LN -> Prop :=
    LCn 0.

 Definition level : U LN -> nat :=
    foldMapd (op := Monoid_op_max) (unit := Monoid_unit_max)
      level_loc.

  Definition scoped : T LN -> AtomSet.t -> Prop :=
    fun t γ => FV t ⊆ γ.

End locally_nameless_operations.

(** ** Notations *)
(******************************************************************************)
Module OpNotations.
  Notation "t '{ x ~> u }" := (subst x u t) (at level 35).
  Notation "t ' ( u )" := (open u t) (at level 35, format "t  ' ( u )" ).
  Notation "' [ x ] t" := (close x t) (at level 35, format "' [ x ]  t" ).
End OpNotations.

Import OpNotations.

Section test_notations.

  Context
    `{DecoratedTraversableMonadFull nat T}.

  Context
    (t : T LN)
    (u : T LN)
    (x : atom)
    (n : nat).

  Check u '{x ~> t}.
  Check u '(t).
  Check '[x] u.

End test_notations.

(** * Lemmas for local reasoning *)
(******************************************************************************)
Create HintDb tea_local.

Tactic Notation "unfold_monoid" :=
  repeat unfold monoid_op, Monoid_op_plus,
  monoid_unit, Monoid_unit_zero in *.

Tactic Notation "unfold_lia" :=
  unfold_monoid; lia.

(** * Basic principles and lemmas *)
(******************************************************************************)
Section locally_nameless_basic_principles.

  Import Notations.

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
    `{ToSubset_T_inst : ToSubset T}
    `{ToBatch_T_inst : ToBatch T}
    `{! Compat_Map_Binddt nat T T}
    `{! Compat_Mapd_Binddt nat T T}
    `{! Compat_Traverse_Binddt nat T T}
    `{! Compat_Bind_Binddt nat T T}
    `{! Compat_Mapdt_Binddt nat T T}
    `{! Compat_Bindd_Binddt nat T T}
    `{! Compat_Bindt_Binddt nat T T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Context
    `{Map_U_inst : Map U}
    `{Mapd_U_inst : Mapd nat U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Mapdt_U_inst : Mapdt nat U}
    `{Bindd_U_inst : Bindd nat T U}
    `{Bindt_U_inst : Bindt T U}
    `{Binddt_U_inst : Binddt nat T U}
    `{ToSubset_U_inst : ToSubset U}
    `{ToBatch_U_inst : ToBatch U}
    `{! Compat_Map_Binddt nat T U}
    `{! Compat_Mapd_Binddt nat T U}
    `{! Compat_Traverse_Binddt nat T U}
    `{! Compat_Bind_Binddt nat T U}
    `{! Compat_Mapdt_Binddt nat T U}
    `{! Compat_Bindd_Binddt nat T U}
    `{! Compat_Bindt_Binddt nat T U}
    `{! Compat_ToSubset_Traverse U}
    `{! Compat_ToBatch_Traverse U}.

  Context
    `{Monad_inst : ! DecoratedTraversableMonad nat T}
      `{Module_inst : ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.

  Implicit Types (l : LN) (n : nat) (t : U LN) (x : atom).

  (** ** Local closure spec *)
  (******************************************************************************)
  Lemma LCn_spec: forall gap,
      LCn gap = Forall_ctx (lc_loc gap).
  Proof.
    intro. ext t.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.

  Definition LC_spec:
    LC = Forall_ctx (lc_loc 0).
  Proof.
    ext t.
    apply propositional_extensionality.
    rewrite forall_ctx_iff.
    reflexivity.
  Qed.
 Lemma lc_loc_mono: forall gap gap' w l,
      gap <= gap' ->
      lc_loc gap (w, l) ->
      lc_loc gap' (w, l).
  Proof.
    unfold lc_loc.
    unfold transparent tcs.
    destruct l; lia.
  Qed.

  Theorem local_closure_mono: forall gap gap' t,
      gap <= gap' ->
      LCn gap t ->
      LCn gap' t.
  Proof.
    unfold LCn. intros.
    apply (lc_loc_mono gap); auto.
  Qed.

  Lemma level1: forall (t: U LN),
    forall w n, (w, Bd n) ∈d t -> n < (w + level t)%nat.
  Proof.
    intros.
    enough (n + 1 - w <= level t).
    lia.
    change (n + 1 - w) with
      (level_loc (w, Bd n)).
    unfold level.
    apply (foldMapd_pompos (R := le)).
    assumption.
  Qed.

  Lemma level2: forall (t: U LN),
      LCn (level t) t.
  Proof.
    intros.
    unfold LCn.
    intros.
    unfold lc_loc.
    destruct l.
    - trivial.
    - unfold transparent tcs.
      apply level1.
      auto.
  Qed.

  Lemma level3: forall (gap: nat) (t: U LN),
      level t <= gap ->
      LCn gap t.
  Proof.
    intros. apply (local_closure_mono (level t)).
    assumption.
    apply level2.
  Qed.

  Lemma level4: forall (gap: nat) (t: U LN),
      LCn gap t ->
      level t <= gap.
  Proof.
    introv hyp.
    rewrite LCn_spec in hyp.
    unfold Forall_ctx in hyp.
    rewrite foldMapd_through_toctxlist in hyp.
    unfold level.
    rewrite foldMapd_through_toctxlist.
    unfold compose in *.
    induction (toctxlist t).
    - cbv. lia.
    - cbn.
      rewrite foldMap_list_eq in hyp.
      rewrite foldMap_list_cons in hyp.
      rewrite <- foldMap_list_eq in hyp.
      destruct hyp.
      apply PeanoNat.Nat.max_lub.
      + destruct a as [n l].
        unfold level_loc.
        unfold lc_loc in H.
        destruct l.
        * lia.
        * lia.
      + auto.
  Qed.

  Lemma level_iff: forall (gap: nat) (t: U LN),
      LCn gap t <-> level t <= gap.
  Proof.
    intros. split.
    - apply level4.
    - apply level3.
  Qed.

  Lemma local_closure_iff: forall (gap: nat) (t: U LN),
      LC t <-> level t = 0.
  Proof.
    intros. unfold LC.
    rewrite level_iff.
    lia.
  Qed.

  (** ** Reasoning principles for proving equalities *)
  (******************************************************************************)

  (** *** <<open>> *)
  (******************************************************************************)
  Lemma open_eq : forall t u1 u2,
      (forall w l, (w, l) ∈d t -> open_loc u1 (w, l) = open_loc u2 (w, l)) ->
      t '(u1) = t '(u2).
  Proof.
    intros. unfold open.
    now apply bindd_respectful.
  Qed.

  Lemma open_id : forall t u,
      (forall w l, (w, l) ∈d t -> open_loc u (w, l) = ret l) ->
      t '(u) = t.
  Proof.
    intros. unfold open.
    now apply bindd_respectful_id.
  Qed.

  Lemma open_ret : forall l (u : T LN),
      (ret l) '(u) = open_loc u (0, l).
  Proof.
    intros. unfold open.
    compose near l on left.
    rewrite kmond_bindd0.
    reflexivity.
  Qed.

  (** *** <<close>> *)
  (******************************************************************************)
  Lemma close_eq : forall t x y,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = close_loc y (w, l)) ->
      '[x] t = '[y] t.
  Proof.
    intros. unfold close.
    now apply mapd_respectful.
  Qed.

  Lemma close_id : forall t x,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = l) ->
      '[x] t = t.
  Proof.
    intros. unfold close.
    now apply mapd_respectful_id.
  Qed.

  Lemma close_ret : forall l x,
      '[x] (ret l) = ret (close_loc x (0, l)).
  Proof.
    intros. unfold close.
    compose near l on left.
    rewrite mapd_ret.
    reflexivity.
  Qed.

  (** *** <<subst>> *)
  (******************************************************************************)
  Lemma subst_eq : forall t x y (u1 u2 : T LN),
      (forall l, l ∈ t -> subst_loc x u1 l = subst_loc y u2 l) ->
      t '{x ~> u1} = t '{y ~> u2}.
  Proof.
    intros. unfold subst.
    now apply bind_respectful.
  Qed.

  Lemma subst_id : forall t x u,
      (forall l, l ∈ t -> subst_loc x u l = ret l) ->
      t '{x ~> u} = t.
  Proof.
    intros. unfold subst.
    now apply mod_bind_respectful_id.
  Qed.

  Lemma subst_ret : forall x l (u : T LN),
      (ret l) '{x ~> u} = subst_loc x u l.
  Proof.
    intros. unfold subst.
    compose near l on left.
    rewrite kmon_bind0.
    reflexivity.
  Qed.

  (** ** Occurrence analysis lemmas *)
  (******************************************************************************)

  (** *** <<open>> *)
  (******************************************************************************)
  Lemma ind_open_iff : forall l n u t,
      (n, l) ∈d t '(u) <-> exists n1 n2 l1,
        (n1, l1) ∈d t /\ (n2, l) ∈d open_loc u (n1, l1) /\ n = n1 ● n2.
  Proof.
    intros. unfold open.
    now rewrite ind_bindd_iff'.
  Qed.

  Lemma in_open_iff : forall l u t,
      l ∈ t '(u) <-> exists n1 l1,
        (n1, l1) ∈d t /\ l ∈ open_loc u (n1, l1).
  Proof.
    intros. unfold open.
    now rewrite in_bindd_iff.
  Qed.

  (** *** <<close>> *)
  (******************************************************************************)
  Lemma ind_close_iff : forall l n x t,
      (n, l) ∈d '[x] t <-> exists l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    rewrite ind_mapd_iff.
    easy.
  Qed.

  Lemma in_close_iff : forall l x t,
      l ∈ '[x] t <-> exists n l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite in_mapd_iff.
  Qed.

  (** *** <<subst>> *)
  (******************************************************************************)
  Lemma ind_subst_iff : forall n l u t x,
      (n, l) ∈d t '{x ~> u} <-> exists n1 n2 l1,
        (n1, l1) ∈d t /\ (n2, l) ∈d subst_loc x u l1 /\ n = n1 ● n2.
  Proof.
    intros. unfold subst.
    now rewrite ind_bind_iff'.
  Qed.

  Lemma in_subst_iff : forall l u t x,
      l ∈ t '{x ~> u} <-> exists l1,
       l1 ∈ t /\ l ∈ subst_loc x u l1.
  Proof.
    intros. unfold subst.
    now rewrite mod_in_bind_iff.
  Qed.

End locally_nameless_basic_principles.

(** * Utilities for reasoning at the leaves *)
(******************************************************************************)
Section locally_nameless_utilities.

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
     (op := Monoid_op_plus)}
    `{ToSubset_T_inst : ToSubset T}
    `{ToSubset_U_inst : ToSubset U}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToSubset_Traverse U}.

  Import Notations.

  (** ** (In)equalities between leaves *)
  (******************************************************************************)
  Lemma Fr_injective : forall (x y : atom),
      (Fr x = Fr y) <-> (x = y).
  Proof.
    intros. split; intro hyp.
    now injection hyp. now subst.
  Qed.

  Lemma Fr_injective_not_iff : forall (x y : atom),
      (Fr x <> Fr y) <-> (x <> y).
  Proof.
    intros. split; intro hyp; contradict hyp.
    now subst. now injection hyp.
  Qed.

  Lemma Fr_injective_not : forall (x y : atom),
      x <> y -> ~ (Fr x = Fr y).
  Proof.
    intros. now rewrite Fr_injective.
  Qed.

  Lemma Bd_neq_Fr : forall n x,
      (Bd n = Fr x) = False.
  Proof.
    introv. propext. discriminate. contradiction.
  Qed.

  (** ** [subst_loc] *)
  (******************************************************************************)
  Lemma subst_loc_eq : forall (u : T LN) x,
      subst_loc x u (Fr x) = u.
  Proof. intros. cbn. now compare values x and x. Qed.

  Lemma subst_loc_eq_impl : forall (u : T LN) x y,
      Fr x = y -> subst_loc x u y = u.
  Proof. intros. subst. now rewrite subst_loc_eq. Qed.

  Lemma subst_loc_fr_eq_impl : forall (u : T LN) x y,
      x = y -> subst_loc x u (Fr y) = u.
  Proof. intros. subst. now rewrite subst_loc_eq. Qed.

  Lemma subst_loc_neq : forall (u : T LN) x y,
      y <> x -> subst_loc x u (Fr y) = ret (Fr y).
  Proof. intros. cbn. now compare values x and y. Qed.

  Lemma subst_loc_b : forall u x n,
      subst_loc x u (Bd n) = ret (Bd n).
  Proof. reflexivity. Qed.

  Lemma subst_loc_fr_neq : forall (u : T LN) l x,
      Fr x <> l -> subst_loc x u l = ret l.
  Proof.
    introv neq. unfold subst_loc.
    destruct l as [a|?]; [compare values x and a | reflexivity ].
  Qed.

  (** ** [open_loc] *)
  (******************************************************************************)
  Lemma open_loc_lt : forall (u : T LN) w n,
      n < w -> open_loc u (w, Bd n) = ret (Bd n).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and w.
  Qed.

  Lemma open_loc_gt : forall (u : T LN) n w,
      n > w -> open_loc u (w, Bd n) = ret (Bd (n - 1)).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and w.
  Qed.

  Lemma open_loc_eq : forall w (u : T LN),
      open_loc u (w, Bd w) = u.
  Proof.
    introv. unfold open_loc. compare naturals w and w.
  Qed.

  Lemma open_loc_atom : forall (u : T LN) w x,
      open_loc u (w, Fr x) = ret (Fr x).
  Proof.
    reflexivity.
  Qed.

  (** ** [close_loc] *)
  (******************************************************************************)
  Lemma close_loc_neq : forall w x y,
      x <> y -> close_loc x (w, Fr y) = Fr y.
  Proof.
    intros. cbn. compare values x and y.
  Qed.

  Lemma close_loc_eq : forall w x,
      close_loc x (w, Fr x) = Bd w.
  Proof.
    intros. cbn. compare values x and x.
  Qed.

  Lemma close_loc_lt : forall x w n,
      n < w ->
      close_loc x (w, Bd n) = Bd n.
  Proof.
    intros. cbn. compare naturals n and w.
  Qed.

  Lemma close_loc_ge : forall x w n,
      n >= w ->
      close_loc x (w, Bd n) = Bd (S n).
  Proof.
    intros. cbn. compare naturals n and w.
  Qed.

  (** ** Local reasoning principles for LC *)
  (******************************************************************************)
  Lemma lc_loc_preincr: forall n m,
      lc_loc n ⦿ m =
        lc_loc (n + m).
  Proof.
    intros.
    ext [w l].
    destruct l.
    - reflexivity.
    - cbn. unfold_monoid. propext; lia.
  Qed.

  Lemma lc_loc_S: forall n,
      lc_loc n ⦿ 1 =
        lc_loc (S n).
  Proof.
    intros.
    rewrite lc_loc_preincr.
    fequal. lia.
  Qed.

  Lemma lc_loc_nBd: forall n w b,
      lc_loc n (w, Bd b) = (b < w + n).
  Proof.
    reflexivity.
  Qed.

  Lemma lc_loc_0Bd: forall w b,
      lc_loc 0 (w, Bd b) = (b < w).
  Proof.
    intros.
    cbn.
    unfold_monoid.
    propext; lia.
  Qed.

  Lemma lc_loc_00Bd: forall b,
      lc_loc 0 (0, Bd b) = False.
  Proof.
    intros.
    rewrite lc_loc_0Bd.
    propext; lia.
  Qed.

  Lemma lc_loc_Fr: forall n w x,
      lc_loc n (w, Fr x) = True.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma neq_symmetry : forall X (x y : X),
      (x <> y) = (y <> x).
  Proof.
    intros. propext; intro hyp; contradict hyp; congruence.
  Qed.

End locally_nameless_utilities.


Create HintDb subst_local.

#[export] Hint Rewrite
  @subst_loc_eq: subst_local.

#[export] Hint Rewrite
  @subst_loc_eq_impl
  @subst_loc_fr_eq_impl
  @subst_loc_b
  @subst_loc_neq
  @subst_loc_fr_neq
  using solve [auto]: subst_local.

Ltac simplify_subst_local :=
  autorewrite with subst_local.


#[export] Hint Rewrite @in_ret_iff @ind_ret_iff
     using typeclasses eauto : tea_local.

#[export] Hint Rewrite Fr_injective Fr_injective_not_iff Bd_neq_Fr : tea_local.
#[export] Hint Resolve Fr_injective_not : tea_local.

#[export] Hint Rewrite
     @subst_loc_eq (*@subst_in_ret*)
     using typeclasses eauto : tea_local.
#[export] Hint Rewrite
     @subst_loc_neq @subst_loc_b @subst_loc_fr_neq (*@subst_in_ret_neq*)
     using first [ typeclasses eauto | auto ] : tea_local.
#[export] Hint Rewrite
     @open_loc_lt @open_loc_gt
     using first [ typeclasses eauto | auto ] : tea_local.
#[export] Hint Rewrite
     @open_loc_eq @open_loc_atom
     using typeclasses eauto : tea_local.

Tactic Notation "simpl_local" := (autorewrite* with tea_local).

Ltac simplify_lc_loc :=
  match goal with
  | |- context[lc_loc ?n ⦿ 1] =>
      rewrite lc_loc_S
  | |- context[lc_loc ?n ⦿ ?m] =>
      rewrite lc_loc_preincr
  | |- context[lc_loc ?n (?w, Fr ?x)] =>
      rewrite lc_loc_Fr
  | |- context[lc_loc 0 (0, Bd ?b)] =>
      rewrite lc_loc_00Bd
  | |- context[lc_loc 0 (?w, Bd ?b)] =>
      rewrite lc_loc_0Bd
  | |- context[lc_loc ?n (?w, Bd ?b)] =>
      rewrite lc_loc_nBd
  end.

(** * Free variables *)
(******************************************************************************)
Section locally_nameless_free_variables.

  Import Notations.

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
    `{ToSubset_T_inst : ToSubset T}
    `{ToBatch_T_inst : ToBatch T}
    `{! Compat_Map_Binddt nat T T}
    `{! Compat_Mapd_Binddt nat T T}
    `{! Compat_Traverse_Binddt nat T T}
    `{! Compat_Bind_Binddt nat T T}
    `{! Compat_Mapdt_Binddt nat T T}
    `{! Compat_Bindd_Binddt nat T T}
    `{! Compat_Bindt_Binddt nat T T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Context
    `{Map_U_inst : Map U}
    `{Mapd_U_inst : Mapd nat U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Mapdt_U_inst : Mapdt nat U}
    `{Bindd_U_inst : Bindd nat T U}
    `{Bindt_U_inst : Bindt T U}
    `{Binddt_U_inst : Binddt nat T U}
    `{ToSubset_U_inst : ToSubset U}
    `{ToBatch_U_inst : ToBatch U}
    `{! Compat_Map_Binddt nat T U}
    `{! Compat_Mapd_Binddt nat T U}
    `{! Compat_Traverse_Binddt nat T U}
    `{! Compat_Bind_Binddt nat T U}
    `{! Compat_Mapdt_Binddt nat T U}
    `{! Compat_Bindd_Binddt nat T U}
    `{! Compat_Bindt_Binddt nat T U}
    `{! Compat_ToSubset_Traverse U}
    `{! Compat_ToBatch_Traverse U}.

  Context
    `{Monad_inst : ! DecoratedTraversableMonad nat T}
      `{Module_inst : ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.
  (** ** Free variables *)
  (******************************************************************************)

  (** *** Specifications for [free] and [FV] *)
  (******************************************************************************)
  Lemma in_free_iff_local : forall x l,
      x ∈ free_loc l = (Fr x = l).
  Proof.
    intros.
    destruct l.
    - cbv. propext.
      + intros [hyp|hyp].
        * now subst.
        * contradiction.
      + inversion 1. now left.
    - cbv. propext.
      + inversion 1.
      + inversion 1.
  Qed.

  Theorem in_free_iff : forall t x,
      x ∈ free (T := U) t = Fr x ∈ t.
  Proof.
    intros. unfold free.
    change_left ((element_of x ∘ foldMap free_loc) t).
    rewrite (foldMap_morphism
               (morphism := Monoid_Morphism_element_list atom x)
               (list atom) Prop (ϕ := element_of x)).
    rewrite (element_of_to_foldMap LN (Fr x)).
    fequal. ext l.
    apply in_free_iff_local.
  Qed.

  Theorem free_iff_FV : forall t x,
      x ∈ free t <-> x `in` FV t.
  Proof.
    intros.
    unfold FV.
    rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  Theorem in_free_iff_T_internal : forall t x,
      x ∈ free (T := T) t = Fr x ∈ t.
  Proof.
    intros. unfold free.
    change_left ((element_of x ∘ foldMap free_loc) t).
    rewrite (foldMap_morphism
               (morphism := Monoid_Morphism_element_list atom x)
               (list atom) Prop (ϕ := element_of x)).
    rewrite (element_of_to_foldMap LN (Fr x)).
    fequal. ext l.
    apply in_free_iff_local.
  Qed.

  (** *** Opening *)
  (******************************************************************************)
  Lemma free_open_iff : forall u t x,
      x ∈ free (t '(u)) <-> exists w l1,
        (w, l1) ∈d t /\ x ∈ free (open_loc u (w, l1)).
  Proof.
    intros.
    rewrite in_free_iff.
    setoid_rewrite (in_free_iff_T_internal).
    now rewrite in_open_iff.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma free_close_iff : forall t x y,
      y ∈ free ('[x] t) <-> exists w l1,
        (w, l1) ∈d t /\ close_loc x (w, l1) = Fr y.
  Proof.
    intros.
    rewrite in_free_iff.
    now rewrite in_close_iff.
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma free_subst_iff : forall u t x y,
      y ∈ free (t '{x ~> u}) <-> exists l1,
        l1 ∈ t /\ y ∈ free (subst_loc x u l1).
  Proof.
    intros.
    rewrite in_free_iff.
    setoid_rewrite in_free_iff_T_internal.
    now rewrite in_subst_iff.
  Qed.

  (** ** [Miscellaneous utilities] *)
  (******************************************************************************)
  Lemma ninf_in_neq : forall x l (t : U LN),
      ~ x ∈ free t ->
      l ∈ t ->
      Fr x <> l.
  Proof.
    introv hyp1 hyp2.
    rewrite in_free_iff in hyp1. destruct l.
    - injection. intros; subst.
      contradiction.
    - discriminate.
  Qed.

End locally_nameless_free_variables.

(** * Locally nameless metatheory *)
(******************************************************************************)
Section locally_nameless_metatheory.


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
    `{ToSubset_T_inst : ToSubset T}
    `{ToBatch_T_inst : ToBatch T}
    `{! Compat_Map_Binddt nat T T}
    `{! Compat_Mapd_Binddt nat T T}
    `{! Compat_Traverse_Binddt nat T T}
    `{! Compat_Bind_Binddt nat T T}
    `{! Compat_Mapdt_Binddt nat T T}
    `{! Compat_Bindd_Binddt nat T T}
    `{! Compat_Bindt_Binddt nat T T}
    `{! Compat_ToSubset_Traverse T}
    `{! Compat_ToBatch_Traverse T}.

  Context
    `{Map_U_inst : Map U}
    `{Mapd_U_inst : Mapd nat U}
    `{Traverse_U_inst : Traverse U}
    `{Bind_U_inst : Bind T U}
    `{Mapdt_U_inst : Mapdt nat U}
    `{Bindd_U_inst : Bindd nat T U}
    `{Bindt_U_inst : Bindt T U}
    `{Binddt_U_inst : Binddt nat T U}
    `{ToSubset_U_inst : ToSubset U}
    `{ToBatch_U_inst : ToBatch U}
    `{! Compat_Map_Binddt nat T U}
    `{! Compat_Mapd_Binddt nat T U}
    `{! Compat_Traverse_Binddt nat T U}
    `{! Compat_Bind_Binddt nat T U}
    `{! Compat_Mapdt_Binddt nat T U}
    `{! Compat_Bindd_Binddt nat T U}
    `{! Compat_Bindt_Binddt nat T U}
    `{! Compat_ToSubset_Traverse U}
    `{! Compat_ToBatch_Traverse U}.

  Context
    `{Monad_inst : ! DecoratedTraversableMonad nat T}
      `{Module_inst : ! DecoratedTraversableRightPreModule nat T U
                        (unit := Monoid_unit_zero)
                        (op := Monoid_op_plus)}.

  Open Scope set_scope.

  Implicit Types
           (l : LN) (p : LN)
           (x : atom) (t : U LN)
           (w : nat) (n : nat).

  (** ** LN analysis: substitution with contexts *)
  (******************************************************************************)
  Lemma ind_subst_loc_iff : forall l w p (u : T LN) x,
      (w, p) ∈d subst_loc x u l <->
      l <> Fr x /\ w = Ƶ /\ l = p \/ (* l is not replaced *)
      l = Fr x /\ (w, p) ∈d u. (* l is replaced *)
  Proof.
    introv. compare l to atom x; simpl_local; intuition.
  Qed.

  Theorem ind_subst_iff2 : forall w t u l x,
      (w, l) ∈d t '{x ~> u} <->
      (w, l) ∈d t /\ l <> Fr x \/
      exists w1 w2 : nat, (w1, Fr x) ∈d t /\ (w2, l) ∈d u /\ w = w1 ● w2.
  Proof.
    intros. rewrite ind_subst_iff.
    setoid_rewrite ind_subst_loc_iff. split.
    - intros [l' [n1 [n2 conditions]]].
      destruct conditions as [c1 [[c2|c2] c3]]; subst.
      + left. destructs c2; subst. now rewrite monoid_id_l.
      + right. destructs c2; subst. eauto.
    - intros [[? ?] | [n1 [n2 [? [? ?]]]]].
      + exists w (Ƶ : nat) l. rewrite monoid_id_l. splits; auto.
      + exists n1 n2 (Fr x). splits; auto.
  Qed.

  (** ** LN analysis: substitution without contexts *)
  (******************************************************************************)
  Lemma in_subst_loc_iff : forall l p (u : T LN) x,
      p ∈ subst_loc x u l <->
      l <> Fr x /\ l = p \/
      l = Fr x /\ p ∈ u.
  Proof.
    introv. compare l to atom x; autorewrite* with tea_local; intuition.
  Qed.

  Theorem in_subst_iff' : forall t u l x,
      l ∈ t '{x ~> u} <->
      l ∈ t /\ l <> Fr x \/
      Fr x ∈ t /\ l ∈ u.
  Proof with auto.
    intros. rewrite in_subst_iff.
    setoid_rewrite in_subst_loc_iff. split.
    - intros [? [? in_sub]].
      destruct in_sub as [[? heq] | [heq ?]]; subst...
    - intros [[? ?]|[? ?]]; eauto.
  Qed.

  (** ** Free variables after substitution *)
  (******************************************************************************)
  Corollary in_free_subst_iff : forall t u x y,
      y ∈ free (t '{x ~> u}) <->
      y ∈ free t /\ y <> x \/ x ∈ free t /\ y ∈ free u.
  Proof.
    intros.
    do 4 rewrite in_free_iff.
    rewrite in_subst_iff'.
    now simpl_local.
  Qed.

  Corollary in_FV_subst_iff : forall t u x y,
      y `in` FV (t '{x ~> u}) <->
      y `in` FV t /\ y <> x \/
      x `in` FV t /\ y `in` FV u.
  Proof.
    intros.
    do 4 rewrite <- free_iff_FV.
    rewrite in_free_subst_iff.
    reflexivity.
  Qed.

  (** ** Upper and lower bounds for leaves after substitution *)
  (******************************************************************************)
  Corollary in_subst_upper : forall t u l x,
      l ∈ t '{x ~> u} ->
      (l ∈ t /\ l <> Fr x) \/ l ∈ u.
  Proof.
    introv hin. rewrite in_subst_iff' in hin.
    intuition.
  Qed.

  Corollary in_free_subst_upper : forall t u x y,
      y ∈ free (t '{x ~> u}) ->
      (y ∈ free t /\ y <> x) \/ y ∈ free u.
  Proof.
    introv.
    do 3 rewrite in_free_iff.
    rewrite in_subst_iff'.
    rewrite Fr_injective_not_iff.
    tauto.
  Qed.

  (* LNgen 4: fv-subst-upper *)
  Corollary FV_subst_upper : forall t u x,
      FV (t '{x ~> u}) ⊆
              (FV t \\ {{x}} ∪ FV u)%set.
  Proof.
    intros t y x a.
    rewrite AtomSet.union_spec, AtomSet.diff_spec,
    AtomSet.singleton_spec.
    rewrite <- ?(free_iff_FV).
    apply in_free_subst_upper.
  Qed.

  Corollary in_subst_lower : forall t u l x,
      l ∈ t /\ l <> Fr x ->
      l ∈ t '{x ~> u}.
  Proof with auto.
    intros; rewrite in_subst_iff'...
  Qed.

  Corollary in_free_subst_lower : forall t (u : T LN) x y,
      y ∈ free t -> y <> x ->
      y ∈ free (t '{x ~> u}).
  Proof.
    setoid_rewrite in_free_iff. intros.
    apply in_subst_lower; now simpl_local.
  Qed.

  (* LNgen 5: fv-subst-lower *)
  Corollary FV_subst_lower : forall (t : T LN) u x,
      FV u \\ {{ x }} ⊆ FV (u '{x ~> t}).
  Proof.
    introv. intro a.
    rewrite AtomSet.diff_spec, AtomSet.singleton_spec.
    do 2 rewrite <- free_iff_FV.
    intros [? ?]. now apply in_free_subst_lower.
  Qed.

  Corollary scoped_subst : forall t (u : T LN) x γ1 γ2,
      scoped t γ1 ->
      scoped u γ2 ->
      scoped (t '{x ~> u}) (γ1 \\ {{x}} ∪ γ2).
  Proof.
    introv St Su. unfold scoped in *.
    etransitivity. apply FV_subst_upper. fsetdec.
  Qed.

  (** ** Substitution of fresh variables *)
  (******************************************************************************)
  Theorem subst_fresh : forall t x u,
      ~ x ∈ free t ->
      t '{x ~> u} = t.
  Proof.
    intros. apply subst_id. intros.
    assert (Fr x <> l) by (eapply ninf_in_neq; eauto).
    now simpl_local.
  Qed.

  Theorem subst_fresh_T : forall (t : T LN) x u,
      ~ x ∈ free t ->
      t '{x ~> u} = t.
  Proof.
    intros.
    apply subst_id. intros.
    assert (Fr x <> l) by (apply (ninf_in_neq x l t); eauto).
    now simpl_local.
  Qed.

  (* LNgen 7: subst-fresh-eq *)
  Corollary subst_fresh_set : forall t x u,
      ~ x `in` FV t ->
      t '{x ~> u} = t.
  Proof.
    setoid_rewrite <- free_iff_FV. apply subst_fresh.
  Qed.

  (* LNgen 6: fv-subst-fresh *)
  Corollary FV_subst_fresh : forall t x u,
      ~ x `in` FV t ->
             FV (t '{x ~> u}) = FV t.
  Proof.
    intros. rewrite subst_fresh_set; auto.
  Qed.

  (** ** Composing substitutions *)
  (******************************************************************************)
  Lemma subst_subst_local : forall (u1 : T LN) (u2 : T LN) x1 x2,
      ~ x1 ∈ free u2 ->
      x1 <> x2 ->
      subst_loc x2 u2 ⋆1 subst_loc x1 u1 =
    subst_loc x1 (subst x2 u2 u1) ⋆1 subst_loc x2 u2.
  Proof with try assumption.
    intros. ext l. unfold kc1, compose.
    change_left (subst x2 u2 (subst_loc x1 u1 l)).
    change_right (subst x1 (subst x2 u2 u1) (subst_loc x2 u2 l)).
    compare l to atom x1.
    - rewrite subst_loc_eq.
      rewrite subst_loc_neq...
      rewrite subst_ret.
      rewrite subst_loc_eq.
      reflexivity.
    - rewrite subst_loc_neq...
      compare values x2 and a.
      + rewrite subst_ret.
        rewrite subst_loc_eq.
        rewrite subst_fresh_T...
        reflexivity.
      + rewrite subst_ret.
        rewrite subst_loc_neq...
        rewrite subst_ret.
        rewrite subst_loc_neq...
        reflexivity.
    - rewrite subst_loc_b.
      rewrite subst_ret.
      rewrite subst_loc_b.
      rewrite subst_ret.
      rewrite subst_loc_b.
      reflexivity.
  Qed.

  (* LNgen 8: subst-subst *)
  Theorem subst_subst : forall u1 u2 t (x1 x2 : atom),
      ~ x1 ∈ free u2 ->
      x1 <> x2 ->
      t '{x1 ~> u1} '{x2 ~> u2} =
      t '{x2 ~> u2} '{x1 ~> u1 '{x2 ~> u2} }.
  Proof with try assumption.
    intros.
    unfold subst.
    compose near t.
    rewrite kmod_bind2.
    rewrite subst_subst_local...
    rewrite kmod_bind2.
    reflexivity.
  Qed.

  (** ** Commuting two substitutions *)
  (******************************************************************************)
  Corollary subst_subst_comm : forall u1 u2 t (x1 x2 : atom),
      x1 <> x2 ->
      ~ x1 ∈ free u2 ->
      ~ x2 ∈ free u1 ->
      t '{x1 ~> u1} '{x2 ~> u2} =
      t '{x2 ~> u2} '{x1 ~> u1}.
  Proof with try assumption.
    intros.
    rewrite subst_subst...
    rewrite (subst_fresh_T u1 x2 u2)...
    reflexivity.
  Qed.

  (** ** Local closure is preserved by substitution *)
  (******************************************************************************)
  Theorem subst_lc : forall u t x,
      LC t ->
      LC u ->
      LC (subst x u t).
  Proof.
    unfold LC. introv lct lcu hin.
    rewrite ind_subst_iff2 in hin.
    destruct hin as [[? ?] | [n1 [n2 [h1 [h2 h3]]]]].
    - auto.
    - subst. specialize (lcu n2 l h2).
      unfold lc_loc in *.
      destruct l; auto. unfold_monoid. lia.
  Qed.

  (** ** Decompose substitution into closing/opening *)
  (******************************************************************************)
  Lemma subst_spec_local : forall (u : T LN) w l x,
      subst_loc x u l =
      open_loc u (cobind (close_loc x) (w, l)).
  Proof.
    introv. compare l to atom x; autorewrite* with tea_local.
    - cbn. compare values x and x. unfold id.
      compare naturals w and w.
    - cbn. compare values x and a. (* todo fix fragile names *)
    - cbn. unfold id. compare naturals n and w.
      now compare naturals (S w) and w.
      now compare naturals (S n) and w.
  Qed.

  (* LNgen 9: subst-spec *)
  Theorem subst_spec : forall x u t,
      t '{x ~> u} = ('[x] t) '(u).
  Proof.
    intros. compose near t on right.
    unfold open, close, subst.
    rewrite (bindd_mapd).
    rewrite (bind_to_bindd).
    fequal. ext [w l].
    unfold compose; cbn.
    now erewrite subst_spec_local.
  Qed.

  (** ** Substitution when <<u>> is a LN **)
  (******************************************************************************)
  Definition subst_loc_LN x (u : LN) : LN -> LN :=
    fun l => match l with
          | Fr y => if x == y then u else Fr y
          | Bd n => Bd n
          end.

  Theorem subst_by_LN_spec : forall x l,
      subst x (ret l) = map (subst_loc_LN x l).
  Proof.
    intros. unfold subst. ext t.
    apply mod_bind_respectful_map.
    intros l' l'in.
    destruct l'.
    - cbn. compare values x and a.
    - reflexivity.
  Qed.

  (** ** Substitution by the same variable is the identity *)
  (******************************************************************************)
  Theorem subst_same : forall t x,
      t '{x ~> ret (Fr x)} = t.
  Proof.
    intros. apply subst_id.
    intros. compare l to atom x; now simpl_local.
  Qed.

  (** ** Free variables after variable closing *)
  (******************************************************************************)
  Lemma in_free_close_iff_loc1 : forall w l t x  y,
      (w, l) ∈d t ->
      close_loc x (w, l) = Fr y ->
      Fr y ∈ t /\ x <> y.
  Proof.
    introv lin heq. destruct l as [la | ln].
    - cbn in heq. destruct_eq_args x la.
      inverts heq.
      apply ind_implies_in in lin. tauto.
    - cbn in heq. compare_nats_args ln w; discriminate.
  Qed.

  Lemma in_free_close_iff_loc2 : forall t x y,
      x <> y ->
      Fr y ∈ t ->
      exists w l, (w, l) ∈d t /\ close_loc x (w, l) = Fr y.
  Proof.
    introv neq yin.
    rewrite (ind_iff_in) in yin. destruct yin as [w yin].
    exists w. exists (Fr y). cbn. compare values x and y.
  Qed.

  Theorem in_free_close_iff : forall t x y,
      y ∈ free ('[x] t) <-> y ∈ free t /\ x <> y.
  Proof.
    introv. rewrite (free_close_iff).
    rewrite (in_free_iff). split.
    - introv [? [? [? ?] ] ]. eauto using in_free_close_iff_loc1.
    - intros [? ?]. eauto using in_free_close_iff_loc2.
  Qed.

  Corollary in_free_close_iff1 : forall t x y,
      y <> x ->
      y ∈ free ('[x] t) <-> y ∈ free t.
  Proof.
    intros. rewrite in_free_close_iff. intuition.
  Qed.

  (* LNgen 3: fv-close *)
  Corollary FV_close : forall t x,
      FV ('[x] t) [=] FV t \\ {{ x }}.
  Proof.
    introv. intro a. rewrite AtomSet.diff_spec.
    rewrite <- 2(free_iff_FV). rewrite in_free_close_iff.
    rewrite AtomSet.singleton_spec. intuition.
  Qed.

  Corollary nin_free_close : forall t x,
      ~ (x ∈ free ('[x] t)).
  Proof.
    introv. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary nin_FV_close : forall t x,
      ~ (x `in` FV ('[x] t)).
  Proof.
    introv. rewrite <- free_iff_FV. apply nin_free_close.
  Qed.

  (** ** Variable closing and local closure *)
  (******************************************************************************)
  Theorem close_lc : forall t x,
      LC t ->
      LCn 1 (close x t).
  Proof.
    unfold LC. introv lct hin.
    rewrite ind_close_iff in hin.
    destruct hin as [l1 [? ?]]. compare l1 to atom x; subst.
    - cbn. compare values x and x. unfold_lia.
    - cbn. compare values x and a.
    - cbn. compare naturals n and w.
      + false.
        specialize (lct w (Bd w) ltac:(assumption)).
        cbn in lct. lia.
      + specialize (lct w (Bd n) ltac:(assumption)).
        cbn in lct. lia.
  Qed.

  (** ** Upper and lower bounds on free variables after opening *)
  (******************************************************************************)
  Lemma free_open_upper_local : forall t (u : T LN) w l x,
      l ∈ t ->
      x ∈ free (open_loc u (w, l)) ->
      (l = Fr x /\ x ∈ free t) \/
      x ∈ free u.
  Proof with auto.
    introv lin xin. rewrite in_free_iff in xin.
    rewrite 2(in_free_iff). destruct l as [y | n].
    - left. autorewrite with tea_local in xin. inverts xin...
    - right. cbn in xin. compare naturals n and w.
      { contradict xin. simpl_local. easy. }
      { assumption. }
      { contradict xin. simpl_local. easy. }
  Qed.

  Theorem free_open_upper : forall t (u : T LN) x,
      x ∈ free (t '(u)) ->
      x ∈ free t \/ x ∈ free u.
  Proof.
    introv xin.
    rewrite free_open_iff in xin.
    destruct xin as [w [l [hin ?]]].
    apply (ind_implies_in) in hin.
    enough ((l = Fr x /\ x ∈ free t) \/ x ∈ free u) by intuition.
    eauto using free_open_upper_local.
  Qed.

  (* LNgen 1: fv-open-upper *)
  Corollary FV_open_upper : forall t (u : T LN),
      FV (t '(u)) ⊆ FV t ∪ FV u.
  Proof.
    intros. intro a. rewrite AtomSet.union_spec.
    repeat rewrite <- (free_iff_FV).
    auto using free_open_upper.
  Qed.

  Theorem free_open_lower : forall t u x,
      x ∈ free t ->
      x ∈ free (t '(u)).
  Proof.
    introv xin.
    rewrite (in_free_iff) in xin.
    rewrite (ind_iff_in) in xin.
    destruct xin as [w xin].
    rewrite (free_open_iff).
    setoid_rewrite (in_free_iff).
    exists w (Fr x). now autorewrite with tea_local.
  Qed.

  (* LNgen 2: fv-open-lower *)
  Corollary FV_open_lower : forall t u,
      FV t ⊆ FV (t '(u)).
  Proof.
    intros. intro a. rewrite <- 2(free_iff_FV).
    apply free_open_lower.
  Qed.

  (** ** Opening a locally closed term is the identity *)
  (**************************************************************************)
  Lemma open_lc_local : forall (u : T LN) w l,
      lc_loc 0 (w, l) ->
      open_loc u (w, l) = ret l.
  Proof.
    introv hyp. destruct l as [a | n].
    - reflexivity.
    - cbn in *. compare naturals n and w; unfold_lia.
  Qed.

  Theorem open_lc : forall t u,
      LC t ->
      t '(u) = t.
  Proof.
    introv lc. apply open_id. introv lin.
    specialize (lc _ _ lin).
    destruct l; auto using open_lc_local.
  Qed.

  (** ** Opening followed by substitution *)
  (**************************************************************************)
  Lemma subst_open_local : forall u1 u2 x,
      LC u2 ->
      subst x u2 ∘ open_loc u1 =
      open_loc (u1 '{x ~> u2}) ⋆5 (subst_loc x u2 ∘ extract).
  Proof.
    introv lcu2. ext [w l]. unfold kc5.
    unfold preincr, compose; cbn. compare l to atom x.
    - rewrite subst_ret. cbn.
      compare values x and x. symmetry.
      apply (bindd_respectful_id).
      intros. destruct a.
      + reflexivity.
      + unfold LC, LCn, lc_loc in lcu2. cbn.
        compare naturals n and (w ● w0).
        { specialize (lcu2 _ _ ltac:(eauto)). cbn in lcu2. unfold_lia. }
        { specialize (lcu2 _ _ ltac:(eauto)). cbn in lcu2. unfold_lia. }
    - rewrite subst_ret. cbn. compare values x and a.
      compose near (Fr a).
      now rewrite (kmond_bindd0).
    - compare naturals n and w; cbn.
      + rewrite subst_ret. compose near (Bd n) on right.
        rewrite (kmond_bindd0); unfold compose. cbn.
        rewrite monoid_id_l. compare naturals n and w.
      + compose near (Bd w) on right.
        rewrite (kmond_bindd0). unfold compose. cbn.
        rewrite monoid_id_l. compare naturals w and w.
      + rewrite subst_ret.
        compose near (Bd n) on right.
        rewrite (kmond_bindd0). unfold compose. cbn.
        rewrite monoid_id_l. compare naturals n and w.
  Qed.


  (* LNgen 10: subst-open *)
  Theorem subst_open :  forall u1 u2 t x,
      LC u2 ->
      t '(u1) '{x ~> u2} =
      t '{x ~> u2} '(u1 '{x ~> u2}).
  Proof.
    introv lc.
    compose near t.
    unfold open, subst at 1 3.
    rewrite (bind_bindd).
    rewrite (bindd_bind).
    fequal.
    change_left (subst x u2 ∘ open_loc u1).
    #[local] Set Keyed Unification.
    rewrite subst_open_local; [|auto].
    #[local] Unset Keyed Unification.
    now ext [w t'].
  Qed.

  (** ** Closing followed by substitution *)
  (**************************************************************************)
  Lemma close_notin_FV: forall y (u: T LN) depth,
      LC u ->
      ~ (y `in` FV u) ->
      mapd (close_loc y ⦿ depth) u = u.
  Proof.
    introv HLC Hnin.
    change u with (id u) at 2.
    rewrite <- dfun_mapd1.
    apply mapd_respectful.
    introv Hin.
    compare a to atom y.
    - false.
      apply ind_implies_in in Hin.
      rewrite <- free_iff_FV in Hnin.
      rewrite in_free_iff in Hnin.
      easy.
    - cbn. compare values a and a.
      destruct (@eq_dec Atom.atom _ y a). false.
      easy.
    - cbn. unfold transparent tcs.
      unfold LC in HLC.
      unfold LCn in HLC.
      specialize (HLC _ _ Hin).
      cbn in HLC.
      compare naturals n and (depth + e)%nat.
  Qed.

  Lemma subst_close_local : forall x y u depth l,
      x <> y ->
      ~ y `in` FV u ->
      LC u ->
      subst_loc x u (close_loc y (depth, l)) =
        mapd (close_loc y ⦿ depth) (subst_loc x u l).
  Proof.
    introv Hneq lc Hnotin.
    compare l to atom y.
    - rewrite close_loc_eq.
      compare values x and y.
      rewrite subst_loc_neq; auto.
      rewrite subst_loc_b.
      compose near (Fr y) on right.
      rewrite mapd_ret.
      reassociate -> on right.
      rewrite preincr_ret.
      unfold compose. cbn.
      now compare values y and y.
    - rewrite close_loc_neq; auto.
      compare values x and a.
      + rewrite subst_loc_eq.
        rewrite close_notin_FV; auto.
      + rewrite subst_loc_neq; auto.
        compose near (Fr a) on right.
        rewrite mapd_ret.
        reassociate -> on right.
        rewrite preincr_ret.
        unfold compose; cbn.
        destruct_eq_args y a.
    - cbn.
      compose near (Bd n) on right.
      rewrite mapd_ret.
      reassociate -> on right.
      rewrite preincr_ret.
      unfold compose; cbn.
      compare naturals n and depth.
  Qed.

  (* LNgen 13: subst-close *)
  Theorem subst_close :  forall (u: T LN) (t: U LN) x y,
      x <> y ->
      ~ y `in` FV u ->
      LC u ->
      ('[y] t) '{x ~> u} =
        '[y] (t '{x ~> u}).
  Proof.
    introv Hneq lc Hnotin.
    compose near t.
    unfold close, subst.
    rewrite (bind_mapd).
    rewrite (mapd_bind).
    fequal. unfold compose.
    ext [depth l].
    apply subst_close_local; auto.
  Qed.

  (** ** Decompose opening into variable opening followed by substitution *)
  (**************************************************************************)
  Lemma open_spec_local : forall u x w l,
      l <> Fr x ->
      (subst x u ∘ open_loc (ret (Fr x))) (w, l) =
      open_loc u (w, l).
  Proof.
    introv neq. unfold compose. compare l to atom x.
    - contradiction.
    - autorewrite with tea_local. rewrite subst_ret.
      now rewrite subst_loc_neq.
    - cbn. compare naturals n and w.
      now rewrite subst_ret.
      now rewrite subst_ret, subst_loc_eq.
      now rewrite subst_ret, subst_loc_b.
  Qed.

  (* This theorem would be easy to prove with [subst_open_eq], but
   applying that theorem would introduce a local closure hypothesis
   for <<u>> that is not actually required for our purposes. *)
  (* LNgen 14: subst-intro *)
  Theorem open_spec : forall u t x,
      ~ x `in` FV t ->
      t '(u) = t '(ret (Fr x)) '{x ~> u}.
  Proof.
    introv fresh. compose near t on right.
    unfold subst, open.
    rewrite (bind_bindd).
    apply (bindd_respectful). introv hin.
    assert (a <> Fr x).
    { apply (ind_implies_in) in hin.
      rewrite <- free_iff_FV in fresh.
      eapply ninf_in_neq in fresh; eauto. }
    now rewrite <- (open_spec_local u x).
  Qed.

  (** ** Opening by a variable, followed by non-equal substitution *)
  (**************************************************************************)
  Lemma subst_open_var_loc : forall u x y,
      x <> y ->
      LC u ->
      subst x u ∘ open_loc (ret (Fr y)) =
      open_loc (ret (Fr y)) ⋆5 (subst_loc x u ∘ extract).
  Proof with auto.
    introv neq lc. rewrite subst_open_local...
    rewrite subst_ret. cbn. compare values x and y.
  Qed.

  (* LNgen 11: subst-open-var *)
  Theorem subst_open_var : forall u t x y,
      x <> y ->
      LC u ->
      t '(ret (Fr y)) '{x ~> u} =
      t '{x ~> u} '(ret (Fr y)).
  Proof.
    introv neq lc. compose near t.
    unfold open, subst.
    rewrite (bind_bindd), (bindd_bind).
    fequal.
    change_left (subst x u ∘ open_loc (ret (Fr y))).
    #[local] Set Keyed Unification.
    rewrite subst_open_var_loc; auto.
    #[local] Unset Keyed Unification.
    now ext [w t'].
  Qed.

  (* LNgen 12: doesn't make sense here because it mentions concrete syntax *)

  (** ** Closing, followed by opening *)
  (**************************************************************************)
  Lemma open_close_local : forall x w l,
      (open_loc (ret (Fr x)) ⋆4 close_loc x)
      (w, l) = ret l.
  Proof.
    intros. cbn. unfold id. compare l to atom x.
    - compare values x and x. compare naturals w and w.
    - compare values x and a.
    - compare naturals n and w.
      compare naturals (S w) and w.
      compare naturals (S n) and w.
  Qed.

  (* LNgen 15: open_close *)
  Theorem open_close : forall x t,
      ('[x] t) '(ret (Fr x)) = t.
  Proof.
    intros. compose near t on left.
    unfold open, close.
    rewrite (bindd_mapd).
    apply (bindd_respectful_id); intros.
    auto using open_close_local.
  Qed.

  (** ** Opening by a LN reduces to an [mapkr] *)
  Definition open_LN_loc (u : LN) : nat * LN -> LN :=
    fun wl => match wl with
           | (w, l) =>
             match l with
             | Fr x => Fr x
             | Bd n =>
               match Nat.compare n w with
               | Gt => Bd (n - 1)
               | Eq => u
               | Lt => Bd n
               end
             end
           end.

  Lemma open_LN_loc_spec: forall (x: LN),
      open_loc (ret x) = ret (T := T) ∘ open_LN_loc x.
  Proof.
    intros. ext [depth l]. unfold compose.
    destruct l.
    - cbn. reflexivity.
    - cbn. compare naturals n and depth.
  Qed.

  Lemma open_by_LN_spec : forall l,
      open (ret l) = mapd (open_LN_loc l).
  Proof.
    intros. unfold open. ext t.
    apply (bindd_respectful_mapd).
    intros w l' l'in. destruct l'.
    - reflexivity.
    - cbn. compare naturals n and w.
  Qed.

  (** ** Opening, followed by closing *)
  (**************************************************************************)
  Lemma close_open_local : forall x w l,
      l <> Fr x ->
      (close_loc x ⋆4 open_LN_loc (Fr x)) (w, l) = l.
  Proof.
    introv neq. cbn. unfold id. compare l to atom x.
    - contradiction.
    - unfold compose; cbn. now compare values x and a.
    - unfold compose; cbn.
      compare naturals n and w. compare values x and x.
      compare naturals (n - 1) and w.
  Qed.

  (* LNgen 16: close_open *)
  Theorem close_open : forall x t,
      ~ x ∈ free t ->
      '[x] (t '(ret (Fr x))) = t.
  Proof.
    introv fresh. compose near t on left.
    rewrite open_by_LN_spec. unfold close.
    rewrite (dfun_mapd2).
    apply (mapd_respectful_id).
    intros w l lin.
    assert (l <> Fr x).
    { rewrite neq_symmetry. apply (ind_implies_in) in lin.
      eauto using (ninf_in_neq (T := T)). }
    now apply close_open_local.
  Qed.

  (** ** Opening and local closure *)
  (**************************************************************************)
  Lemma open_lcn_1 : forall n t u,
      LC u ->
      LCn n t ->
      LCn (n - 1) (t '(u)).
  Proof.
    unfold LCn.
    introv lcu lct Hin. rewrite ind_open_iff in Hin.
    destruct Hin as [n1 [n2 [l1 [h1 [h2 h3]]]]].
    destruct l1.
    - cbn in h2. rewrite (ind_ret_iff) in h2.
      destruct h2; subst. cbn. trivial.
    - specialize (lct _ _ h1). cbn in h2. compare naturals n0 and n1.
      + rewrite (ind_ret_iff) in h2; destruct h2; subst.
        cbn. unfold_monoid. lia.
      + specialize (lcu n2 l h2). unfold lc_loc in *.
        destruct l; [trivial|]. unfold_monoid. lia.
      + rewrite (ind_ret_iff) in h2. destruct h2; subst.
        unfold lc_loc in *. unfold_lia.
  Qed.

  Lemma open_lcn_2 : forall n t u,
      n > 0 ->
      LC u ->
      LCn (n - 1) (t '(u)) ->
      LCn n t.
  Proof.
    unfold LCn.
    introv ngt lcu lct Hin. setoid_rewrite (ind_open_iff) in lct.
    destruct l.
    - cbv. trivial.
    - compare naturals n0 and w.
      + specialize (lct w (Bd n0)).
        lapply lct.
        { cbn; unfold_lia. }
        { exists w (Ƶ : nat) (Bd n0).
          split; auto. cbn. compare naturals n0 and w.
          rewrite (ind_ret_iff). now simpl_monoid. }
      + cbn. unfold_lia.
      + cbn. specialize (lct w (Bd (n0 - 1))).
        lapply lct.
        { cbn; unfold_lia. }
        { exists w (Ƶ : nat) (Bd n0).
          split; auto. cbn. compare naturals n0 and w.
          rewrite (ind_ret_iff). now simpl_monoid. }
  Qed.

  Theorem open_lcn_iff : forall n t u,
      n > 0 ->
      LC u ->
      LCn n t <->
      LCn (n - 1) (t '(u)).
  Proof.
    intros; intuition (eauto using open_lcn_1, open_lcn_2).
  Qed.

  Corollary open_var_lcn : forall n t x,
      n > 0 ->
      LCn n t <->
      LCn (n - 1) (t '(ret (Fr x))).
  Proof.
    intros. apply open_lcn_iff. auto.
    intros w l hin. rewrite (ind_ret_iff) in hin.
    destruct hin; subst. cbv. trivial.
  Qed.

  Corollary open_lcn_iff_1 : forall t u,
      LC u ->
      LCn 1 t <->
      LC (t '(u)).
  Proof.
    intros. unfold LC.
    change 0 with (1 - 1).
    rewrite <- open_lcn_iff; auto.
    reflexivity.
  Qed.

  Corollary open_var_lcn_1 : forall t x,
      LCn 1 t <->
      LC (t '(ret (Fr x))).
  Proof.
    intros. unfold LC.
    change 0 with (1 - 1).
    rewrite <- open_var_lcn; auto.
    reflexivity.
  Qed.

  (** ** Injectivity of opening *)
  (******************************************************************************)

  (* LNgen 17: open-inj *)
  Lemma open_inj: forall (x: atom) (t u: U LN),
      ~ x `in` (FV t ∪ FV u) ->
      t '(ret (Fr x)) = u '(ret (Fr x)) ->
      t = u.
  Proof.
    introv Hnin Heq.
    rewrite open_by_LN_spec in Heq.
    apply (mapd_injective2 (open_LN_loc (Fr x))); auto.
    intros e a1 a2 Hint1 Hint2 Heq_loc.
    assert (Heq_loc2:
             open_loc (ret (T := T) (Fr x)) (e, a1) =
               open_loc (ret (Fr x)) (e, a2)).
    { rewrite open_LN_loc_spec.
      unfold compose. fequal. rewrite Heq_loc. reflexivity. }
    enough (Hneq: a1 <> Fr x /\ a2 <> Fr x).
    { destruct Hneq.
      cbn in Heq_loc.
      destruct a1.
      { destruct a2.
        { now inversion Heq_loc. }
        { compare naturals n and e; false. }
      }
      { destruct a2.
        { compare naturals n and e; false. }
        { compare naturals n and e.
          { compare naturals n0 and e.
            - now inversion Heq_loc.
            - false.
            - inversion Heq_loc. lia.
          }
          { compare naturals n0 and e.
            - now inversion Heq_loc.
            - false.
          }
          { compare naturals n0 and e.
            - inversion Heq_loc. lia.
            - false.
            - inversion Heq_loc. lia. }
        }
      }
    }
    split.
    - assert (cut: ~ (x `in` FV t)) by fsetdec.
      rewrite <- free_iff_FV in cut.
      apply ind_implies_in in Hint1.
      eapply ninf_in_neq in Hint1; eauto.
    - assert (cut: ~ (x `in` FV u)) by fsetdec.
      rewrite <- free_iff_FV in cut.
      apply ind_implies_in in Hint2.
      eapply ninf_in_neq in Hint2; eauto.
  Qed.

  (* LNgen 17: close-inj *)
  Lemma close_inj: forall (x: atom) (t u: U LN),
      '[x] t = '[x]  u ->
      t = u.
  Proof.
    introv premise.
    apply (mapd_injective2 (close_loc x)); auto.
    intros e a1 a2 Hint1 Hint2 Heq_loc.
    cbn in Heq_loc.
    compare a1 to atom x.
    - compare values x and x.
      compare a2 to atom x.
      + reflexivity.
      + compare values x and a.
      + compare naturals n and e.
        { inversion Heq_loc. lia. }
        { inversion Heq_loc. lia. }
        { inversion Heq_loc. lia. }
    - compare values x and a.
      compare a2 to atom x.
      compare values x and x.
      compare values x and a0.
      compare naturals n and e.
      { false. }
      { false. }
      { false. }
    - compare a2 to atom x.
      { compare naturals n and e.
        compare values x and x.
        { inversion Heq_loc. lia. }
        { compare values x and x.
          inversion Heq_loc. lia. }
        { compare values x and x.
          inversion Heq_loc. lia. }
      }
      { compare naturals n and e.
        destruct (@eq_dec Atom.atom _ x a).
        { inversion Heq_loc. lia. }
        { inversion Heq_loc. }
        { compare values x and a. }
        destruct (@eq_dec Atom.atom _ x a).
        { inversion Heq_loc. lia. }
        { inversion Heq_loc. }
      }
      { compare naturals n and e;
          compare naturals n0 and e;
          inversion Heq_loc; try lia; easy.
      }
  Qed.

End locally_nameless_metatheory.
