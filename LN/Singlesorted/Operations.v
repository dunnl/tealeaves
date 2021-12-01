From Tealeaves Require Import
     Util.Prelude Util.EqDec_eq
     LN.Atom LN.AtomSet LN.Leaf
     Singlesorted.Classes.DecoratedTraversableModule.

Import DecoratedTraversableMonad.Notations.
Import LN.AtomSet.Notations.
Open Scope tealeaves_scope.
Open Scope set_scope.

(** * Operations for locally nameless *)
(******************************************************************************)

(** ** Local operations *)
(******************************************************************************)
Section locally_nameless_local_operations.

  Context
    `{Return T}.

  Definition free_loc : leaf -> list atom :=
    fun l => match l with
          | Fr x => cons x List.nil
          | _ => List.nil
          end.

  Definition subst_loc (x : atom) (u : T leaf) : leaf -> T leaf :=
    fun l => match l with
          | Fr y => if x == y then u else ret T (Fr y)
          | Bd n => ret T (Bd n)
          end.

  Definition open_loc (u : T leaf) : nat * leaf -> T leaf :=
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

  Definition is_opened : nat * leaf -> Prop :=
    fun p =>
      match p with
      | (ctx, l) =>
        match l with
        | Fr y => False
        | Bd n => n = ctx
        end
      end.

  Definition close_loc (x : atom ) : nat * leaf -> leaf :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr y => if x == y then Bd w else Fr y
            | Bd n =>
              match Nat.compare n w with
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
  Definition is_bound_or_free (gap : nat) : nat * leaf -> Prop :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => True
            | Bd n => n < w ● gap
            end
          end.

End locally_nameless_local_operations.

(** ** Lifted operations *)
(******************************************************************************)
Section locally_nameless_operations.

  Context
    (F : Type -> Type)
    `{DecoratedTraversableModule nat F T}.

  Definition open (u : T leaf) : F leaf -> F leaf  :=
    subd F (open_loc u).

  Definition close x : F leaf -> F leaf :=
    fmapd F (close_loc x).

  Definition subst x (u : T leaf) : F leaf -> F leaf :=
    sub F (subst_loc x u).

  Definition free : F leaf -> list atom :=
    fun t => bind list free_loc (tolist F t).

  Definition freeset : F leaf -> AtomSet.t :=
    fun t => LN.AtomSet.atoms (free t).

  Definition locally_closed_gap (gap : nat) : F leaf -> Prop :=
    fun t => forall w l, (w, l) ∈d t -> is_bound_or_free gap (w, l).

  Definition locally_closed : F leaf -> Prop :=
    locally_closed_gap 0.

  Definition scoped : F leaf -> AtomSet.t -> Prop :=
    fun t γ => freeset t ⊆ γ.

End locally_nameless_operations.

(** ** Notations *)
(******************************************************************************)
Module Notations.
  Notation "t '{ x ~> u }" := (subst _ x u t) (at level 35).
  Notation "t '( u )" := (open _ u t) (at level 35).
  Notation "'[ x ] t" := (close _ x t) (at level 35).
End Notations.

(** ** Specialized reasoning principles for the operations *)
(******************************************************************************)
Section locally_nameless_basic_principles.

  Section test_notations.

    Import Notations.

    Context
      `{DecoratedTraversableModule nat F T}.

    Context
      (t : T leaf)
      (u : F leaf)
      (x : atom)
      (n : nat).

    Check u '{x ~> t}.
    Check u '(t).
    Check '[ x ] u.

  End test_notations.

  Import Notations.

  Context
    `{DecoratedTraversableModule nat (unit := Monoid_unit_zero)
                                 (op := Monoid_op_plus) F T}.

  Implicit Types (l : leaf) (n : nat) (t : F leaf) (x : atom).

  (** ** Identity and equality lemms for operations *)
  (******************************************************************************)
  Lemma open_eq : forall t u1 u2,
      (forall w l, (w, l) ∈d t -> open_loc u1 (w, l) = open_loc u2 (w, l)) ->
      t '(u1) = t '(u2).
  Proof.
    intros. unfold open.
    now apply (SetlikeModule.subd_respectful F).
  Qed.

  Lemma open_id : forall t u,
      (forall w l, (w, l) ∈d t -> open_loc u (w, l) = ret T l) ->
      t '(u) = t.
  Proof.
    intros. unfold open.
    now apply (SetlikeModule.subd_respectful_id F).
  Qed.

  Lemma subst_eq : forall t x y u1 u2,
      (forall l, l ∈ t -> subst_loc x u1 l = subst_loc y u2 l) ->
      t '{x ~> u1} = t '{y ~> u2}.
  Proof.
    intros. unfold subst.
    now apply (SetlikeModule.sub_respectful F T).
  Qed.

  Lemma subst_id : forall t x u,
      (forall l, l ∈ t -> subst_loc x u l = ret T l) ->
      t '{x ~> u} = t.
  Proof.
    intros. unfold subst.
    now apply (SetlikeModule.sub_respectful_id F T).
  Qed.

  Lemma close_eq : forall t x y,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = close_loc y (w, l)) ->
      '[x] t = '[y] t.
  Proof.
    intros. unfold close.
    now apply (fmapd_respectful F).
  Qed.

  Lemma close_id : forall t x,
      (forall w l, (w, l) ∈d t -> close_loc x (w, l) = l) ->
      '[x] t = t.
  Proof.
    intros. unfold close.
    now apply (fmapd_respectful_id F).
  Qed.

  (** ** Context-sensitive leaf analysis of operations *)
  (******************************************************************************)

  (** *** Opening *)
  (******************************************************************************)
  Lemma ind_open_iff : forall l n u t,
      (n, l) ∈d t '(u) <-> exists l1 n1 n2,
        (n1, l1) ∈d t /\ (n2, l) ∈d open_loc u (n1, l1) /\ n = n1 ● n2.
  Proof.
    intros. unfold open.
    now rewrite (SetlikeModule.ind_subd_iff F).
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma ind_close_iff : forall l n x t,
      (n, l) ∈d '[x] t <-> exists l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite (ind_fmapd_iff F).
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma ind_subst_iff : forall n l u t x,
      (n, l) ∈d t '{x ~> u} <-> exists l1 n1 n2,
        (n1, l1) ∈d t /\ (n2, l) ∈d subst_loc x u l1 /\ n = n1 ● n2.
  Proof.
    intros. unfold subst.
    now rewrite (SetlikeModule.ind_sub_iff F).
  Qed.

  (** ** Context-agnostic leaf analysis of operations *)
  (******************************************************************************)

  (** *** Opening *)
  (******************************************************************************)
  Lemma in_open_iff : forall l u t,
      l ∈ t '(u) <-> exists l1 n1,
        (n1, l1) ∈d t /\ l ∈ open_loc u (n1, l1).
  Proof.
    intros. unfold open.
    now rewrite (SetlikeModule.in_subd_iff F).
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma in_close_iff : forall l x t,
      l ∈ '[x] t <-> exists n l1,
        (n, l1) ∈d t /\ close_loc x (n, l1) = l.
  Proof.
    intros. unfold close.
    now rewrite (in_fmapd_iff F).
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma in_subst_iff : forall l u t x,
      l ∈ t '{x ~> u} <-> exists l1,
       l1 ∈ t /\ l ∈ subst_loc x u l1.
  Proof.
    intros. unfold subst.
    now rewrite (SetlikeModule.in_sub_iff F T).
  Qed.

  (** ** Free variables *)
  (******************************************************************************)

  (** *** Specifications for [free] and [freeset] *)
  (******************************************************************************)
  Theorem in_free_iff : forall (t : F leaf) (x : atom),
      x ∈ free F t <-> Fr x ∈ t.
  Proof.
    intros. unfold free. rewrite (in_bind_iff list). split.
    - intros [l ?]. destruct l.
      + rewrite in_iff_in_list. cbn in *.
        cut (a = x). now intro; subst. tauto.
      + cbn in *. tauto.
    - exists (Fr x). rewrite <- (in_iff_in_list).
      cbn. tauto.
  Qed.

  Theorem in_free_iff_T : forall (t : T leaf) (x : atom),
      x ∈ free T t <-> Fr x ∈ t.
  Proof.
    intros. unfold free. rewrite (in_bind_iff list). split.
    - intros [l ?]. destruct l.
      + rewrite in_iff_in_list. cbn in *.
        cut (a = x). now intro; subst. tauto.
      + cbn in *. tauto.
    - exists (Fr x). rewrite <- (in_iff_in_list).
      cbn. tauto.
  Qed.

  Theorem free_iff_freeset : forall (t : F leaf) (x : atom),
      x ∈ free F t <-> x ∈@ freeset F t.
  Proof.
    intros. unfold freeset. rewrite <- in_atoms_iff.
    reflexivity.
  Qed.

  (** *** Opening *)
  (******************************************************************************)
  Lemma free_open_iff : forall u t x,
      x ∈ free F (t '(u)) <-> exists l1 w,
        (w, l1) ∈d t /\ x ∈ free T (open_loc u (w, l1)).
  Proof.
    intros. rewrite in_free_iff. setoid_rewrite in_free_iff_T.
    now rewrite in_open_iff.
  Qed.

  (** *** Closing *)
  (******************************************************************************)
  Lemma free_close_iff : forall t x y,
      y ∈ free F ('[x] t) <-> exists w l1,
        (w, l1) ∈d t /\ close_loc x (w, l1) = Fr y.
  Proof.
    intros. rewrite in_free_iff.
    now rewrite in_close_iff.
  Qed.

  (** *** Substitution *)
  (******************************************************************************)
  Lemma free_subst_iff : forall u t x y,
      y ∈ free F (t '{x ~> u}) <-> exists l1,
        l1 ∈ t /\ y ∈ free T (subst_loc x u l1).
  Proof.
    intros. rewrite (in_free_iff). setoid_rewrite (in_free_iff_T).
    now rewrite (in_subst_iff).
  Qed.

End locally_nameless_basic_principles.

(** * Utilities for reasoning at the leaves *)
(******************************************************************************)
Section locally_nameless_utilities.

  Context
    `{DecoratedTraversableModule nat (unit := Monoid_unit_zero) (op := Monoid_op_plus) F T}.

  Import Notations.

  (** ** (In)equalities between leaves *)
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
  Lemma subst_loc_eq : forall (u : T leaf) x,
      subst_loc x u (Fr x) = u.
  Proof. intros. cbn. now compare values x and x. Qed.

  Lemma subst_loc_neq : forall (u : T leaf) x y,
      y <> x -> subst_loc x u (Fr y) = ret T (Fr y).
  Proof. intros. cbn. now compare values x and y. Qed.

  Lemma subst_loc_b : forall u x n,
      subst_loc x u (Bd n) = ret T (Bd n).
  Proof. reflexivity. Qed.

  Lemma subst_loc_fr_neq : forall (u : T leaf) l x,
      Fr x <> l -> subst_loc x u l = ret T l.
  Proof.
    introv neq. unfold subst_loc.
    destruct l as [a|?]; [compare values x and a | reflexivity ].
  Qed.

  (** ** [open_loc] *)
  Lemma open_loc_lt : forall (u : T leaf) w n,
      n < w -> open_loc u (w, Bd n) = ret T (Bd n).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and w.
  Qed.

  Lemma open_loc_gt : forall (u : T leaf) n w,
      n > w -> open_loc u (w, Bd n) = ret T (Bd (n - 1)).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and w.
  Qed.

  Lemma open_loc_eq : forall w (u : T leaf),
      open_loc u (w, Bd w) = u.
  Proof.
    introv. unfold open_loc. compare naturals w and w.
  Qed.

  Lemma open_loc_atom : forall (u : T leaf) w x,
      open_loc u (w, Fr x) = ret T (Fr x).
  Proof.
    reflexivity.
  Qed.

  (** ** [Miscellaneous utilities] *)
  Lemma ninf_in_neq : forall x l (t : F leaf),
      ~ x ∈ free F t ->
      l ∈ t ->
      Fr x <> l.
  Proof.
    introv hyp1 hyp2.
    rewrite in_free_iff in hyp1. destruct l.
    - injection. intros; subst.
      contradiction.
    - discriminate.
  Qed.

  Lemma neq_symmetry : forall X (x y : X),
      (x <> y) = (y <> x).
  Proof.
    intros. propext; intro hyp; contradict hyp; congruence.
  Qed.

End locally_nameless_utilities.

Hint Rewrite @in_ret_iff @ind_ret_iff
     using typeclasses eauto : tea_local.

Hint Rewrite Fr_injective Fr_injective_not_iff Bd_neq_Fr : tea_local.
#[export] Hint Resolve Fr_injective_not : tea_local.

Hint Rewrite @subst_loc_eq (*@subst_in_ret*) using typeclasses eauto : tea_local.
Hint Rewrite @subst_loc_neq @subst_loc_b @subst_loc_fr_neq (*@subst_in_ret_neq*)
     using first [ typeclasses eauto | auto ] : tea_local.

Hint Rewrite @open_loc_lt @open_loc_gt
     using first [ typeclasses eauto | auto ] : tea_local.
Hint Rewrite @open_loc_eq @open_loc_atom using typeclasses eauto : tea_local.

Tactic Notation "simpl_local" := (autorewrite* with tea_local).
