From Tealeaves Require Import
     Util.Prelude Util.EqDec_eq
     LN.Atom LN.AtomSet LN.Leaf
     Classes.DecoratedTraversableModule
     Functors.Maybe.

Import DecoratedTraversableMonad.Notations.
Import LN.AtomSet.Notations.
Open Scope tealeaves_scope.
Open Scope set_scope.

(** * Locally nameless leaves *)
(******************************************************************************)
Inductive leaf :=
| Fr : Atom.atom -> leaf
| Bd : nat -> nat -> leaf.
(* Bd group index, individual index *)

Theorem eq_dec_leaf : forall l1 l2 : leaf, {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
  - compare values a and a0; auto.
  - compare values n and n0; auto.
    compare values n0 and n2; auto.
    compare values n0 and n2; auto.
  - compare values n and n1; auto.
Qed.

Instance EqDec_leaf : EquivDec.EqDec leaf eq := eq_dec_leaf.

Fixpoint nth {A} (n : nat) (l : list A) : Maybe A :=
  match n, l with
  | O, x :: l' => Just x
  | O, other => None
  | S m, nil => None
  | S m, x :: t => nth m t
  end.

Lemma nth1 : forall (A : Type) (n : nat), nth n (@nil A) = None.
Proof.
  intros. now induction n.
Qed.

Lemma nth2 : forall (A : Type) (n : nat) (w : list A),
    Nat.compare n (length w) = Gt -> nth n w = None.
Proof.
  intros. generalize dependent n. induction w.
  - intros. now rewrite nth1.
  - intros. destruct n.
    + cbv in H. inversion H.
    + cbn in *. auto.
Qed.

Lemma nth3 : forall (A : Type) (w : list A),
    nth (length w) w = None.
Proof.
  intros. induction w.
  - cbn. reflexivity.
  - cbn. auto.
Qed.

(** * Operations for locally nameless *)
(******************************************************************************)

(** ** Local operations *)
(******************************************************************************)
Section local_operations.

  Context
    `{Return T}.

  Implicit Types (x : atom).

  Definition free_loc : leaf -> list atom :=
    fun l => match l with
          | Fr x => cons x List.nil
          | _ => List.nil
          end.

  Definition subst_loc x (u : T leaf) : leaf -> T leaf :=
    fun l => match l with
          | Fr y => if x == y then u else ret T (Fr y)
          | Bd grp ix => ret T (Bd grp ix)
          end.

  Definition open_loc (binders : list (T leaf)) : list nat * leaf -> Maybe (T leaf) :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => Just (ret T (Fr x))
            | Bd grp ix =>
              match Nat.compare grp (length w) with
              | Lt => Just (ret T (Bd grp ix))
              | Eq => nth ix binders
              | Gt => Just (ret T (Bd (grp - 1) ix))
              end
            end
          end.

  Definition is_bound_or_free : list nat * leaf -> Prop :=
    fun p => match p with
          | (w, l) =>
            match l with
            | Fr x => True
            | Bd grp ix =>
              match nth grp w with
              | Just size => ix < size
              | None => False
              end
            end
          end.

End local_operations.

(** ** Lifted operations *)
(******************************************************************************)
Section LocallyNamelessOperations.

  About DecoratedTraversableModule.
  Context
    (T : Type -> Type)
    `{DecoratedTraversableMonad (list nat)
                                 (op := @List.app nat) (unit := nil) T}.

  Definition open (binders : list (T leaf)) : T leaf -> Maybe (T leaf)  :=
    binddt T (open_loc binders).

  Definition locally_closed : T leaf -> Prop :=
    fun t => forall w l, (w, l) ∈d t -> is_bound_or_free (w, l).

  Corollary open_respectful_id (us : list (T leaf)) : forall (t : T leaf),
      (forall w a, (w, a) ∈d t -> open_loc us (w, a) = Just (ret T a)) -> binddt T (open_loc us) t = pure Maybe t.
  Proof.
    intros. now apply (binddt_respectful_id T).
  Qed.

  Theorem correct : forall (t : T leaf) (us : list (T leaf)),
      locally_closed t -> open us t = Just t.
  Proof.
    introv LC. unfold locally_closed in LC.
    apply open_respectful_id.
    intros w l Hin. specialize (LC w l Hin).
    destruct l; cbn in LC.
    - reflexivity.
    - cbn. compare naturals n and (length w).
      + rewrite nth3 in LC. inversion LC.
      + assert (lemma : nth n w = None) by auto using nth2.
        rewrite lemma in LC. inversion LC.
  Qed.

End LocallyNamelessOperations.
