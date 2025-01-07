From Tealeaves Require Import
  Classes.EqDec_eq
  Classes.Kleisli.DecoratedTraversableMonadPoly
  Backends.LN.Atom
  Functors.Constant.

Import Product.Notations.
Import ContainerFunctor.Notations.

(** * Transparent atoms *)
(******************************************************************************)

Module Type AtomModule  <: UsualDecidableType.

  Parameter name : Set.

  Definition t := name.

  Parameter eq_dec : forall x y : name, {x = y} + {x <> y}.

  Parameter name_fresh_for_list :
    forall (xs : list t), {x : name | ~ x ∈ xs}.

  Parameter fresh : list name -> name.

  Parameter fresh_not_in : forall l, ~ fresh l ∈ l.

  Parameter nat_of : name -> nat.

  #[export] Hint Resolve eq_dec : core.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

End AtomModule.

(** ** Implementation of atoms *)
(******************************************************************************)
Module Atom <: AtomModule.

  Definition name := nat.

  Definition t := name.

  Definition eq_dec := PeanoNat.Nat.eq_dec.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

  Lemma max_lt_r : forall x y z,
      x <= z -> x <= max y z.
  Proof.
    induction x.
    - auto with arith.
    - induction y.
      + auto with arith.
      + cbn. induction z. lia. auto with arith.
  Defined.

  Lemma nat_list_max : forall (xs : list nat),
      { n : nat | forall x, List.In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    - exists 0. inversion 1.
    - exists (max x y). intros z J.
      cbn in J. destruct J as [K | K].
      + subst. auto with arith.
      + auto using max_lt_r.
  Defined.

  Lemma name_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ n ∈ xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). lia. trivial.
  Defined.

  Definition fresh (l : list name) : name  :=
    match name_fresh_for_list l with
      (exist _ x _) => x
    end.

  Lemma fresh_not_in : forall l, ~ fresh l ∈ l.
  Proof.
    intro l. unfold fresh.
    destruct name_fresh_for_list. auto.
  Qed.

  Definition nat_of := fun (x : name) => (x : nat).

End Atom.

(** ** Shorthands and notations *)
(******************************************************************************)
Notation name := Atom.name.
Notation fresh := Atom.fresh.
Notation fresh_not_in := Atom.fresh_not_in.
Notation name_fresh_for_list := Atom.name_fresh_for_list.

(* Automatically unfold Atom.eq *)
#[global] Arguments Atom.eq /.

#[export] Instance EqDec_atom : @EqDec name eq eq_equivalence := Atom.eq_dec.

(** ** Localized operations *)
(******************************************************************************)
Section locally_nameless_local_operations.

  Context
    (T : Type -> Type -> Type)
    `{forall W, Return (T W)}
    `{Substitute T T}.

  (* Import Derived. *)

  (* Test if x is an element of l, returning a boolean *)
  Fixpoint list_in (x : name) (l : list name) : bool :=
    match l with
    | nil => false
    | y :: rest => (x ==b y) || list_in x rest
    end.

  Fixpoint list_fmapd_weird_rec (hist : list name) (f : list name * name -> name) (l : list name) : list name :=
    match l with
    | nil => nil
    | cons x xs => f (hist, x) :: list_fmapd_weird_rec (x :: hist) f xs
    end.

  Definition list_fmapd_weird (f : list name * name -> name) : list name -> list name :=
    list_fmapd_weird_rec nil f.

  Fixpoint list_fmapd_weird2_rec (hist : list name) (f : list name * name -> name) (l : list name) : list name :=
    match l with
    | nil => nil
    | cons x xs => f (hist, x) :: list_fmapd_weird2_rec (f (hist, x) :: hist) f xs
    end.

  Definition list_fmapd_weird2 (f : list name * name -> name) : list name -> list name :=
    list_fmapd_weird2_rec nil f.

  Definition hf_local (new_free_vars : list name) : list name * name -> name :=
    fun '(history, current) => fresh (new_free_vars ++ history).

  Definition hereditarily_freshen (new_free_vars : list name) : list name -> list name :=
    list_fmapd_weird2 (hf_local new_free_vars).

  Definition hf_local2 (new_free_vars : list name) : list name * name -> name :=
    fun '(history, current) => fresh (new_free_vars ++ hereditarily_freshen new_free_vars history).

  Import List.ListNotations.

  Definition X := fresh nil.
  Definition Y := fresh [X].
  Definition Z := fresh [X ; Y].

  Goal hereditarily_freshen nil nil = nil. reflexivity. Qed.
  Goal hereditarily_freshen nil [1] = [1]. reflexivity. Qed.
  Goal hereditarily_freshen nil [1 ; 2] = [1 ; 2]. reflexivity. Qed.
  Goal hereditarily_freshen nil [X ; Y ; Z] = [X ; Y ; Z]. reflexivity. Qed.
  Goal hereditarily_freshen [1] [1 ; 2 ; 3] = [2 ; 3 ; 4]. reflexivity. Qed.
  Goal hereditarily_freshen [1] [1 ; 3 ; 2] = [2 ; 3 ; 4]. reflexivity. Qed.
  Goal hereditarily_freshen [1] [1 ; 3 ; 3] = [2 ; 3 ; 4]. cbv. reflexivity. Qed.
  Goal hereditarily_freshen [1] [1 ; 3 ; 3] = [2 ; 3 ; 4]. cbv. reflexivity. Qed.

  (** ** The logic of binding *)

  Inductive Binding : Type :=
    Bound : list name -> list name -> Binding
  | Unbound : Binding.

  Fixpoint is_bound_ (discarded : list name)  (l : list name) (x : name) : Binding :=
    match l with
    | nil => Unbound
    | cons y ys => if x == y then Bound ys discarded else is_bound_ discarded ys x
    end.

  Definition is_bound (l : list name) (x : name) : Binding :=
    is_bound_ [] (List.rev l) x.


  (* Given a list of open binders, and an auxiliary list of names that clash, *)

  (*
  Definition rename (new_free : list name) : list name * name -> name :=
    fun '(ctx, x) =>
      if
        list_in x (avoid ++ ctx)
      then
        fresh (avoid ++ ctx)
      else
        x.
   *)


  About substitute.
  Definition FRV : T name name -> list name :=
    substitute
      (A1 := name) (B1 := name)
      (A2 := False) (B2 := False)
      (T := T) (U := T)
      (G := const (list name))
      (* (extract (W := prod (list name))) *)
      (const (@nil name))
      (fun '(ctx, x) => if is_bound ctx x then @nil name else [x]).

  Definition subst_naive_local (x : name) (u : T name name) : list name * name -> T name name :=
    fun '(l, y) => if x == y then u else ret (T name) y.

  Definition subst_smart_local (x : name) (u : T name name) : list name * name -> T name name :=
    fun '(l, y) =>
      match is_bound l y with
      | Bound top bottom =>
          ret (T name) (hf_local2 (FRV u) (top, y))
      | Unbound =>
          if x == y
          then u
          else ret (T name) y
      end.

  Definition subst (x : name) (u : T name name) : T name name -> T name name :=
    binddt T name name (fun A => A) (hf_local2 (FRV u)) (subst_smart_local x u).

  Fixpoint lookup_binding_ix_rec (n : nat) (l : list name) (nm : name) : option nat :=
    match l with
    | nil => None
    | cons nm' rest =>
        if nm == nm'
        then Some n
        else lookup_binding_ix_rec (S n) rest nm
    end.

  Definition lookup_binding_ix (l : list name) (nm : name) : option nat :=
    lookup_binding_ix_rec 0 l nm.

  Definition alpha_equiv_local : list name * name -> list name * name -> Prop :=
    fun '(ctx0, nm0) '(ctx1, nm1) =>
      lookup_binding_ix ctx0 nm0 === lookup_binding_ix ctx1 nm1.

  Check binddt T name name (fun A => A -> Prop) (extract (list name ×) (A:=name)) (alpha_equiv_local).

  Definition alpha_equiv : T name name -> T name name -> Prop :=
    binddt T name name (fun A => A -> Prop) (extract (list name ×) (A:=name)).

End locally_nameless_local_operations.


(** ** Localized operations *)
(******************************************************************************)
Section locally_nameless_local_operations.

  Context
    (T : Type -> Type -> Type)
    `{forall W, Return (T W)}
    `{Binddt T T}.


  Require Import Tealeaves.Backends.LN.


  Definition name_to_atom : name -> atom.
  Admitted.

  Definition translate_local : list name * name -> T unit LN :=
    fun '(l, y) =>
      match is_bound l y with
      | Bound remain opened =>
          ret (T unit) (Bd (length opened))
      | Unbound =>
          ret (T unit) (Fr (name_to_atom y))
      end.

  Definition translate : T name name -> T unit LN :=
    binddt T (T := T) name unit (fun A => A) (fun _ => tt) (translate_local).
