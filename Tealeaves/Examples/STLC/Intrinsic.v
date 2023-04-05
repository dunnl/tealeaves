From Tealeaves Require Export
  Backends.LN.
From Coq Require Import
  Vectors.Vector.
Import Setlike.Functor.Notations. (* ∈ *)

Parameter base_typ : Type.

Inductive typ :=
| base : base_typ -> typ
| arr : typ -> typ -> typ.

Module term1.

  (* Track the variable scope in the type of terms, but track free and
     bound variables separately. *)
  Inductive t_ (Γ : list atom) (bs : nat) : Type :=
  | fvar : forall (a : atom), a ∈ Γ -> t_ Γ bs
  | bvar : Fin.t bs -> t_ Γ bs
  | lam : typ -> t_ Γ (bs + 1) -> t_ Γ bs
  | app : t_ Γ bs -> t_ Γ bs -> t_ Γ bs.

  (* Top-level terms have some free variables but we have not gone
  under any binders yet. *)
  Definition t (Γ : list atom) : Type := t_ Γ 0.

End term1.

Module term2.

  (* Track the free variable scope in the type of terms. The second
  argument is the type of bound variables, which is parameterized by
  the binding depth. *)
  Inductive t_ (Γ : list atom) (bs : nat -> Type) :=
  | fvar : forall (a : atom), a ∈ Γ -> t_ Γ bs
  | bvar : bs 0 -> t_ Γ bs
  | lam : typ -> t_ Γ (precompose (plus 1) bs) -> t_ Γ bs
  | app : t_ Γ bs -> t_ Γ bs -> t_ Γ bs.

  (* Top-level terms have free variables and bound variables are
  members of a finite set. *)
  Definition t (Γ : list atom) : Type := t_ Γ Fin.t.

End term2.

Module term3.

  (* Tealeaves style, where there is a single variable constructor and
  a single type of variables. *)
  Inductive t_ (vars : nat -> Type) :=
  | var : vars 0 -> t_ vars
  | lam : typ -> t_ (precompose (plus 1) vars) -> t_ vars
  | app : t_ vars -> t_ vars -> t_ vars.

  (* A locally nameless variable is a free variable or a de Bruijn
  index in the proper range. *)
  Inductive LN (Γ : list atom) (n : nat) : Type :=
  | fvar : forall (a : atom), a ∈ Γ -> LN Γ n
  | bvar : Fin.t n -> LN Γ n.

  Definition t (Γ : list atom) := t_ (LN Γ).

End term3.
