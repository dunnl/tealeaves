Variable (n:nat).
Compute 0 + n.
Compute n + 0.

Goal n = n + 0.
Abort.

From Tealeaves Require Export
  Backends.LN
  Functors.Option.

Export LN.Simplification.
Export LN.Notations.

#[local] Set Implicit Arguments.
#[local] Set Maximal Implicit Insertion.

(*|
========================================
Using Tealeaves with STLC
========================================
|*)
Parameter base_typ : Type.

Inductive typ :=
| base : base_typ -> typ
| arr : typ -> typ -> typ.

Coercion base : base_typ >-> typ.

Inductive Lam (V : Type) :=
| tvar : V -> Lam V
| lam  : typ -> Lam V -> Lam V
| app  : Lam V -> Lam V -> Lam V.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Notations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Module TermNotations.
  Notation "'term'" := (Lam LN).
  Notation "'λ'" := (lam) (at level 45).
  Notation "⟨ t ⟩ ( u )" := (app t u) (at level 80, t at level 40, u at level 40).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End TermNotations.

Import TermNotations.

Definition lnvar := @tvar LN.
Definition bvar := @tvar LN ○ Bd.
Definition fvar := @tvar LN ○ Fr.
Coercion lnvar: LN >-> Lam.
Coercion bvar: nat >-> Lam.
Coercion fvar: atom >-> Lam.
Coercion Bd: nat >-> LN.
Coercion Fr: atom >-> LN.

(* Help the simplification tactics unfold coercions to expose a
   <<tvar>> constructor, which is needed to find a match for
   <<bindd f (ret x)>> *)
#[global] Hint Unfold fvar bvar: tea_ret_coercions.

Section test_notations.

  Context
    (β : Type)
    (x y z : atom)
    (b : β) (τ : typ).

  Check 1.
  Check (1: LN).
  Check (1: Lam LN).
  Check λ τ (tvar (Bd 1)).
  Check λ τ (Bd 1).
  Check λ τ 1.
  Check λ τ (tvar (Fr x)).
  Check λ τ (Fr x).
  Check λ τ x.
  Check ⟨λ τ (tvar (Bd 1))⟩ (tvar (Fr x)).
  Check ⟨λ τ (Bd 1)⟩ (Fr x).
  Check ⟨λ τ (Bd 1)⟩ (x).
  Check ⟨λ τ (tvar (Fr x))⟩ (tvar (Bd 0)).
  Check ⟨λ τ (Fr x)⟩ (Bd 0).
  Check ⟨λ τ x⟩ (0).

End test_notations.

(*|
========================================
Definition of binddt
========================================
|*)
Fixpoint binddt_Lam (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f : nat * v1 -> G (Lam v2)) (t : Lam v1) : G (Lam v2) :=
  match t with
  | tvar v => f (0, v)
  | lam τ body => pure (lam τ) <⋆> binddt_Lam (f ⦿ 1) body
  | app t1 t2 => pure (@app v2) <⋆> binddt_Lam f t1 <⋆> binddt_Lam f t2
  end.

#[export] Instance Return_STLC: Return Lam := @tvar.
#[export] Instance Binddt_STLC: Binddt nat Lam Lam := @binddt_Lam.
#[export] Instance DTM_STLC: DecoratedTraversableMonad nat Lam.
Proof.
  (* We duplicate the goal just for the purpose of debugging the tactics *)
  dup. {
    constructor.
    typeclasses eauto.
    - derive_dtm1.
    - constructor.
      + derive_dtm2.
      + derive_dtm3.
      + derive_dtm4. }
  derive_dtm.
Qed.

#[local] Notation "f ⦿ n" := (f ○ (fun m => n ● m)).

Module intrinsic.


  Inductive Lam (V : nat -> Type): Type :=
  | tvar : V 0 -> Lam V
  | lam  : typ -> Lam (V ⦿ 1) -> Lam V
  | app  : Lam V -> Lam V -> Lam V.

  Fixpoint binddt_Lam (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : nat -> Type} (f : forall (n: nat), v1 n -> G (Lam (v2 ⦿ n))) (t : Lam v1) : G (Lam v2) :=
    match t with
    | tvar _ v => f 0 v
    | lam _ τ body => pure (lam _ τ) <⋆> binddt_Lam (f ⦿ 1) body
    | app t1 t2 => pure (@app v2) <⋆> binddt_Lam f t1 <⋆> binddt_Lam f t2
    end.

  Lemma dtm1:
    forall (G : Type -> Type) (H : Map G)
      (H0 : Pure G) (H1 : Mult G),
      Applicative G ->
      forall (A B : nat -> Type) (f : forall n, A n -> G (Lam (B ⦿ n))),
        binddt_Lam f ∘ tvar A = f 0.
  Proof.
    intros.
    unfold ret.
    reflexivity.
  Qed.

End intrinsic.

(* exampls *)

Module test.

  Import Coq.Vectors.Fin.
  Import intrinsic.

  Context (τ: typ).

  Definition V : nat -> Type := Fin.t.
  Definition term := Lam V.

  Definition one: (V ⦿ 1) 0.
    cbv.
    apply Fin.F1.
  Defined.

  Example tm1: Lam V :=
    lam V τ (tvar _ Fin.F1).

  Example tm2: Lam V :=
    lam _ τ (lam _ τ (tvar _ Fin.F1)).

  Example tm3: Lam V :=
    lam _ τ (lam _ τ (tvar _ (FS Fin.F1))).

  Print tm2.


End test.

Module nested.

  Inductive Lam (V : Type) :=
  | tvar : V -> Lam V
  | lam  : typ -> Lam (option V) -> Lam V
  | app  : Lam V -> Lam V -> Lam V.

  Fixpoint map_lam {X Y} (f: X -> Y) (l: Lam X): Lam Y :=
    match l with
    | tvar x => tvar (f x)
    | lam τ body => lam τ (map_lam (map (F := option) f) body)
    | app t1 t2 => app (map_lam f t1) (map_lam f t2)
    end.

  Instance Map_lam : Map Lam := @map_lam.

  Definition fubar {X}: option (Lam X) -> Lam (option X) :=
    fun x => match x with
          | None => tvar None
          | Some l => map Some l
          end.

  Fixpoint bind_Lam
    {v1 v2 : Type} (f : v1 -> Lam v2) (t: Lam v1) : Lam v2 :=
    match t with
    | tvar v => f v
    | lam τ body => lam τ (bind_Lam (fubar ∘ map (F := option) f) body)
    | app t1 t2 => @app v2 (bind_Lam f t1) (bind_Lam f t2)
    end.

End nested.























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

  (* Top-level terms have some free variables and bound variables are
  the finite set with cardinality equal to the binding depth. *)
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
