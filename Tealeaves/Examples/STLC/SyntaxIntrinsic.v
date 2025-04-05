From Tealeaves Require Export
  Backends.LN.

Export LN.Simplification.
Export LN.Notations.

#[local] Set Implicit Arguments.

Definition go {v: nat -> Type} {n1 n2: nat}: n1 = n2 -> v n1 -> v n2 :=
  fun p v1 => match p in (_ = n2') return (v n2') with
           | eq_refl => v1
           end.


Definition go2 {v: nat -> Type} (x1 x2: nat -> nat) (p: forall n, x1 n = x2 n):
  ((forall n, v (x1 n)) -> (forall n, v (x2 n))).
Proof.
  intros.
  specialize (X n).
  rewrite (p n) in X.
  assumption.
Defined.

Open Scope nat_scope.

Section preincr.

  Definition preincr {A : nat -> Type}
    (f : forall (n: nat), A n) (w : nat) :=
    fun n => f (w + n).

  #[local] Infix "⦿" := preincr (at level 30) : tealeaves_scope.

  Lemma preincr_zero {A : Type} : forall (f : nat -> A),
      f ⦿ Ƶ = f.
  Proof.
    intros.
    unfold preincr.
    unfold_ops @Monoid_unit_zero.
    ext n.
    fequal.
  Qed.

  Lemma assoc {n1 n2 n3: nat}:
    ((n1 + n2) + n3) = n1 + (n2 + n3).
  Proof.
    lia.
  Qed.

  Lemma rassoc {n1 n2 n3: nat}:
    n1 + (n2 + n3) = ((n1 + n2) + n3).
  Proof.
    lia.
  Qed.

End preincr.

Section coercions.

  (*
  Goal forall (A: nat -> Type) (f: forall n, A n) w1 w2,
      f ⦿ w1 ⦿ w2 = f ⦿ w1 ⦿ w2 .
  Proof.
    intros.
    unfold preincr.
    ext n.
      f ∘ (fun n => (w1 + w2 + n)).

  Lemma preincr_preincr {A: nat -> Type} : forall (f : forall (n: nat), A n) (w1 : nat) (w2 : nat),
       f ⦿ w1 ⦿ w2 = go2 (fun n => w1 + w2 + n) (fun n => w1 + (w2 + n)) _ (f ⦿ (w1 + w2)).
  Proof.
    intros. unfold preincr.
    ext n.
    reassociate ->.
    fequal. unfold transparent tcs.
    unfold compose. ext n.
    lia.
  Qed.
   *)

End coercions.

(*
Section preincr.

  Definition preincr {A : Type} (f : nat -> A) (w : nat) :=
    f ∘ (plus w).

  #[local] Infix "⦿" := preincr (at level 30) : tealeaves_scope.

  Lemma preincr_zero {A : Type} : forall (f : nat -> A),
      f ⦿ Ƶ = f.
  Proof.
    intros.
    unfold preincr.
    unfold_ops @Monoid_unit_zero.
    reflexivity.
  Qed.

  Lemma preincr_preincr {A : Type} : forall (f : nat -> A) (w1 : nat) (w2 : nat),
       f ⦿ w1 ⦿ w2 = f ⦿ (w1 ● w2).
  Proof.
    intros. unfold preincr.
    reassociate ->.
    fequal. unfold transparent tcs.
    unfold compose. ext n.
    lia.
  Qed.

End preincr.
*)

#[local] Infix "⦿" := preincr (at level 30) : tealeaves_scope.


(*|
========================================
Definition of binddt
========================================
|*)

Generalizable All Variables.

Inductive Lam (V : nat -> Type) :=
| tvar : V 0 -> Lam V
| lam  : Lam (V ⦿ 1) -> Lam V
| app  : Lam V -> Lam V -> Lam V.

Fixpoint binddt_Lam {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
  {v1 v2 : nat -> Type}
  (f : forall (n: nat), v1 n -> G (Lam (v2 ⦿ n))) (t : Lam v1) : G (Lam v2) :=
  match t with
  | tvar _ v => f 0 v
  | lam body => ap G (pure (F := G) (@lam v2)) (binddt_Lam (G := G) (v1 := v1 ⦿ 1) (v2 := v2 ⦿ 1) (f ⦿ 1) body)
  | app t1 t2 => pure (F := G) (@app v2) <⋆> binddt_Lam (G := G) f t1 <⋆> binddt_Lam (G := G) f t2
  end.


  Lemma dtm1:
    forall (G : Type -> Type)
      (H : Map G)
      (H0 : Pure G)
      (H1 : Mult G),
      Applicative G ->
      forall (A B : nat -> Type) (f : forall n, A n -> G (Lam (B ⦿ n))),
        binddt_Lam f ∘ tvar A = f 0.
  Proof.
    intros.
    unfold ret.
    reflexivity.
  Qed.

  Context {A: nat -> Type}.
  Check binddt_Lam (v1 := A) (v2 := A) (G := fun A => A).
  (fun n v => tvar _ v).

  Lemma dtm2 {A: nat -> Type}:
    binddt_Lam (G := fun A => A) (fun n v => tvar _ v)
    = @id (Lam A).

  Lemma dtm4 {A B: nat -> Type}:
    forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ}
      `(f : forall (n: nat), A n -> G1 (Lam (B ⦿ n))),
      ϕ (Lam B) ∘ binddt_Lam f = binddt_Lam (fun n => ϕ (Lam (B ⦿ n)) ∘ f n).
  Proof.
    intros. ext t.
    unfold compose.
    generalize dependent B.
    induction t; intros.
    - unfold preincr; cbn.
      reflexivity.
    - intros.
      cbn.
      rewrite ap_morphism_1.
      rewrite appmor_pure.
      fequal. apply IHt.
    - cbn.
      unfold preincr.
      rewrite ap_morphism_1.
      rewrite ap_morphism_1.
      rewrite appmor_pure.
      fequal; fequal.
      + rewrite IHt1. reflexivity.
      + rewrite IHt2. reflexivity.
  Qed.






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
