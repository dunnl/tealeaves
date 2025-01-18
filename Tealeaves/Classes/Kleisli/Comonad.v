From Tealeaves Require Export
  Classes.Functor
  Classes.Categorical.Comonad (Extract, extract).

Import Functor.Notations.

#[local] Generalizable Variables W A B C D.

(** * Comonads *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Class Cobind (W : Type -> Type) :=
  cobind : forall (A B : Type), (W A -> B) -> W A -> W B.

#[global] Arguments cobind {W}%function_scope {Cobind} {A B}%type_scope _%function_scope _.

(** ** Co-Kleisli Composition *)
(******************************************************************************)
Definition kc1 {W : Type -> Type} `{Cobind W}
  {A B C : Type} `(g : W B -> C) `(f : W A -> B) : (W A -> C) :=
  g ∘ @cobind W _ A B f.

#[local] Infix "⋆1" := (kc1) (at level 60) : tealeaves_scope.

(** ** Typeclasses *)
(******************************************************************************)
Class Comonad `(W : Type -> Type) `{Cobind W} `{Extract W} :=
    { kcom_cobind0 : forall `(f : W A -> B),
        @extract W _ B ∘ @cobind W _ A B f = f;
      kcom_cobind1 : forall (A : Type),
        @cobind W _ A A (@extract W _ A) = @id (W A);
      kcom_cobind2 : forall (A B C : Type) (g : W B -> C) (f : W A -> B),
        @cobind W _ B C g ∘ @cobind W _ A B f = @cobind W _ A C (g ⋆1 f)
    }.


(** ** Kleisli Category Laws *)
(******************************************************************************)
Section Kleisli_category_laws.

  Context
    `{Comonad W}.

  Lemma kc1_id_r {B C} : forall (g : W B -> C),
      g ⋆1 (@extract W _ B) = g.
  Proof.
    intros.
    unfold kc1.
    rewrite kcom_cobind1.
    reflexivity.
  Qed.

  Lemma kc1_id_l {A B} : forall  (f : W A -> B),
      (@extract W _ B) ⋆1 f = f.
  Proof.
    intros.
    unfold kc1.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  Lemma kc1_assoc {A B C D} : forall (h : W C -> D) (g : W B -> C) (f : W A -> B),
      h ⋆1 g ⋆1 f = h ⋆1 (g ⋆1 f).
  Proof.
    intros.
    unfold kc1.
    reassociate ->.
    rewrite kcom_cobind2.
    reflexivity.
  Qed.

End Kleisli_category_laws.

(** ** Comonad Homomorphisms *)
(** TODO *)
(******************************************************************************)

(** * Derived Structures *)
(******************************************************************************)

(** ** Derived Operations *)
(******************************************************************************)
Module DerivedOperations.

  #[export] Instance Map_Cobind (W: Type -> Type)
    `{Extract_W: Extract W} `{Cobind_W: Cobind W}: Map W :=
  fun A B (f : A -> B) => @cobind W Cobind_W A B (f ∘ @extract W Extract_W A).

End DerivedOperations.

Class Compat_Map_Cobind
  (W: Type -> Type)
  `{Extract_W: Extract W}
  `{Cobind_W: Cobind W}
  `{Map_W: Map W}: Prop :=
  compat_map_cobind:
    @Map_W = @DerivedOperations.Map_Cobind W Extract_W Cobind_W.

#[export] Instance Compat_Map_Cobind_Comonad (W: Type -> Type)
  `{Extract_W: Extract W} `{Cobind_W: Cobind W}:
  @Compat_Map_Cobind W Extract_W Cobind_W
    (@DerivedOperations.Map_Cobind W Extract_W Cobind_W).
Proof.
  reflexivity.
Qed.

Lemma map_to_cobind {W: Type -> Type}
  `{Extract_W: Extract W}
  `{Combind_W: Cobind W}
  `{Map_W: Map W}
  `{! Compat_Map_Cobind W}: forall {A B: Type} (f: A -> B),
    map (F := W) f = cobind (f ∘ extract).
Proof.
  intros.
  rewrite compat_map_cobind.
  reflexivity.
Qed.

(** ** Derived Kleisli Composition Laws *)
(******************************************************************************)
Section derived_instances.

  Context `{Comonad W} `{Map W} `{! Compat_Map_Cobind W}.

  (** *** Special cases for Kleisli composition *)
  (******************************************************************************)
  Lemma kc1_10 {A B C} : forall (g : W B -> C) (f : A -> B),
      g ⋆1 (f ∘ extract) = g ∘ map f.
  Proof.
    intros.
    unfold kc1.
    rewrite map_to_cobind.
    reflexivity.
  Qed.

  Lemma kc1_01 {A B C} : forall (g : B -> C) (f : W A -> B),
      (g ∘ extract) ⋆1 f = g ∘ f.
  Proof.
    intros.
    unfold kc1.
    reassociate ->.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  Lemma kc1_00 {A B C} : forall (g : B -> C) (f : A -> B),
      (g ∘ extract) ⋆1 (f ∘ extract) = (g ∘ f) ∘ extract.
  Proof.
    intros.
    unfold kc1.
    reassociate ->.
    rewrite kcom_cobind0.
    reflexivity.
  Qed.

  (** *** Other rules for Kleisli composition *)
  (******************************************************************************)
  Lemma kc1_asc1: forall `(h: W C -> D) `(g: B -> C) `(f: W A -> B),
      h ⋆1 (g ∘ f) = (h ∘ map g) ⋆1 f.
  Proof.
    intros.
    unfold kc1.
    reassociate ->.
    rewrite map_to_cobind.
    rewrite kcom_cobind2.
    rewrite kc1_01.
    reflexivity.
  Qed.

  Lemma kc1_asc2: forall `(h: C -> D) `(g: W B -> C) `(f: W A -> B),
      (h ∘ g) ⋆1 f = h ∘ (g ⋆1 f).
  Proof.
    intros. unfold kc1.
    reflexivity.
  Qed.

End derived_instances.

(** ** Derived Typeclass Instances *)
(******************************************************************************)
Module DerivedInstances.

  #[export] Instance Functor_Comonad
    (W : Type -> Type)
    `{Comonad W}
    `{Map W}
    `{! Compat_Map_Cobind W}: Functor W.
  Proof.
    constructor.
    - intros.
      rewrite map_to_cobind.
      change (id ∘ ?x) with x.
      rewrite kcom_cobind1.
      reflexivity.
    - intros.
      rewrite map_to_cobind.
      rewrite map_to_cobind.
      rewrite kcom_cobind2.
      rewrite kc1_00.
      rewrite map_to_cobind.
      reflexivity.
  Qed.

  Include DerivedOperations.

End DerivedInstances.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆1" := (kc1) (at level 60) : tealeaves_scope.
End Notations.
