From Tealeaves Require Export
  Classes.Functor.

#[local] Generalizable Variables F G A B.

(** * Endofunctors of Two Arguments *)
(**********************************************************************)

(** ** Operation <<map2>> *)
(**********************************************************************)
Class Map2 (F: Type -> Type -> Type): Type :=
  map2: forall (B1 A1 B2 A2: Type) (g: B1 -> B2) (f: A1 -> A2),
      F B1 A1 -> F B2 A2.

#[global] Arguments map2 {F}%function_scope {Map2}
  {B1 A1 B2 A2}%type_scope (g f)%function_scope.

(** ** Typeclass *)
(**********************************************************************)
Class Functor2 (F: Type -> Type -> Type) `{map2_F: Map2 F}: Type :=
  { fun2_map_id: forall (A1 A2: Type),
      map2 (@id A1) (@id A2) = @id (F A1 A2);
    fun2_map_map: forall (B1 A1 B2 A2 B3 A3: Type)
                    (g2: B2 -> B3) (f2: A2 -> A3)
                    (g1: B1 -> B2) (f1: A1 -> A2),
      map2 g2 f2 ∘ map2 g1 f1 = map2 (g2 ∘ g1) (f2 ∘ f1);
  }.


(** ** Natural Transformations *)
(**********************************************************************)
#[local] Notation "F ⇒2 G" :=
  (forall B A: Type, F B A -> G B A) (at level 60):
    tealeaves_scope.

Class Natural2 `{Map2 F} `{Map2 G} (ϕ: F ⇒2 G) :=
  { natural2_src: Functor2 F;
    natural2_tgt: Functor2 G;
    natural2: forall `(g: B1 -> B2) `(f: A1 -> A2),
      map2 (F := G) g f ∘ ϕ B1 A1 = ϕ B2 A2 ∘ map2 (F := F) g f
  }.
(** ** Single-Argument Functor Instances *)
(**********************************************************************)
Section composition_with_functor.

  Context
    `{Functor2 F}.

  #[export] Instance Map2_1 {B}: Map (F B) :=
    fun A1 A2 f => map2 id f.

  #[export] Instance Map2_2 {A}: Map (fun B => F B A) :=
    fun B1 B2 g => map2 g id.

  #[export] Instance Functor_Map2_1 {B}:
    Functor (F B) (Map_F := Map2_1).
  Proof.
    constructor; intros; unfold_ops @Map2_1.
    - rewrite fun2_map_id.
      reflexivity.
    - rewrite fun2_map_map.
      reflexivity.
  Qed.

  #[export] Instance Functor_Map2_2 {A}:
    Functor (fun B => F B A) (Map_F := Map2_2).
  Proof.
    constructor; intros; unfold_ops @Map2_2.
    - rewrite fun2_map_id.
      reflexivity.
    - rewrite fun2_map_map.
      reflexivity.
  Qed.

  Context {B1 B2 A1 A2: Type}.
  Context {B0 A0 B3 A3: Type}
    {g: B1 -> B2} {f: A1 -> A2}
    {h: A0 -> A1} {j: B0 -> B1}
    {k: B2 -> B3} {l: A2 -> A3}.

  (*
  Lemma fun2_map22_map21_commute:
    map2 (F := F) g id ∘ map2 id f =
      map2 (F := F) id f ∘ map2 (F := F) g id.
  Proof.
    rewrite fun2_map_map.
    rewrite fun2_map_map.
    reflexivity.
  Qed.

  Lemma fun2_map22_map21':
    map2 (F := F) g id ∘ map2 id f =
      map2 (F := F) g f.
  Proof.
    rewrite fun2_map_map.
    reflexivity.
  Qed.
  *)


  Lemma fun2_map22_map21:
    map (Map := Map2_2) g ∘ map (Map := Map2_1) f =
      map2 (F := F) g f.
  Proof.
    unfold_ops @Map2_2 @Map2_1.
    rewrite fun2_map_map.
    reflexivity.
  Qed.

  Lemma fun2_map2_map21:
    map2 (F := F) g f ∘ map (Map := Map2_1) h =
      map2 (F := F) g (f ∘ h).
  Proof.
    unfold_ops @Map2_1.
    rewrite fun2_map_map.
    reflexivity.
  Qed.

  Lemma fun2_map2_map22:
    map2 (F := F) g f ∘ map (Map := Map2_2) j =
      map2 (F := F) (g ∘ j) f.
  Proof.
    unfold_ops @Map2_2.
    rewrite fun2_map_map.
    reflexivity.
  Qed.

  Lemma fun2_map21_map2:
    map (Map := Map2_1) l ∘ map2 (F := F) g f =
      map2 g (l ∘ f).
  Proof.
    unfold_ops @Map2_1.
    rewrite fun2_map_map.
    reflexivity.
  Qed.

  Lemma fun2_map22_map2:
    map (Map := Map2_2) k ∘ map2 (F := F) g f =
      map2 (k ∘ g) f.
  Proof.
    unfold_ops @Map2_2.
    rewrite fun2_map_map.
    reflexivity.
  Qed.

End composition_with_functor.

(** ** Composition with Single-Argument Functors *)
(**********************************************************************)
#[local] Notation "G ○12 F" :=
  (compose G ○ F) (at level 50):tealeaves_scope.
#[local] Notation "F ○21 G" :=
  (fun B A => F (G B) (G A)) (at level 50): tealeaves_scope.

Section composition_with_functor.

  Context
    `{Functor G}
    `{Functor2 F}.

  #[export] Instance Map21_compose: Map2 (F ○21 G) :=
    fun A1 B1 A2 B2 f1 f2 => map2 (F := F) (map f1) (map f2).

  #[export] Instance Functor21_compose: Functor2 (F ○21 G).
  Proof.
    constructor; intros; unfold_ops @Map21_compose.
    - rewrite fun_map_id.
      rewrite fun_map_id.
      rewrite fun2_map_id.
      reflexivity.
    - rewrite fun2_map_map.
      rewrite fun_map_map.
      rewrite fun_map_map.
      reflexivity.
  Qed.

  #[export] Instance Map12_compose: Map2 (G ○12 F) :=
    fun A1 B1 A2 B2 f1 f2 => map (F := G) (map2 f1 f2).

  #[export] Instance Functor12_compose: Functor2 (G ○12 F).
  Proof.
    constructor; intros; unfold_ops @Map12_compose.
    - rewrite fun2_map_id.
      rewrite fun_map_id.
      reflexivity.
    - rewrite (fun_map_map (F := G)
                 (F B1 A1) (F B2 A2) (F B3 A3)).
      rewrite fun2_map_map.
      reflexivity.
  Qed.

End composition_with_functor.


(** ** Strength *)
(**********************************************************************)
Definition strength2 {F: Type -> Type -> Type}
  `{Map2 F} {A B C}:
  forall (p : A * F B C), F (A * B) (A * C) :=
    fun '(a, t) => map2 (pair a) (pair a) t.

(** * Notations *)
(**********************************************************************)
Module Notations.

  #[global] Notation "G ○12 F" :=
  (compose G ○ F) (at level 50):
    tealeaves_scope.

  #[global] Notation "F ○21 G" :=
    (fun B A => F (G B) (G A)) (at level 50):
      tealeaves_scope.

  #[global] Notation "F ⇒2 G" :=
    (forall B A: Type, F B A -> G B A) (at level 60):
      tealeaves_scope.

End Notations.
