From Tealeaves Require Import
  Classes.Categorical.Monad
  Classes.Categorical.DecoratedMonad (shift)
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedTraversableMonad
  Functors.Early.Subset
  Functors.Early.Ctxset
  Functors.Early.List.

Import DecoratedTraversableFunctor.Notations.
Import Functor.Notations.
Import List.ListNotations.
Import Product.Notations.
Import Subset.Notations.
Import Applicative.Notations.
Import Strength.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables W M A B G ϕ.

Definition env (E: Type) (A: Type) := list (E * A).

(** * Decorated Traversable Functor Instance (Kleisli)] *)
(**********************************************************************)
Section env.

  Context
    (E: Type).

  (** ** Operation <<mapdt>> and Derived Operations *)
  (********************************************************************)
  Fixpoint mapdt_env (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
    `(f: E * A -> G B) (Γ: env E A): G (env E B) :=
    match Γ with
    | nil => pure (@nil (E * B))
    | (e, a) :: rest =>
        pure (@List.cons (E * B))
          <⋆> σ (e, f (e, a))
          <⋆> mapdt_env G f rest
    end.

  Fixpoint traverse_env (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
    `(f: A -> G B) (l: env E A): G (env E B) :=
    match l with
    | nil => pure (@nil (E * B))
    | (e, a) :: xs =>
        pure (@List.cons (E * B))
          <⋆> σ (e, f a)
          <⋆> traverse_env G f xs
    end.

  Fixpoint mapd_env `(f: E * A -> B) (Γ: env E A): env E B :=
    match Γ with
    | nil => @nil (E * B)
    | (e, a) :: rest =>
        (e, f (e, a)) :: mapd_env f rest
    end.

  Fixpoint map_env `(f: A -> B) (Γ: env E A): env E B :=
    match Γ with
    | nil => @nil (E * B)
    | (e, a) :: rest =>
        (e, f a) :: map_env f rest
    end.

  #[export] Instance Mapdt_env: Mapdt E (env E) := @mapdt_env.
  #[export] Instance Traverse_env: Traverse (env E) := @traverse_env.
  #[export] Instance Mapd_env: Mapd E (env E) := @mapd_env.
  #[export] Instance Map_env: Map (env E) := @map_env.

End env.

Ltac simple_env_tactic :=
  intros;
  let l := fresh "l" in
  let e := fresh "e" in
  let a := fresh "a" in
  let rest := fresh "rest" in
  let IHrest := fresh "IHrest" in
  ext l;
  ( induction l as [|[e a] rest IHrest] ||
  induction l as [|a rest IHrest] );
  [ reflexivity |
    try (cbn; now rewrite IHrest)].

(** ** Rewriting Laws for <<mapdt>> *)
(**********************************************************************)
Section mapdt_rewriting_lemmas.

  Context
    `{Applicative G}
    (E A B: Type).

  Lemma mapdt_env_nil: forall `(f: E * A -> G B),
      mapdt f (@nil (E * A)) = pure nil.
  Proof.
    reflexivity.
  Qed.

  Lemma mapdt_env_one:
    forall (f: E * A -> G B) (e: E) (a: A),
      mapdt f (ret (T := list) (e, a)) =
        map (ret (T := list) ∘ pair e) (f (e, a)).
  Proof.
    intros.
    cbn.
    rewrite map_to_ap.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma mapdt_env_cons:
    forall (f: E * A -> G B) (e: E) (a: A) (l: env E A),
      mapdt f ((e, a) :: l) =
        pure cons <⋆> σ (e, f (e, a)) <⋆> mapdt f l.
  Proof.
    reflexivity.
  Qed.

  Lemma mapdt_env_app:
    forall (f: E * A -> G B) (l1 l2: env E A),
      mapdt f (l1 ++ l2) =
        pure (@app (E * B)) <⋆> mapdt f l1 <⋆> mapdt f l2.
  Proof.
    intros.
    induction l1.
    - cbn.
      rewrite ap2.
      rewrite ap1.
      reflexivity.
    - destruct a  as (e, a).
      cbn.
      rewrite IHl1.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      rewrite ap3.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      reflexivity.
  Qed.

End mapdt_rewriting_lemmas.

#[export] Hint Rewrite
  mapdt_env_nil @mapdt_env_cons mapdt_env_one mapdt_env_app:
  tea_env.

(** ** Compatibility Typeclass Instances *)
(**********************************************************************)
Lemma env_traverse_compat:
  forall (E: Type) `{Applicative G} (A B: Type) (f: A -> G B),
    traverse f = mapdt (E := E) (f ∘ extract).
Proof.
  simple_env_tactic.
Qed.

Lemma env_mapd_compat: forall (E A B: Type) (f: E * A -> B),
    mapd (T := env E) f = mapdt (E := E) f.
Proof.
  simple_env_tactic.
Qed.

Lemma env_map_compat: forall (E A B: Type) (f: A -> B),
    map (F := env E) f = mapdt (E := E) (f ∘ extract (W := (E ×))).
Proof.
  simple_env_tactic.
Qed.

#[export] Instance Compat_Traverse_Mapdt_env {E: Type}:
  Compat_Traverse_Mapdt E (env E).
Proof.
  hnf. intros.
  ext G MapG PureG MultG.
  ext A B f l.
  unfold Traverse_env.
  change_left (traverse f l).
  change_right (mapdt (T := env E) (f ∘ extract (W := (E ×))) l).
  induction l.
  - reflexivity.
  - cbn.
    destruct a as [e a].
    rewrite IHl.
    reflexivity.
Qed.

#[export] Instance Compat_Map_Mapdt_env {E: Type}:
  Compat_Map_Mapdt E (env E).
Proof.
  hnf. ext A B f l.
  change_left (map f l).
  rewrite env_map_compat.
  reflexivity.
Qed.

#[export] Instance Compat_Mapd_Mapdt_env {E: Type}:
  Compat_Mapd_Mapdt E (env E).
Proof.
  hnf. ext A B f l.
  change_left (mapd f l).
  rewrite env_mapd_compat.
  reflexivity.
Qed.

(** ** Decorated Traversable Functor Laws *)
(**********************************************************************)
Section env_laws.

  Context
    (E: Type).

  Lemma env_mapdt1:
    forall (A: Type),
      mapdt (extract (W := (E ×))) = @id (env E A).
  Proof.
    intros. ext l. induction l.
    - reflexivity.
    - destruct a.
      autorewrite with tea_env.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma env_mapdt2
    `{Applicative G1}
    `{Applicative G2}:
    forall (A B C: Type)
      (g: E * B -> G2 C)
      (f: E * A -> G1 B),
      map (mapdt g) ∘ mapdt f =
        mapdt (G := G1 ∘ G2) (g ⋆3 f).
  Proof.
    intros. ext l. induction l.
    - unfold compose.
      cbn.
      compose near (@nil (E * B)).
      rewrite (natural (ϕ := @pure G1 _)).
      reflexivity.
    - unfold compose at 1.
      unfold compose at 1 in IHl.
      destruct a as [e a].
      autorewrite with tea_env.
      unfold strength.
      rewrite (map_to_ap (A := B) (G := G1)).
      rewrite <- ap4; do 2 rewrite ap2.
      rewrite map_to_ap.
      rewrite <- ap4; rewrite ap2.
      rewrite <- ap4; do 2 rewrite ap2.
      (* RHS *)
      rewrite map_to_ap.
      rewrite <- ap4; do 2 rewrite ap2.
      rewrite <- IHl.
      rewrite map_to_ap.
      rewrite (ap_compose1 G2 G1).
      rewrite (ap_compose1 G2 G1).
      unfold_ops @Pure_compose.
      rewrite <- ap4.
      rewrite <- ap4; do 3 rewrite ap2.
      rewrite <- ap4; do 2 rewrite ap2.
      unfold kc3, compose, strength.
      change (cobind f (e, a)) with (e, f (e, a)).
      do 2 rewrite map_to_ap.
      rewrite <- ap4; repeat rewrite ap2.
      rewrite <- ap4; repeat rewrite ap2.
      rewrite ap3.
      rewrite <- ap4; repeat rewrite ap2.
      repeat fequal.
      ext b l'. unfold compose.
      autorewrite with tea_env.
      unfold strength.
      rewrite map_to_ap.
      rewrite <- ap4; repeat rewrite ap2.
      reflexivity.
  Qed.

  Lemma env_mapdt_morph
    `{ApplicativeMorphism G1 G2 ϕ}:
      forall (A B: Type) (f: E * A -> G1 B),
          ϕ (env E B) ∘ mapdt (T := env E) f =
            mapdt (T := env E) (ϕ B ∘ f).
  Proof.
    intros. ext l. induction l.
    - unfold compose. cbn.
      rewrite appmor_pure.
      reflexivity.
    - destruct a as (e, a).
      unfold compose at 1.
      autorewrite with tea_env.
      rewrite <- IHl.
      unfold compose at 2.
      rewrite ap_morphism_1.
      rewrite ap_morphism_1.
      rewrite appmor_pure.
      unfold strength.
      rewrite appmor_natural.
      reflexivity.
  Qed.

End env_laws.

(** ** Typeclass Instance *)
(**********************************************************************)
#[export] Instance DecoratedTraversableFunctor_env (E: Type):
  DecoratedTraversableFunctor E (env E) :=
  {| kdtf_mapdt1 := env_mapdt1 E;
     kdtf_mapdt2 := @env_mapdt2 E;
     kdtf_morph := @env_mapdt_morph E;
  |}.

#[export] Instance Functor_env (E: Type): Functor (env E) :=
  DerivedInstances.Functor_DecoratedTraversableFunctor.

#[export] Instance DecoratedFunctor_env (E: Type):
  DecoratedFunctor E (env E) :=
  DerivedInstances.DecoratedFunctor_DecoratedTraversableFunctor.

#[export] Instance TraversableFunctor_env (E: Type):
  TraversableFunctor (env E) :=
  DerivedInstances.TraversableFunctor_DecoratedTraversableFunctor.

(** ** Alternative Specifications for <<mapd>> *)
(**********************************************************************)
Lemma env_mapd_spec: forall (E A B: Type) (f: E * A -> B),
    mapd (T := env E) f = map (F := list) (cobind (W := (E ×)) f).
Proof.
  simple_env_tactic.
Qed.

Lemma env_map_spec:
  forall (E A B: Type) (f: A -> B),
    map (F := env E) f = map (F := list) (map (F := (E ×)) f).
Proof.
  simple_env_tactic.
Qed.

Lemma env_map_spec2: forall (E A B: Type) (f: A -> B),
    map (F := env E) f = map (Map := Map_compose list (E ×)) f.
Proof.
  intros. now rewrite env_map_spec.
Qed.

(** * Decorated Traversable Monad Instance (Kleisli) *)
(**********************************************************************)
Section env.

  Context
    `{Monoid W}.

  #[export] Instance Return_env: Return (env W) :=
    fun A => ret (T := list) ∘ ret (T := (W ×)) (A := A).

  Fixpoint binddt_env (G: Type -> Type) `{Map G} `{Pure G} `{Mult G}
    `(f: W * A -> G (env W B)) (Γ: env W A): G (env W B) :=
    match Γ with
    | nil => pure (@nil (W * B))
    | (w, a) :: rest =>
        pure (@List.app (W * B))
          <⋆> map (F := G) (fun x => shift list (w, x)) (f (w, a))
          <⋆> binddt_env G f rest
    end.

  Fixpoint bindd_env `(f: W * A -> env W B) (Γ: env W A): env W B :=
    match Γ with
    | nil => @nil (W * B)
    | (w, a) :: rest =>
        shift list (w, f (w, a)) ++ bindd_env f rest
    end.

  Fixpoint bind_env `(f: A -> env W B) (l: env W A): env W B :=
    match l with
    | nil => pure (@nil (W * B))
    | (w, a) :: xs =>
        pure (@List.app (W * B))
          <⋆> shift list (w, f a)
          <⋆> bind_env f xs
    end.

  #[export] Instance Binddt_env: Binddt W (env W) (env W) := @binddt_env.
  #[export] Instance Bindd_env: Bindd W (env W) (env W) := @bindd_env.
  #[export] Instance Bind_env: Bind (env W) (env W) := @bind_env.

End env.
