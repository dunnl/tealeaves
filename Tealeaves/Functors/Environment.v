From Tealeaves Require Export
  Classes.Categorical.Monad
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Categorical.DecoratedFunctor (shift)
  Functors.Subset
  Functors.List.

Import DecoratedTraversableFunctor.Notations.
Import Functor.Notations.
Import List.ListNotations.
Import Product.Notations.
Import Subset.Notations.
Import Applicative.Notations.
Import Strength.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables M A B G ϕ.

Definition ctxset (E : Type) (A : Type) := subset (E * A).
Definition env (E : Type) (A : Type) := list (E * A).

(** * "Decorated" subset functor *)
(******************************************************************************)
Section env.

  Context
    (E : Type).

  Definition mapd_ctxset `(f : E * A -> B) (s : ctxset E A) : ctxset E B :=
    fun '(e, b) => exists (a : A), s (e, a) /\ f (e, a) = b.

  Definition map_ctxset `(f : A -> B) (s : ctxset E A) : ctxset E B :=
    fun '(e, b) => exists (a : A), s (e, a) /\ f a = b.

  #[export] Instance Mapd_ctxset : Mapd E (ctxset E) := @mapd_ctxset.

  #[export] Instance Map_ctxset : Map (ctxset E) := @map_ctxset.

  #[export] Instance mapd_ctxset_morphism : forall `(f : E * A -> B),
      Monoid_Morphism (ctxset E A) (ctxset E B) (mapd f).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - cbv. ext [e b]. propext.
      + intros; now preprocess.
      + contradiction.
    - intros. ext [e b]. cbv. propext.
      + intros; preprocess.
        destruct H; eauto.
      + intros [H|H]; preprocess.
        eauto. eauto.
  Qed.

  #[export] Instance map_ctxset_morphism : forall `(f : A -> B),
      Monoid_Morphism (ctxset E A) (ctxset E B) (map f).
  Proof.
    intros. constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - cbv. ext [e b]. propext.
      + intros; now preprocess.
      + contradiction.
    - intros. ext [e b]. cbv. propext.
      + intros; preprocess.
        destruct H; eauto.
      + intros [H|H]; preprocess.
        eauto. eauto.
  Qed.

  Lemma ctxset_map_to_mapd : forall (A B : Type) (f : A -> B),
      map f = mapd (T := ctxset E) (f ∘ extract).
  Proof.
    intros. unfold_ops @Map_ctxset @Mapd_ctxset.
    unfold map_ctxset, mapd_ctxset.
    ext s [e b]. propext.
    - intros [a [H1 H2]]. eauto.
    - intros [a [H1 H2]]. eauto.
  Qed.

  Lemma Mapd_ctxset_spec1 : forall `(f : E * A -> B),
    @mapd_ctxset A B f =
      map (F := subset) (cobind (W := (E ×)) f).
  Proof.
    intros. ext s (e, b).
    unfold_ops @Map_subset @Map_Bind @Bind_subset.
    unfold_ops @Mapd_ctxset; unfold mapd_ctxset.
    unfold_ops @Return_subset @Cobind_reader.
    unfold compose at 1.
    propext.
    - intros [a Hs].
      exists (e, a). now preprocess.
    - intros [[e' a] H].
      exists a. now preprocess.
  Qed.

  Lemma dfun_subset_mapd1 :
    forall A : Type, mapd (T := ctxset E) extract = @id (ctxset E A).
  Proof.
    intros. cbv. ext f [e a]. propext.
    - intros [a' Heq]. now preprocess.
    - intros H. exists a. intuition.
  Qed.

  Lemma dfun_subset_mapd2 :
    forall (A B C : Type) (g : E * B -> C) (f : E * A -> B),
      mapd g ∘ mapd f = mapd (kc4 g f).
  Proof.
    intros. do 2 rewrite Mapd_ctxset_spec1.
    rewrite (fun_map_map (E * A) (E * B) (E * C) (F := subset)).
    rewrite (kcom_cobind2).
    rewrite <- Mapd_ctxset_spec1.
    reflexivity.
  Qed.

  #[export] Instance DTF_ctxset : DecoratedFunctor E (ctxset E) :=
    {| dfun_mapd1 := dfun_subset_mapd1;
       dfun_mapd2 := dfun_subset_mapd2;
    |}.

  #[export] Instance DTF_Full_ctxset :
    DecoratedFunctorFull E (ctxset E) :=
    {| dfunf_map_to_mapd := ctxset_map_to_mapd;
    |}.

End env.

Section toset.

  Class Elementsd (E : Type) (F : Type -> Type) :=
    elementsd : forall A : Type, F A -> subset (E * A).

  #[global] Arguments elementsd {E}%type_scope {F}%function_scope
    {Elementsd} {A}%type_scope _.

End toset.

(** * The [env] decorated traversable functor, Kleisli-style *)
(******************************************************************************)
Section env.

  Context
    (E : Type).

  Fixpoint mapdt_env (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    `(f : E * A -> G B) (Γ : env E A) : G (env E B) :=
    match Γ with
    | nil => pure (@nil (E * B))
    | (e, a) :: rest =>
        pure (@List.cons (E * B)) <⋆> σ (e, f (e, a)) <⋆> mapdt_env G f rest
    end.

  Fixpoint traverse_env (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    `(f : A -> G B) (l : env E A) : G (env E B) :=
    match l with
    | nil => pure (@nil (E * B))
    | (e, a) :: xs =>
        pure (@List.cons (E * B)) <⋆> σ (e, f a) <⋆> traverse_env G f xs
    end.

  Fixpoint map_env `(f : A -> B) (Γ : env E A) : env E B :=
    match Γ with
    | nil => @nil (E * B)
    | (e, a) :: rest =>
        (e, f a) :: map_env f rest
    end.

  #[export] Instance Mapdt_env : Mapdt E (env E) := @mapdt_env.
  #[export] Instance Traverse_env : Traverse (env E) := @traverse_env.
  #[export] Instance Mapd_env : Mapd E (env E) := DerivedOperations.Mapd_Mapdt.
  #[export] Instance Map_env : Map (env E) := @map_env.

End env.

(** ** Compatibility for operations *)
(******************************************************************************)
Lemma env_traverse_compat :
  forall (E : Type) `{Applicative G} (A B : Type) (f : A -> G B),
    traverse f = mapdt (E := E) (f ∘ extract).
Proof.
  intros. ext l. induction l as [|(e, a) rest IHrest].
  - reflexivity.
  - cbn. rewrite IHrest.
    reflexivity.
Qed.

Lemma env_map_compat : forall (E A B : Type) (f : A -> B),
    map (F := env E) f = mapdt (E := E) (f ∘ extract (W := (E ×))).
Proof.
  intros. ext l. induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

Lemma env_map_compat2 : forall (E A B : Type) (f : A -> B),
    map (F := env E) f =
      map (Map := Map_compose list (E ×)) f.
Proof.
  intros. ext l. induction l as [|[e a] rest IHrest].
  - reflexivity.
  - cbn. rewrite IHrest. reflexivity.
Qed.

(** ** Rewriting lemmas for <<bindt>> *)
(******************************************************************************)
Section mapdt_rewriting_lemmas.

  Context
    `{Applicative G}
    (E A B : Type).

  Lemma mapdt_env_nil : forall `(f : E * A -> G B),
      mapdt f (@nil (E * A)) = pure nil.
  Proof.
    reflexivity.
  Qed.

  Lemma mapdt_env_one : forall (f : E * A -> G B) (e : E) (a : A),
      mapdt f (ret (T := list) (e, a)) = map (ret (T := list) ∘ pair e) (f (e, a)).
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

  Lemma mapdt_env_cons : forall (f : E * A -> G B) (e : E) (a : A) (l : env E A),
      mapdt f ((e, a) :: l) =
        pure cons <⋆> σ (e, f (e, a)) <⋆> mapdt f l.
  Proof.
    reflexivity.
  Qed.

  Lemma mapdt_env_app : forall (f : E * A -> G B) (l1 l2 : env E A),
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

#[export] Hint Rewrite mapdt_env_nil @mapdt_env_cons mapdt_env_one mapdt_env_app :
  tea_env.

(** ** General properties *)
(******************************************************************************)
Section theory.

  Context (E : Type).

  Lemma map_env_spec1 : forall `(f : A -> B),
    map (F := env E) f = map (F := list ∘ (E ×)) (Map := Map_compose _ _) f.
  Proof.
    intros. ext l. induction l.
    - reflexivity.
    - destruct a as [e a].
      cbn. rewrite IHl.
      reflexivity.
  Qed.

End theory.

(** ** Decorated traversable functor instance *)
(******************************************************************************)
Section env_laws.

  Context
    (E : Type).

  Lemma env_mapdt1 : forall A : Type, mapdt (extract (W := (E ×))) = @id (env E A).
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
    `{Applicative G2} :
    forall (A B C : Type)
      (g : E * B -> G2 C)
      (f : E * A -> G1 B),
      map (mapdt g) ∘ mapdt f =
        mapdt (G := G1 ∘ G2) (g ⋆6 f).
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
      unfold kc6, compose, strength.
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
    `{ApplicativeMorphism G1 G2 ϕ} :
      forall (A B : Type) (f : E * A -> G1 B),
        mapdt (T := env E) (ϕ B ∘ f) =
          ϕ (env E B) ∘ mapdt (T := env E) f.
  Proof.
    intros. ext l. induction l.
    - unfold compose. cbn.
      rewrite appmor_pure.
      reflexivity.
    - destruct a as (e, a).
      unfold compose at 2.
      autorewrite with tea_env.
      rewrite IHl.
      unfold compose at 2.
      rewrite ap_morphism_1.
      rewrite ap_morphism_1.
      rewrite appmor_pure.
      unfold strength.
      rewrite appmor_natural.
      reflexivity.
  Qed.

End env_laws.

#[export] Instance DTF_env (E : Type) :
  DecoratedTraversableFunctor E (env E) :=
  {| kdtfun_mapdt1 := env_mapdt1 E;
     kdtfun_mapdt2 := @env_mapdt2 E;
     kdtfun_morph := @env_mapdt_morph E;
  |}.

#[export] Instance DTF_Full_env (E : Type) :
  DecoratedTraversableFunctorFull E (env E) :=
  {| kdtfunf_map_to_mapdt := env_map_compat E;
     kdtfunf_mapd_to_mapdt := @DerivedOperations.mapd_to_mapdt E (env E) _;
     kdtfunf_traverse_to_mapdt := @env_traverse_compat E;
  |}.

(** * The [env] DTM, Kleisli-style *)
(******************************************************************************)
Section env.

  Context
    (W : Type)
    `{Monoid W}.

  Definition ret_env : Return (env W) :=
    fun A => ret (T := list) ∘ ret (T := (W ×)) (A := A).

  Fixpoint binddt_env (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
    `(f : W * A -> G (env W B)) (Γ : env W A) : G (env W B) :=
    match Γ with
    | nil => pure (@nil (W * B))
    | (w, a) :: rest =>
        pure (@List.app (W * B)) <⋆> map (F := G) (fun x => shift list (w, x)) (f (w, a)) <⋆> binddt_env G f rest
    end.

  Fixpoint bind_env `(f : A -> env W B) (l : env W A) : env W B :=
    match l with
    | nil => pure (@nil (W * B))
    | (w, a) :: xs =>
        pure (@List.app (W * B)) <⋆> shift list (w, f a) <⋆> bind_env f xs
    end.

  #[export] Instance Binddt_env : Binddt W (env W) (env W) := @binddt_env.
  #[export] Instance Bind_env : Bind (env W) (env W) := @bind_env.

End env.
