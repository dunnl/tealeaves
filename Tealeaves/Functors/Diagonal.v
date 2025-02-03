From Tealeaves Require Export
  Classes.Categorical.Applicative.
  From Tealeaves Require Import
  Classes.Comonoid
  Classes.Kleisli.TraversableFunctor.

Export Comonoid (dup).

Import Applicative.Notations.

(** * Diagonal (Duplication) Applicative Functor *)
(**********************************************************************)
Definition Diagonal (A: Type): Type := A * A.

#[export] Instance Map_Diagonal: Map Diagonal :=
  fun A B f => map_both f: A * A -> B * B.

#[export, program] Instance Functor_Diagonal: Functor Diagonal.

Solve All Obligations with
  (intros; now ext [?]).

(** ** Applicative Functor Instance *)
(**********************************************************************)
#[export] Instance Pure_Diagonal: Pure Diagonal := @dup.

#[export] Instance Mult_Diagonal: Mult Diagonal :=
  fun A B (x: Diagonal A * Diagonal B) =>
    ((fst (fst x), fst (snd x)), (snd (fst x), snd (snd x))).

#[export, program] Instance Applicative_Diagonal: Applicative Diagonal.

Solve Obligations with
  (unfold Diagonal; intros; now destruct_all_pairs).

(** ** Traversable Functor Instance *)
(**********************************************************************)
#[export] Instance Traverse_Diagonal: Traverse (fun A => A * A).
Proof.
  intros G GMap GPure GMult A B f [a1 a2].
  exact (pure pair <⋆> f a1 <⋆> f a2).
Defined.

Lemma traverse_Diagonal_rw {A B: Type} {G}
  `{Map G} `{Mult G} `{Pure G} (f: A -> G B) (a1 a2: A):
  traverse (T := fun A => A * A) f (a1, a2) =
    pure pair <⋆> f a1 <⋆> f a2.
Proof.
  reflexivity.
Qed.

#[export] Instance TraversableFunctor_Diagonal:
  TraversableFunctor (fun A => A * A).
Proof.
  constructor.
  - intros. ext [a1 a2]. reflexivity.
  - intros. ext [a1 a2]. unfold compose, kc2.
    cbn.
    do 2 rewrite map_ap.
    rewrite app_pure_natural.
    change (fun a => G1 (G2 a)) with (G1 ∘ G2).
    rewrite (ap_compose2 G2 G1).
    rewrite (ap_compose2 G2 G1).
    unfold_ops @Pure_compose.
    rewrite app_pure_natural.
    rewrite map_ap.
    rewrite app_pure_natural.
    unfold compose at 4 5.
    rewrite <- (ap_map).
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- (ap_map).
    rewrite app_pure_natural.
    reflexivity.
  - intros.
    ext [a1 a2].
    unfold compose at 1.
    cbn.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    reflexivity.
Qed.
