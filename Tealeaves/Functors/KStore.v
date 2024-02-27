From Tealeaves Require Export
  Functors.Batch
  Functors.Vector.

#[local] Generalizable Variables G ϕ.

Import Applicative.Notations.

(** * The [KStore] functor *)
(******************************************************************************)
Inductive KStore A B C :=
  { length : nat;
    contents : VEC length A;
    build : VEC length B -> C;
  }.

Definition kstore {A B : Type}: A -> KStore A B B :=
  fun a => Build_KStore A B B 1 (Vector.cons A a 0 (Vector.nil A)) unone.

(** ** Functor instance *)
(******************************************************************************)
Section map.

  Context
    {A B : Type}.

  Definition map_KStore : forall (C D : Type) (f : C -> D),
      KStore A B C -> KStore A B D.
  Proof.
    intros. destruct X.
    econstructor. eassumption.
    intros. apply f. auto.
  Defined.

  #[export] Instance Map_KStore : Map (KStore A B) := map_KStore.

  Lemma map_id_KStore : forall (C : Type),
      map (F := KStore A B) (@id C) = @id (KStore A B C).
  Proof.
    intros. ext k. destruct k as [len contents make].
    reflexivity.

  Qed.
  Lemma map_map_KStore : forall (C D E : Type) (f : C -> D) (g : D -> E),
      map (F := KStore A B) g ∘ map (F := KStore A B) f = map (F := KStore A B) (g ∘ f).
  Proof.
    intros. ext k. destruct k as [len contents make].
    reflexivity.
  Qed.

  #[export] Instance Functor_KStore : Functor (KStore A B) :=
    {| fun_map_id := @map_id_KStore;
      fun_map_map := @map_map_KStore;
    |}.

End map.

(** ** Applicative instance *)
(******************************************************************************)
Definition pure_KStore: forall (A B C : Type), C -> KStore A B C.
Proof.
  intros.
  apply (Build_KStore _ _ _ 0).
  apply Vector.nil.
  intros _; apply X.
Defined.

#[export] Instance Pure_KStore (A B : Type): Pure (KStore A B) :=
  pure_KStore A B.

Definition mult_KStore: forall (A B C D : Type),
    KStore A B C * KStore A B D -> KStore A B (C * D).
Proof.
  introv [k1 k2].
  destruct k1.
  destruct k2.
  apply (Build_KStore A B (C * D) (length0 + length1)).
  apply Vector.append; eauto.
  intro t.
  apply (VectorDef.splitat length0) in t.
  destruct t as [tc td].
  split; auto.
Defined.

#[export] Instance Mult_KStore (A B : Type):
  Mult (KStore A B) := mult_KStore A B.

#[export] Instance Applicative_KStore:
  forall (A B : Type), Applicative (KStore A B).
Admitted.

(** * Cata for <<KStore>> *)
(******************************************************************************)
Section cata.

  Context
    (A B : Type).

  Definition cata `{Mult G} `{Map G} `{Pure G}:
    forall (f : A -> G B) C, KStore A B C -> G C.
  Proof.
    intros f C [len contents make].
    pose (x := traverse (T := VEC len) (G := G) f contents).
    apply (map (F := G) make x).
  Defined.

  #[local] Instance Natural_cata:
    forall `{Applicative G} (f : A -> G B),
      Natural (cata f).
  Proof.
    constructor; try typeclasses eauto.
    intros. ext k.
    unfold compose. destruct k.
    cbn. compose near ((traverse (T := VEC length0) f contents0)) on left.
    rewrite (fun_map_map (F := G)).
    reflexivity.
  Qed.

  Lemma cata_kstore : forall C, cata kstore C = @id (KStore A B C).
  Proof.
    intros C. ext k. destruct k as [len contents make].
    unfold id.
    assert (lemma : traverse (T := VEC len)
                             (G := KStore A B) kstore contents =
              {| length := len; contents := contents; build := (@id _) |}).
    { clear. induction contents.
      - cbn. unfold_ops @Pure_KStore.
        unfold pure_KStore. fequal.
        ext b. rewrite toNil. reflexivity.
      - cbn.
        change_left (pure (F := KStore A B)
                          (Basics.flip (fun a : B => Vector.cons B a n))
                     <⋆> traverse (T := VEC n) (G := KStore A B) kstore contents0
                      <⋆> kstore h).
        rename h into a.
        rewrite IHcontents.
        unfold kstore.
        unfold ap.
        unfold_ops @Mult_KStore @Pure_KStore.
        unfold mult_KStore, pure_KStore.
        cbn.
        admit.
    }
    cbn.
    rewrite lemma.
    reflexivity.
  Admitted.

  Lemma cata_appmor
  `{ApplicativeMorphism G1 G2 ϕ}:
    forall (f : A -> G1 B) C, ϕ C ∘ cata f C = cata (ϕ B ∘ f) C.
  Proof.
    intros. ext k.
    inversion H5. unfold compose. induction k.
    cbn. rewrite appmor_natural.
    compose near (contents0).
    rewrite (trf_traverse_morphism (T := VEC length0)).
    reflexivity.
  Qed.

End cata.
