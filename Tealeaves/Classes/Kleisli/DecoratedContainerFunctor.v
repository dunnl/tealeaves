From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Categorical.ContainerFunctor
  Functors.Subset
  Functors.Ctxset
  Functors.Environment.

Import ContainerFunctor.Notations.
Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.

#[local] Generalizable Variables E T.

(** * Container-like functors with context *)
(******************************************************************************)

(** ** <<toctxset>> operation *)
(******************************************************************************)
Class ToCtxset (E : Type) (F : Type -> Type) :=
  toctxset : forall A : Type, F A -> ctxset E A.

#[global] Arguments toctxset {E}%type_scope {F}%function_scope
  {ToCtxset} {A}%type_scope _.

Definition element_ctx_of `{ToCtxset E T} {A: Type}:
  E * A -> T A -> Prop := fun p t => toctxset t p.

Lemma element_ctx_of_toctxset `{ToCtxset E T} {A: Type}:
  forall (p:E*A), element_ctx_of p = evalAt p ∘ toctxset.
Proof.
  reflexivity.
Qed.

#[local] Notation "x ∈d t" :=
  (element_ctx_of x t) (at level 50) : tealeaves_scope.

Section compat.

  Context
    `{ToCtxset_inst : ToCtxset E T}.

  Definition ToSubset_ToCtxset : ToSubset T :=
    fun A => map (F := subset) extract ∘ toctxset.

  Class Compat_ToSubset_ToCtxset
    `{ToSubset_inst : ToSubset T} : Prop :=
    compat_elements_elements_ctx :
      @tosubset T ToSubset_inst =
        @tosubset T ToSubset_ToCtxset.

  Lemma ind_iff_in
    `{Compat_ToSubset_ToCtxset}:
    forall (A : Type) (t : T A) (a : A),
      a ∈ t <-> exists (e: E), (e, a) ∈d t.
  Proof.
    intros.
    change_left ((evalAt a ∘ tosubset) t).
    rewrite compat_elements_elements_ctx.
    unfold_ops @ToSubset_ToCtxset.
    unfold_ops @Map_subset.
    unfold evalAt, compose.
    split.
    - intros [[e a'] [Hin Heq]].
      cbn in Heq. subst. eauto.
    - intros [e Hin].
      eauto.
  Qed.

  Lemma ind_implies_in
    `{Compat_ToSubset_ToCtxset}:
    forall (A : Type) (e : E) (a : A) (t : T A),
      (e, a) ∈d t -> a ∈ t.
  Proof.
    intros.
    rewrite ind_iff_in.
    eauto.
  Qed.

End compat.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedContainerFunctor
  (E : Type) (F : Type -> Type)
  `{Mapd E F} `{ToCtxset E F} :=
  { dcont_functor :> DecoratedFunctor E F;
    dcont_natural :> DecoratedNatural E F (ctxset E) (@toctxset E _ _);
    dcont_pointwise : forall (A B : Type) (t : F A) (f g : E * A -> B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> mapd f t = mapd g t;
  }.

Class DecoratedContainerFunctorFull
  (E : Type) (F : Type -> Type)
  `{Map F} `{Mapd E F}
  `{ToSubset F}
  `{ToCtxset E F} :=
  { dcontf_functor :> DecoratedFunctorFull E F;
    dcontf_dcont :> DecoratedContainerFunctor E F;
    dcontf_compat :> Compat_ToSubset_ToCtxset;
  }.

(** ** [ToCtxset]-preserving Natural transformations *)
(******************************************************************************)
Class DecoratedContainerTransformation
  {E : Type} {F G : Type -> Type}
  `{Map F} `{Mapd E F} `{ToCtxset E F}
  `{Map G} `{Mapd E G} `{ToCtxset E G}
  (η : F ⇒ G) :=
  { dcont_trans_natural : Natural η;
    dcont_trans_commute :
    forall A, toctxset (F := F) = toctxset (F := G) ∘ η A;
  }.

(** * Container instance for <<ctxset>> *)
(******************************************************************************)
Section Container_ctxset.

  Context {E: Type}.

  Instance ToCtxset_ctxset : ToCtxset E (ctxset E) :=
    fun (A : Type) (s : ctxset E A) => s.

  Instance Natural_elements_ctx_ctxset :
    DecoratedNatural E (ctxset E) (ctxset E)
      (@toctxset E (ctxset E) _).
  Proof.
    constructor. reflexivity.
  Qed.

  Lemma ctxset_pointwise : forall (A B : Type) (t : ctxset E A) (f g : E * A -> B),
      (forall (e : E) (a : A), (e, a) ∈d t -> f (e, a) = g (e, a)) ->
      mapd f t = mapd g t.
  Proof.
    introv hyp. ext [e b]. cbv in *. propext.
    - intros [a [Hin Heq]].
      specialize (hyp e a Hin).
      subst. eauto.
    - intros [a [Hin Heq]].
      specialize (hyp e a Hin).
      subst. eauto.
  Qed.

  Instance ContainerFunctor_ctxset : DecoratedContainerFunctor E (ctxset E) :=
    {| dcont_pointwise := ctxset_pointwise;
    |}.

End Container_ctxset.

(** * Basic properties of decorated containers *)
(******************************************************************************)
Section setlike_functor_theory.

  Context
    `{DecoratedFunctor E T}
    `{Map_inst : Map T}
    `{! Compat_Map_Mapd}
    `{ToCtxset E T}
    `{ToSubset_inst : ToSubset T}
    `{! Compat_ToSubset_ToCtxset}
    `{! DecoratedContainerFunctor E T}
    {A B : Type}.

  Implicit Types (t : T A) (b : B) (e : E) (a : A).

  (** ** Interaction between (∈d) and <<mapd>> *)
  (******************************************************************************)
  Theorem ind_mapd_iff : forall e t f b,
      (e, b) ∈d mapd f t <-> exists a : A, (e, a) ∈d t /\ f (e, a) = b.
  Proof.
    introv.
    compose near t on left.
    rewrite element_ctx_of_toctxset.
    reassociate -> on left.
    rewrite <- (dec_natural (ϕ := @toctxset E T _)).
    reflexivity.
  Qed.

  Corollary in_mapd_iff : forall t f b,
      b ∈ mapd f t <-> exists (e : E) (a : A), (e, a) ∈d t /\ f (e, a) = b.
  Proof.
    introv.
    rewrite ind_iff_in.
    setoid_rewrite ind_mapd_iff.
    reflexivity.
  Qed.

  Corollary ind_map_iff : forall e t f b,
      (e, b) ∈d map f t <-> exists a : A, (e, a) ∈d t /\ f a = b.
  Proof.
    introv.
    rewrite DecoratedFunctor.map_to_mapd.
    rewrite ind_mapd_iff.
    reflexivity.
  Qed.

  Corollary ind_mapd_mono : forall t e a (f : E * A -> B),
      (e, a) ∈d t -> (e, f (e, a)) ∈d mapd f t.
  Proof.
    introv. rewrite ind_mapd_iff. now exists a.
  Qed.

  Corollary ind_map_mono : forall t e a (f : A -> B),
      (e, a) ∈d t -> (e, f a) ∈d map f t.
  Proof.
    introv. rewrite ind_map_iff. now exists a.
  Qed.

  Corollary mapd_respectful : forall t (f g : E * A -> A),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> mapd f t = mapd g t.
  Proof.
    apply dcont_pointwise.
  Qed.

  Corollary mapd_respectful_id : forall t (f : E * A -> A),
      (forall e a, (e, a) ∈d t -> f (e, a) = a) -> mapd f t = t.
  Proof.
    introv hyp.
    change t with (id t) at 2.
    rewrite <- (fun_map_id (Functor := Functor_instance_0)).
    rewrite DecoratedFunctor.map_to_mapd.
    apply dcont_pointwise.
    apply hyp.
  Qed.

End setlike_functor_theory.

(** * Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈d t" :=
  (element_ctx_of x t) (at level 50) : tealeaves_scope.

End Notations.

(** * Instance for <<env>> *)
(******************************************************************************)
Section env_instance.

  Context {E : Type}.

#[export] Instance ToCtxset_env : ToCtxset E (env E) :=
  fun (A : Type) (s : env E A) =>
    tosubset (F := list) s.

#[export] Instance DecoratedNatural_toctxset_env :
  DecoratedNatural E (env E) (ctxset E) (@toctxset E (env E) _).
Proof.
  constructor. intros.
  ext Γ [e b].
  unfold_ops @ToCtxset_env @Mapd_ctxset.
  unfold compose.
  induction Γ.
  - cbn. propext.
    + intros [a [contra heq]]. contradiction.
    + contradiction.
  - destruct a as [e' a].
    change_right ((e', f (e', a)) = (e, b) \/ (e, b) ∈d mapd f Γ).
    setoid_rewrite <- IHΓ; clear IHΓ.
    autorewrite with tea_list.
    propext.
    + intros [a' [[Hin|Hin] Heq]].
      * left.
        autorewrite with tea_set in *.
        now inversion Hin; subst.
      * right. now exists a'.
    + intros [Heq | [a' [Hin Heq]]].
      * inversion Heq; subst. exists a.
        autorewrite with tea_set.
        intuition.
      * exists a'.
        autorewrite with tea_set.
        intuition.
Qed.

#[export] Instance Natural_ToCtxset_env :
  Natural (@toctxset E (env E) _).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - unfold_ops @ToCtxset_env.
    intros.
    rewrite ctxset_map_spec.
    rewrite (natural (A := E * A)
                     (B := E * B)
                     (ϕ := @tosubset list _)).
    rewrite env_map_spec.
    reflexivity.
Qed.

End env_instance.
