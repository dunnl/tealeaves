From Tealeaves Require Import
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.Theory.DecoratedFunctor.

#[local] Generalizable Variables E T.

Import DecoratedContainerFunctor.Notations.
Import ContainerFunctor.Notations.
Import Subset.Notations.

(** ** Compatibility *)
(******************************************************************************)
Section compat.

  Context
    `{ToCtxset_inst: ToCtxset E T}.

  Definition ToSubset_ToCtxset: ToSubset T :=
    fun A => map (F := subset) extract ∘ toctxset.

  Class Compat_ToSubset_ToCtxset
    `{ToSubset_inst: ToSubset T}: Prop :=
    compat_elements_elements_ctx :
      @tosubset T ToSubset_inst =
        @tosubset T ToSubset_ToCtxset.

  Lemma ind_iff_in
    `{Compat_ToSubset_ToCtxset}:
    forall (A: Type) (t: T A) (a: A),
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
    forall (A: Type) (e: E) (a: A) (t: T A),
      (e, a) ∈d t -> a ∈ t.
  Proof.
    intros.
    rewrite ind_iff_in.
    eauto.
  Qed.

End compat.

(*
Class DecoratedContainerFunctorFull
  (E: Type) (F: Type -> Type)
  `{Map F} `{Mapd E F}
  `{ToSubset F}
  `{ToCtxset E F} :=
  { dcontf_functor :> DecoratedFunctorFull E F;
    dcontf_dcont :> DecoratedContainerFunctor E F;
    dcontf_compat :> Compat_ToSubset_ToCtxset;
  }.
 *)

(** * Container instance for <<ctxset>> *)
(******************************************************************************)
Section Container_ctxset.

  Context {E: Type}.

  Instance ToCtxset_ctxset: ToCtxset E (ctxset E) :=
    fun (A: Type) (s: ctxset E A) => s.

  Instance Natural_elements_ctx_ctxset :
    DecoratedHom E (ctxset E) (ctxset E)
      (@toctxset E (ctxset E) _).
  Proof.
    constructor. reflexivity.
  Qed.

  Lemma ctxset_pointwise: forall (A B: Type) (t: ctxset E A) (f g: E * A -> B),
      (forall (e: E) (a: A), (e, a) ∈d t -> f (e, a) = g (e, a)) ->
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

  Instance ContainerFunctor_ctxset: DecoratedContainerFunctor E (ctxset E) :=
    {| dcont_pointwise := ctxset_pointwise;
    |}.

End Container_ctxset.

(** * Basic properties of decorated containers *)
(******************************************************************************)
Section decorated_container_functor_theory.

  Context
    `{DecoratedFunctor E T}
    `{Map_T: Map T}
    `{ToCtxset_ET: ToCtxset E T}
    `{ToSubset_T: ToSubset T}
    `{! Compat_Map_Mapd E T}
    `{! Compat_ToSubset_ToCtxset}
    `{! DecoratedContainerFunctor E T}
    {A B: Type}.

  Implicit Types (t: T A) (b: B) (e: E) (a: A).

  (** ** Interaction between (∈d) and <<mapd>> *)
  (******************************************************************************)
  Theorem ind_mapd_iff: forall e t f b,
      (e, b) ∈d mapd f t <-> exists a: A, (e, a) ∈d t /\ f (e, a) = b.
  Proof.
    introv.
    compose near t on left.
    rewrite element_ctx_of_toctxset.
    reassociate -> on left.
    rewrite <- (dhom_natural (ϕ := @toctxset E T _)).
    reflexivity.
  Qed.

  Corollary in_mapd_iff: forall t f b,
      b ∈ mapd f t <-> exists (e: E) (a: A), (e, a) ∈d t /\ f (e, a) = b.
  Proof.
    introv.
    rewrite ind_iff_in.
    setoid_rewrite ind_mapd_iff.
    reflexivity.
  Qed.

  Corollary ind_map_iff: forall e t f b,
      (e, b) ∈d map f t <-> exists a: A, (e, a) ∈d t /\ f a = b.
  Proof.
    introv.
    rewrite map_to_mapd.
    rewrite ind_mapd_iff.
    reflexivity.
  Qed.

  Corollary ind_mapd_mono: forall t e a (f: E * A -> B),
      (e, a) ∈d t -> (e, f (e, a)) ∈d mapd f t.
  Proof.
    introv. rewrite ind_mapd_iff. now exists a.
  Qed.

  Corollary ind_map_mono: forall t e a (f: A -> B),
      (e, a) ∈d t -> (e, f a) ∈d map f t.
  Proof.
    introv. rewrite ind_map_iff. now exists a.
  Qed.

  Corollary mapd_respectful: forall t (f g: E * A -> A),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> mapd f t = mapd g t.
  Proof.
    apply dcont_pointwise.
  Qed.

  Corollary mapd_respectful_id: forall t (f: E * A -> A),
      (forall e a, (e, a) ∈d t -> f (e, a) = a) -> mapd f t = t.
  Proof.
    introv hyp.
    change t with (id t) at 2.
    rewrite <- fun_map_id.
    rewrite map_to_mapd.
    apply dcont_pointwise.
    apply hyp.
  Qed.

End decorated_container_functor_theory.
