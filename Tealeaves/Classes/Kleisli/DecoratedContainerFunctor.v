From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Categorical.ContainerFunctor
  Functors.Subset
  Functors.Ctxset
  Functors.Environment.

Import Monoid.Notations.
Import Functor.Notations.
Import Subset.Notations.
Import List.ListNotations.

(** * Decorated container functors *)
(******************************************************************************)
Class CtxElements (E : Type) (F : Type -> Type) :=
  ctx_element_of : forall A : Type, F A -> ctxset E A.

#[global] Arguments ctx_element_of {E}%type_scope {F}%function_scope
  {CtxElements} {A}%type_scope _.

#[local] Notation "x ∈d t" :=
  (ctx_element_of t x) (at level 50) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedContainerFunctor
  (E : Type) (F : Type -> Type)
  `{Map F} `{Mapd E F} `{CtxElements E F} :=
  { dcont_functor :> DecoratedFunctorFull E F;
    dcont_natural :> DecoratedNatural E F (ctxset E) (@ctx_element_of E _ _);
    dcont_pointwise : forall (A B : Type) (t : F A) (f g : E * A -> B),
      (forall e a, (e, a) ∈d t -> f (e, a) = g (e, a)) -> mapd f t = mapd g t;
  }.

(** ** Natural transformations *)
(******************************************************************************)
Class DecoratedContainerTransformation
  {E : Type} {F G : Type -> Type}
  `{Map F} `{Mapd E F} `{CtxElements E F}
  `{Map G} `{Mapd E G} `{CtxElements E G}
  (η : F ⇒ G) :=
  { dcont_trans_natural : Natural η;
    dcont_trans_commute :
    forall A, ctx_element_of (F := F) = ctx_element_of (F := G) ∘ η A;
  }.

(** ** Instance for <<env>> *)
(******************************************************************************)
#[export] Instance CtxElements_env (E : Type) : CtxElements E (env E) :=
  fun (A : Type) (s : env E A) => element_of (F := list) s.

#[export] Instance DecoratedNatural_ctxelements_env (E : Type) :
  DecoratedNatural E (env E) (ctxset E) (@ctx_element_of E (env E) _).
Proof.
  constructor. intros.
  ext Γ [e b].
  unfold compose; unfold_ops @Mapd_ctxset.
  induction Γ.
  - cbn. propext.
    + intros. now preprocess.
    + easy.
  - preprocess.
    change_right ((e0, f (e0, a)) = (e, b) \/ (e, b) ∈d mapd f Γ).
    rewrite <- IHΓ. clear IHΓ. propext.
    + intros [a' [[Hin|Hin] Heq]].
      * left. inversion Hin; now subst.
      * right. exists a'. easy.
    + intros [Heq | [a' [Hin Heq]]].
      * inversion Heq; subst. exists a.
        split; now try left.
      * exists a'. split; now try right.
Qed.

#[export] Instance Natural_Elementd_Mapdt (E : Type) :
  Natural (@ctx_element_of E (env E) _).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
Abort.

(** ** Basic properties of containers *)
(******************************************************************************)
Section setlike_functor_theory.

  Context
    (E : Type)
    (F : Type -> Type)
    `{DecoratedContainerFunctor E F}
    {A B : Type}.

  Implicit Types (t : F A) (b : B) (e : E) (a : A).

  Theorem ind_mapd_iff : forall e t f b,
      (e, b) ∈d mapd f t <-> exists a : A, (e, a) ∈d t /\ f (e, a) = b.
  Proof.
    introv. compose near t on left.
    rewrite <- dec_natural.
    reflexivity.
  Qed.

  Theorem ind_map_iff : forall e t f b,
      (e, b) ∈d map f t <-> exists a : A, (e, a) ∈d t /\ f a = b.
  Proof.
    introv.
    rewrite dfunf_map_to_mapd.
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

  Corollary mapd_respectful_id : forall t (f : E * A -> A),
      (forall e a, (e, a) ∈d t -> f (e, a) = a) -> mapd f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (fun_map_id).
    rewrite (dfunf_map_to_mapd).
    apply dcont_pointwise.
    apply hyp.
  Qed.

End setlike_functor_theory.

Module Notations.

  Notation "x ∈d t" :=
    (ctx_element_of t x) (at level 50) : tealeaves_scope.

End Notations.
