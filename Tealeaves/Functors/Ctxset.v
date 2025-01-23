From Tealeaves Require Export
  Functors.Early.Ctxset
  Classes.Kleisli.DecoratedContainerFunctor
  Classes.Kleisli.Theory.DecoratedContainerFunctor.

Import DecoratedContainerFunctor.Notations.

(** * <<DecoratedContainerFunctor>> Instance for <<ctxset>> *)
(******************************************************************************)
Section Container_ctxset.

  Context {E: Type}.

  #[local] Instance ToCtxset_ctxset: ToCtxset E (ctxset E) :=
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

  #[local] Instance DecoratedContainerFunctor_ctxset:
    DecoratedContainerFunctor E (ctxset E) :=
    {| dcont_pointwise := ctxset_pointwise;
    |}.

End Container_ctxset.
