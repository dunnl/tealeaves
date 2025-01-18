From Tealeaves Require Export
  Functors.List
  Functors.Early.Environment
  Classes.Kleisli.DecoratedContainerFunctor.

Import DecoratedContainerFunctor.Notations.

(** * Instance for <<env>> *)
(******************************************************************************)
Section env_instance.

  Context {E: Type}.

  #[export] Instance ToCtxset_env: ToCtxset E (env E) :=
    fun (A: Type) (s: env E A) =>
      tosubset (F := list) s.

#[export] Instance DecoratedHom_toctxset_env :
  DecoratedHom E (env E) (ctxset E) (@toctxset E (env E) _).
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
  - try typeclasses eauto. admit.
  - typeclasses eauto.
  - unfold_ops @ToCtxset_env.
    intros.
    rewrite ctxset_map_spec.
    rewrite (natural (A := E * A)
                     (B := E * B)
                     (ϕ := @tosubset list _)).
    rewrite env_map_spec.
    reflexivity.
Admitted.

End env_instance.



