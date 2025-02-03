From Tealeaves Require Export
  Functors.List
  Functors.Early.Environment
  Classes.Kleisli.Theory.DecoratedTraversableFunctor.

Import Subset.Notations.
Import DecoratedContainerFunctor.Notations.
Import List.ListNotations.

(** * Decorated Container Instance for <<env>> *)
(**********************************************************************)
Section env_instance.

  Context {E: Type}.

  #[export] Instance ToCtxset_env: ToCtxset E (env E) :=
    fun (A: Type) (s: env E A) =>
      tosubset (F := list) s.

  #[export] Instance Compat_ToCtxset_Mapdt_env:
    Compat_ToCtxset_Mapdt E (env E).
  Proof.
    (* TODO *)
  Admitted.

  (** ** Rewriting Rules for <<toctxset>> *)
  (********************************************************************)
  Lemma toctxset_env_nil: forall (A: Type),
      toctxset (F := env E) (@nil (E * A)) = subset_empty.
  Proof.
    reflexivity.
  Qed.

  Lemma toctxset_env_one: forall (A: Type) (e: E) (a: A),
      toctxset (F := env E) [(e, a)] = {{ (e, a) }}.
  Proof.
    intros. unfold_ops @ToCtxset_env.
    simpl_list. simpl_subset.
    reflexivity.
  Qed.

  Lemma toctxset_env_cons: forall (A: Type) (e: E) (a: A) (l: env E A),
      toctxset (F := env E) ((e, a) :: l) =
        {{(e, a)}} ∪ (toctxset l).
  Proof.
    reflexivity.
  Qed.

  Lemma toctxset_env_app: forall (A: Type) (l1 l2: env E A),
      toctxset (F := env E) (l1 ++ l2) =
        toctxset l1 ∪ toctxset l2.
  Proof.
    intros. unfold_ops @ToCtxset_env.
    simpl_list.
    reflexivity.
  Qed.

  (** ** Naturality *)
  (********************************************************************)
  #[export] Instance Natural_ToCtxset_env:
    Natural (@toctxset E (env E) _).
  Proof.
    constructor.
    - try typeclasses eauto.
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

  (** ** <<toctxset>> is a Homomorphism of Decorated Functors *)
  (********************************************************************)
  #[export] Instance DecoratedHom_toctxset_env:
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
        * right.
          now (exists a').
      + intros [Heq | [a' [Hin Heq]]].
        * inversion Heq; subst. exists a.
          autorewrite with tea_set.
          intuition.
        * exists a'.
          autorewrite with tea_set.
          intuition.
  Qed.

End env_instance.
