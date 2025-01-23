From Tealeaves Require Export
  Classes.Functor
  Classes.Kleisli.ContainerMonad
  Classes.Kleisli.Monad.

#[local] Generalizable Variables U T A B.

Import ContainerFunctor.Notations.

(** * Derived Properties of <<ContainerMonad>> *)
(******************************************************************************)
Section corollaries.

  Context
    `{ContainerMonad T}
    `{Map_inst: Map T}
    `{! Compat_Map_Bind T T}.

  (** ** <<ret>> is injective *)
  (******************************************************************************)
  Lemma ret_injective: forall (A: Type) (a a': A),
      ret a = ret a' -> a = a'.
  Proof.
    introv hyp.
    cut (tosubset (ret a) = tosubset (ret a')).
    compose near a.
    compose near a'.
    rewrite (kmon_hom_ret (ϕ := @tosubset T _)).
    now apply set_ret_injective.
    now rewrite hyp.
  Qed.

  (** ** Specification of <<a ∈ ret a'>> *)
  (******************************************************************************)
  Theorem in_ret_iff :
    forall (A: Type) (a1 a2: A), a1 ∈ ret a2 <-> a1 = a2.
  Proof.
    intros.
    compose near a2 on left.
    rewrite element_of_tosubset.
    reassociate -> on left.
    rewrite (kmon_hom_ret (ϕ := @tosubset T _)).
    easy.
  Qed.

  (** ** Specification of <<b ∈ bind f t>> *)
  (******************************************************************************)
  Theorem in_bind_iff :
    forall `(f: A -> T B) (t: T A) (b: B),
      b ∈ bind f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros. compose near t on left.
    rewrite element_of_tosubset.
    reassociate -> on left.
    rewrite (kmon_hom_bind (ϕ := @tosubset T _)).
    reflexivity.
  Qed.

  (** ** Respectfulness Properties for <<bind>> *)
  (******************************************************************************)
  (** This is just a more convenient name for consistency *)
  Corollary bind_respectful: forall (A B: Type) (t: T A) (f g: A -> T B),
      (forall a, a ∈ t -> f a = g a) -> bind f t = bind g t.
  Proof.
    exact contm_pointwise.
  Qed.

  Corollary bind_respectful_map :
    forall `(f1: A -> T B) `(f2: A -> B) (t: T A),
      (forall (a: A), a ∈ t -> f1 a = ret (f2 a)) -> bind f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite compat_map_bind.
    now eapply bind_respectful.
  Qed.

  Corollary bind_respectful_id :
    forall `(f1: A -> T A) (t: T A),
      (forall (a: A), a ∈ t -> f1 a = ret a) -> bind f1 t = t.
  Proof.
    introv hyp.
    change t with (id t) at 2.
    rewrite <- kmon_bind1.
    now apply bind_respectful.
  Qed.

End corollaries.

(** * Derived Properties of <<ContainerRightModule>> *)
(******************************************************************************)
Section corollaries.

  Context
    `{Return T}
    `{Module_inst: ContainerRightModule T U}
    `{Map_U_inst: Map U}
    `{! Compat_Map_Bind T U}.

  (** ** Specification of <<b ∈ bind f t>> *)
  (******************************************************************************)
  Theorem mod_in_bind_iff :
    forall `(f: A -> T B) (t: U A) (b: B),
      b ∈ bind f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros.
    compose near t on left.
    rewrite element_of_tosubset.
    reassociate -> on left.
    rewrite (kmodpar_hom_bind (ϕ := @tosubset U _)).
    reflexivity.
  Qed.

  (** ** Respectfulness Properties for <<bind>> *)
  (******************************************************************************)
  Corollary mod_bind_respectful: forall (A B: Type) (t: U A) (f g: A -> T B),
      (forall a, a ∈ t -> f a = g a) -> bind f t = bind g t.
  Proof.
    apply contmod_pointwise.
  Qed.

  Corollary mod_bind_respectful_map :
    forall `(f1: A -> T B) `(f2: A -> B) (t: U A),
      (forall (a: A), a ∈ t -> f1 a = ret (f2 a)) -> bind f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite compat_map_bind.
    now eapply mod_bind_respectful.
  Qed.

  Corollary mod_bind_respectful_id :
    forall `(f1: A -> T A) (t: U A),
      (forall (a: A), a ∈ t -> f1 a = ret a) ->
      bind f1 t = t.
  Proof.
    introv hyp.
    change t with (id t) at 2.
    rewrite <- (kmod_bind1 (U := U) (T := T)).
    now apply mod_bind_respectful.
  Qed.

End corollaries.

