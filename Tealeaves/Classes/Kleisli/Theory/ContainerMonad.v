From Tealeaves Require Export
  Classes.Functor
  Classes.Kleisli.ContainerMonad
  Classes.Kleisli.Theory.Monad.


Section corollaries.

  Context
    `{ContainerMonad T}
    `{Map_inst : Map T}
    `{! Compat_Map_Bind T T}.

  Lemma ret_injective : forall (A : Type) (a a' : A),
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

  Theorem in_ret_iff :
    forall (A : Type) (a1 a2 : A), a1 ∈ ret a2 <-> a1 = a2.
  Proof.
    intros.
    compose near a2 on left.
    rewrite element_of_tosubset.
    reassociate -> on left.
    rewrite (kmon_hom_ret (ϕ := @tosubset T _)).
    easy.
  Qed.

  Theorem in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros. compose near t on left.
    rewrite element_of_tosubset.
    reassociate -> on left.
    rewrite (kmon_hom_bind (ϕ := @tosubset T _)).
    reflexivity.
  Qed.

  Corollary bind_respectful : forall (A B : Type) (t : T A) (f g : A -> T B),
      (forall a, a ∈ t -> f a = g a) -> bind f t = bind g t.
  Proof.
    apply contm_pointwise.
  Qed.

  Corollary bind_respectful_map :
    forall `(f1 : A -> T B) `(f2 : A -> B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = ret (f2 a)) -> bind f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite compat_map_bind.
    now eapply bind_respectful.
  Qed.

  Corollary bind_respectful_id :
    forall `(f1 : A -> T A) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = ret a) -> bind f1 t = t.
  Proof.
    introv hyp.
    change t with (id t) at 2.
    rewrite <- kmon_bind1.
    now apply bind_respectful.
  Qed.

End corollaries.

Section corollaries.

  Context
    `{Module_inst: ContainerRightModule T U}
    `{Map_U_inst: Map U}
    `{! Compat_Map_Bind U T}.

  Theorem mod_in_bind_iff :
    forall `(f : A -> T B) (t : U A) (b : B),
      b ∈ bind f t <-> exists a, a ∈ t /\ b ∈ f a.
  Proof.
    intros.
    compose near t on left.
    rewrite element_of_tosubset.
    reassociate -> on left.
    rewrite (kmodpar_hom_bind (ϕ := @tosubset U _)).
    reflexivity.
  Qed.

  Corollary mod_bind_respectful : forall (A B : Type) (t : U A) (f g : A -> T B),
      (forall a, a ∈ t -> f a = g a) -> bind f t = bind g t.
  Proof.
    apply contmod_pointwise.
  Qed.

  Corollary mod_bind_respectful_map :
    forall `(f1 : A -> T B) `(f2 : A -> B) (t : U A),
      (forall (a : A), a ∈ t -> f1 a = ret (f2 a)) -> bind f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite compat_map_bind.
    now eapply mod_bind_respectful.
  Qed.

  Corollary mod_bind_respectful_id :
    forall `(f1 : A -> T A) (t : U A),
      (forall (a : A), a ∈ t -> f1 a = ret a) ->
      bind f1 t = t.
  Proof.
    introv hyp.
    change t with (id t) at 2.
    rewrite <- (kmod_bind1 (U := U) (T := T)).
    now apply mod_bind_respectful.
  Qed.

End corollaries.

