
(** * Equivalence between monads and Kleisli triples *)
(******************************************************************************)
Class KleisliMonad T `{Return T} `{Bind T} :=
  { kmon_bind_ret_r : forall `(f : A -> T B),
      bind T f ∘ ret T = f;
    kmon_bind_ret_l :
      `(bind T (ret T) = @id (T A));
    kmon_bind_bind : forall `(g : B -> T C) `(f : A -> T B),
        bind T g ∘ bind T f = bind T (bind T g ∘ f);
  }.

Section KleisliMonad_of_Monad.

  Context
    `{Monad T}.

  Instance KleisliMonad_Monad : KleisliMonad T :=
    {| kmon_bind_ret_l := mon_join_fmap_ret T;
       kmon_bind_ret_r := fun A B => bind_comp_ret T;
       kmon_bind_bind := fun B C => bind_bind T ;
    |}.

End KleisliMonad_of_Monad.

Section Monad_of_KleisliMonad.

  Context
    `{KleisliMonad T}.

  Instance Fmap_Kleisli : Fmap T :=
    fun A B (f : A -> B) => bind T (ret T ∘ f).

  Lemma fmap_id_Kleisli : forall A, fmap T (@id A) = @id (T A).
  Proof.
    intros. unfold_ops @Fmap_Kleisli.
    apply kmon_bind_ret_l.
  Qed.

  Lemma fmap_fmap_Kleisli : forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap T g ∘ fmap T f = fmap T (g ∘ f).
  Proof.
    intros. unfold_ops @Fmap_Kleisli.
    rewrite kmon_bind_bind. reassociate <- on left.
    now rewrite kmon_bind_ret_r.
  Qed.

  Instance Functor_Kleisli : Functor T :=
    {| Functor.fun_fmap_id := fmap_id_Kleisli;
       Functor.fun_fmap_fmap := fmap_fmap_Kleisli;
    |}.

  Instance Join_Kleisli : Join T := fun A => bind T (@id (T A)).

  Lemma join_ret_Kleisli : forall (A : Type), join T ∘ ret T = @id (T A).
  Proof.
    intros. unfold_ops @Join_Kleisli.
    unfold_compose_in_compose.
    now rewrite kmon_bind_ret_r.
  Qed.

  Lemma join_fmap_ret_Kleisli : forall (A : Type), join T ∘ fmap T (ret T) = @id (T A).
  Proof.
    intros. unfold_ops @Join_Kleisli @Fmap_Kleisli.
    unfold_compose_in_compose.
    rewrite kmon_bind_bind.
    rewrite <- kmon_bind_ret_l.
    reassociate <- on left.
    now do 2 rewrite kmon_bind_ret_r.
  Qed.

  Lemma join_fmap_join_Kleisli : forall (A : Type),
      join T ∘ join T = join T ∘ fmap T (join T) (A:=(T (T A))).
  Proof.
    intros. unfold_ops @Join_Kleisli @Fmap_Kleisli.
    unfold_compose_in_compose.
    do 2 rewrite kmon_bind_bind.
    reassociate <- on right.
    now rewrite kmon_bind_ret_r.
  Qed.

  Lemma Natural_Ret_Kleisli : Natural (fun A => ret T).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold_ops @Fmap_Kleisli.
    now rewrite kmon_bind_ret_r.
  Qed.

  Lemma Natural_Join_Kleisli : Natural (fun A => join (A:=A) T).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold_ops @Join_Kleisli @Fmap_compose @Fmap_Kleisli.
    unfold_compose_in_compose.
    unfold fmap. repeat rewrite kmon_bind_bind.
    reassociate <-. change (?f ∘ id) with f.
    now rewrite kmon_bind_ret_r.
  Qed.

  Instance Monad_Kleisli : Monad T :=
    {| mon_join_ret := join_ret_Kleisli;
       mon_join_fmap_ret := join_fmap_ret_Kleisli;
       mon_join_join := join_fmap_join_Kleisli;
       mon_ret_natural := Natural_Ret_Kleisli;
       mon_join_natural := Natural_Join_Kleisli;
    |}.

End Monad_of_KleisliMonad.
