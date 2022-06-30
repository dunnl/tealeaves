From Tealeaves Require Export
     Classes.Bimonad
     Classes.RightModule.

Import Product.Notations.
Import Functor.Notations.
Import Monoid.Notations.
Import Monad.Notations.
#[local] Open Scope tealeaves_scope.

(** * Product functor *)
(** For any type [A], there is an endofunctor whose object map is
    <<fun B => prod A B>>. *)
(******************************************************************************)
Instance Fmap_prod {X} : Fmap (X ×) := (fun A B => map_snd).

#[program] Instance Functor_prod X : Functor (X ×).

Solve All Obligations with (introv; now ext [? ?]).

(** ** Properties of <<strength>> w.r.t. monad operations *)
(** Formalizing the product functor allows expressing some general
    properties about how the monad operations interact with the
    tensorial strength operation. These laws play a role in reasoning
    about decorated monads in particular. *)
(******************************************************************************)
Section Monad_strength_laws.

  Context
    (T : Type -> Type)
    {W : Type}
    `{Monad T}.

  Lemma strength_ret : forall (A : Type),
      σ T ∘ fmap (W ×) (ret T) = ret T (A := W * A).
  Proof.
    intros. ext [w a]. unfold compose; cbn. compose near a on left.
    now rewrite (natural (G := T) (F := fun A => A)).
  Qed.

  Lemma strength_join : forall (A : Type),
      σ T ∘ fmap (W ×) (μ T) =
      μ T (A := W * A) ∘ fmap T (σ T) ∘ σ T.
  Proof.
    intros. ext [w t]. change_left (σ T (w, μ T t)).
    unfold strength, compose.
    compose near t on right.
    rewrite (fun_fmap_fmap T).
    unfold compose. change_right (μ T (fmap (T ∘ T) (pair w) t)).
    compose near t on right. now rewrite <- (natural (F := T ∘ T)).
  Qed.

  Context
    (F : Type -> Type)
    `{RightModule F T}.

  Lemma strength_right_action : forall (A : Type),
      σ F ∘ fmap (W ×) (right_action F) =
      right_action F (A := W * A) ∘ fmap F (σ T) ∘ σ F.
  Proof.
    intros. ext [w t]. change_left (σ F (w, right_action F t)).
    unfold strength, compose.
    compose near t on right.
    rewrite (fun_fmap_fmap F).
    unfold compose. change_right (right_action F (fmap (F ∘ T) (pair w) t)).
    compose near t on right. now rewrite <- (natural (F := F ∘ T)).
  Qed.

End Monad_strength_laws.

(** * Product comonad (a/k/a the"Reader" comonad) *)
(** The properties of Cartesian products imply the product functor (by
    any type <<W>>) forms a comonad. This comonad is sometimes called
    "Reader" in the Haskell community (or sometimes "co-Reader")
    because it is the comonad formed by taking the so-called Reader
    monad across the product/exponent adjunction. It is also sometimes
    called the Writer comonad because it shares the same underlying
    object-map as the Writer monad, although its semantics are a form
    of reading rather than writing.

    The extract operation is projection to the second element. The
    duplication operation makes two copies of the first element. *)
(******************************************************************************)
Lemma dup_left_spec {A B} :
    @dup_left A B  = α ∘ map_fst comonoid_comult.
Proof.
  now ext [? ?].
Qed.

Section reader_comonad_instance.

  Context
    `{W : Type}.

  #[global] Instance Cojoin_prod : Cojoin (W ×) :=
    @dup_left W.

  #[global] Instance Extract_prod : Extract (W ×) :=
    @snd W.

  #[global] Instance Natural_extract_prod : Natural (@extract (W ×) _).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [? ?].
  Qed.

  #[global] Instance Natural_cojoin_prod : Natural (@cojoin (W ×) _).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [? ?].
  Qed.

  #[global, program] Instance Comonad_prod : Comonad (W ×).

  Solve All Obligations with (introv; now ext [? ?]).

End reader_comonad_instance.

(** ** Miscellaneous properties *)
(******************************************************************************)
Section miscellaneous.

  Context
    {W : Type}.

  Theorem strength_extract `{Functor F} :
    `(fmap F (extract (W ×)) ∘ σ F = extract (W ×) (A := F A)).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite (fun_fmap_fmap F), (fun_fmap_id F).
  Qed.

  Theorem strength_cojoin `{Functor F} :
    `(fmap F (cojoin (W ×)) ∘ σ F = σ F ∘ cobind (W ×) (σ F) (A := F A)).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite 2(fun_fmap_fmap F).
  Qed.

  Theorem product_fmap_commute {W1 W2 A B : Type} (g : W1 -> W2) (f : A -> B) :
    fmap (W2 ×) f ∘ map_fst g = map_fst g ∘ fmap (W1 ×) f.
  Proof.
    now ext [w a].
  Qed.

End miscellaneous.

(** * Writer monad *)
(** In the even that [A] is a monoid, the product functor forms a monad. The
    return operation maps <<b>> to <<(1, b)>> where <<1>> is the monoid unit.
    The join operation monoidally combines the two monoid values. *)
(******************************************************************************)
Section writer_monad.

  Context
    `{Monoid X}.

  #[global] Instance Join_writer : Join (prod X) :=
    fun A (p : X * (X * A)) => map_fst (uncurry (@monoid_op X _)) (α^-1 p).

  #[global] Instance Return_writer : Return (prod X) :=
    fun A (a : A) => (Ƶ, a).

  #[global] Instance Natural_ret_writer : Natural (@ret (prod X) Return_writer).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. now ext a.
  Qed.

  #[global] Instance Natural_join_writer : Natural (@join (prod X) Join_writer).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [x [x' a]].
  Qed.

  #[global, program] Instance Monad_writer : Monad (prod X).

  Solve Obligations with
      (intros; unfold transparent tcs; ext p;
      unfold compose in *; destruct_all_pairs;
      cbn; now simpl_monoid).

End writer_monad.

(** * Writer bimonad *)
(******************************************************************************)
Instance BeckDistribution_strength (W : Type) (T : Type -> Type) `{Fmap T}:
  BeckDistribution (W ×) T := (fun A => σ T).

(** ** <<T ∘ (W ×)>> is a monad *)
(******************************************************************************)
Instance Natural_strength `{Functor F} {W : Type} : Natural (F := prod W ∘ F) (@strength F _ W).
Proof.
  constructor; try typeclasses eauto.
  intros. unfold_ops @Fmap_compose. ext [a t].
  unfold compose; cbn.
  compose near t on left.
  compose near t on right.
  now rewrite 2(fun_fmap_fmap F).
Qed.

Section strength_as_writer_distributive_law.

  Context
    `{Monoid W}.

  Lemma strength_ret_l `{Functor T} : forall A : Type,
      σ T ∘ ret (W ×) (A := T A) =
      fmap T (ret (W ×)).
  Proof.
    reflexivity.
  Qed.

  Lemma strength_join_l `{Functor T} : forall A : Type,
      σ T ∘ join (W ×) (A := T A) =
      fmap T (join (W ×)) ∘ σ T ∘ fmap (W ×) (σ T).
  Proof.
    intros. ext [w1 [w2 t]]. unfold compose; cbn.
    compose near t. rewrite (fun_fmap_fmap T).
    compose near t on right. rewrite (fun_fmap_fmap T).
    reflexivity.
  Qed.

  Context
    `{Monad T}.

  #[global, program] Instance BeckDistributiveLaw_strength :
    BeckDistributiveLaw (W ×) T :=
    {| dist_join_r := strength_join T;
       dist_unit_r := strength_ret T;
       dist_join_l := strength_join_l;
       dist_unit_l := strength_ret_l;
    |}.

  #[global] Instance: Monad (T ∘ (W ×)) := Monad_Beck.

End strength_as_writer_distributive_law.

(** ** <<(W ×)>> is a bimonad *)
(******************************************************************************)
Section writer_bimonad_instance.

  Context
    `{Monoid W}.

  Lemma writer_dist_involution : forall (A : Type),
      bdist (prod W) (prod W) ∘ bdist (prod W) (prod W) = @id (W * (W * A)).
  Proof.
    intros. now ext [? [? ?]].
  Qed.

  Lemma bimonad_dist_counit_l : forall A,
      extract (W ×) ∘ bdist (W ×) (W ×) =
      fmap (W ×) (extract (W ×) (A := A)).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_dist_counit_r : forall A,
      fmap (W ×) (extract (W ×)) ∘ bdist (W ×) (W ×) =
      extract (W ×) (A := W * A).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_baton : forall A,
      extract (W ×) ∘ ret (W ×) = @id A.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma bimonad_cup : forall A,
      cojoin (W ×) ∘ ret (W ×) = ret (W ×) ∘ ret (W ×) (A := A).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma bimonad_cap : forall A,
      extract (W ×) ∘ join (W ×) = extract (W ×) ∘ extract (W ×) (A := W * A).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_butterfly : forall A,
      cojoin (W ×) ∘ join (W ×) (A := A) =
      fmap (W ×) (join (W ×)) ∘ join (W ×) ∘ fmap (W ×) (bdist (W ×) (W ×))
           ∘ cojoin (W ×) ∘ fmap (W ×) (cojoin (W ×)).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  #[global] Instance Bimonad_Writer : Bimonad (W ×) :=
    {| bimonad_monad := Monad_writer;
       bimonad_comonad := Comonad_prod;
       Bimonad.bimonad_dist_counit_l := @bimonad_dist_counit_l;
       Bimonad.bimonad_dist_counit_r := @bimonad_dist_counit_r;
       Bimonad.bimonad_distributive_law := BeckDistributiveLaw_strength;
       Bimonad.bimonad_cup := @bimonad_cup;
       Bimonad.bimonad_cap := @bimonad_cap;
       Bimonad.bimonad_baton := @bimonad_baton;
       Bimonad.bimonad_butterfly := @bimonad_butterfly;
    |}.

End writer_bimonad_instance.

(** ** Miscellaneous properties *)
(******************************************************************************)
Section Writer_miscellaneous.

  Context
    `{Monoid W}.

  (* It sometimes useful to have this curried operation. *)
  Definition incr {A : Type} : W -> W * A -> W * A :=
    fun w '(w2, a) => (w ● w2, a).

  Lemma extract_incr {A : Type} :
    forall (w : W), extract (W ×) ∘ incr w = extract (W ×) (A := A).
  Proof.
    intros. now ext [w' a].
  Qed.

  (* This rewrite is useful when proving decoration-traversal compatibility
     in the binder case. *)
  Theorem strength_shift1 : forall `{Functor F} (w : W) (A : Type),
      σ F ∘ μ (W ×) ∘ pair w = fmap F (μ (W ×) ∘ pair w) ∘ σ F (B := A).
  Proof.
    intros. ext [w' x]. unfold compose; cbn.
    compose near x. now rewrite (fun_fmap_fmap F).
  Qed.

End Writer_miscellaneous.
