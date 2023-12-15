From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.Bimonad
  Classes.Categorical.RightModule
  Functors.Categorical.Environment
  Misc.Product.

Import Strength.Notations.
Import Monad.Notations.
Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables W T F A M.
#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments extract (W)%function_scope {Extract} (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin} {A}%type_scope _.

(** * Writer monad *)
(** In the even that [A] is a monoid, the product functor forms a monad. The
    return operation maps <<b>> to <<(1, b)>> where <<1>> is the monoid unit.
    The join operation monoidally combines the two monoid values. *)
(******************************************************************************)
Section writer_monad.

  Context
    `{Monoid M}.

  #[export] Instance Join_writer : Join (prod M) :=
    fun A (p : M * (M * A)) => map_fst (uncurry (@monoid_op M _)) (α^-1 p).

  #[export] Instance Return_writer : Return (prod M) :=
    fun A (a : A) => (Ƶ, a).

  #[export] Instance Natural_ret_writer : Natural (@ret (prod M) Return_writer).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. now ext a.
  Qed.

  #[export] Instance Natural_join_writer : Natural (@join (prod M) Join_writer).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [x [x' a]].
  Qed.

  #[export, program] Instance Monad_writer : Monad (prod M).

  Solve Obligations with
      (intros; unfold transparent tcs; ext p;
      unfold compose in *; destruct_all_pairs;
      cbn; now simpl_monoid).

End writer_monad.

(** * Writer bimonad *)
(******************************************************************************)
#[export] Instance BeckDistribution_strength (W : Type) (T : Type -> Type) `{Map T}:
  BeckDistribution (W ×) T := (@strength T _ W).

(** ** <<T ∘ (W ×)>> is a monad *)
(******************************************************************************)
#[export] Instance Natural_strength `{Functor F} {W : Type} : Natural (F := prod W ∘ F) (@strength F _ W).
Proof.
  constructor; try typeclasses eauto.
  intros. unfold_ops @Map_compose. ext [a t].
  unfold compose; cbn.
  compose near t on left.
  compose near t on right.
  now rewrite 2(fun_map_map).
Qed.

Section strength_as_writer_distributive_law.

  Context
    `{Monoid W}.

  Lemma strength_ret_l `{Functor F} : forall A : Type,
      σ ∘ ret (W ×) (F A) =
      map F (ret (W ×) A).
  Proof.
    reflexivity.
  Qed.

  Lemma strength_join_l `{Functor F} : forall A : Type,
      σ ∘ join (T := (W ×)) (A := F A) =
      map F (join (T := (W ×)) (A := A)) ∘ σ ∘ map (W ×) σ.
  Proof.
    intros. ext [w1 [w2 t]]. unfold compose; cbn.
    compose near t. rewrite fun_map_map.
    compose near t on right. rewrite fun_map_map.
    reflexivity.
  Qed.

  Context
    `{Monad T}.

  #[export, program] Instance BeckDistributiveLaw_strength :
    BeckDistributiveLaw (W ×) T :=
    {| bdist_join_r := strength_join T W;
       bdist_unit_r := strength_ret T W;
       bdist_join_l := strength_join_l;
       bdist_unit_l := strength_ret_l;
    |}.

  #[export] Instance: Monad (T ∘ (W ×)) := Monad_Beck.

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
      extract (W ×) (W * A) ∘ bdist (W ×) (W ×) =
      map (W ×) (extract (W ×) A).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_dist_counit_r : forall A,
      map (W ×) (extract (W ×) A) ∘ bdist (W ×) (W ×) =
      extract (W ×) (W * A).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_baton : forall A,
      extract (W ×) A ∘ ret (W ×) A = @id A.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma bimonad_cup : forall A,
      cojoin (W ×) ∘ ret (W ×) A = ret (W ×) (W * A) ∘ ret (W ×) A.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma bimonad_cap : forall A,
      extract (W ×) A ∘ join (T := (W ×)) = extract (W ×) A ∘ extract (W ×) (W * A).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_butterfly : forall (A : Type),
      cojoin (W ×) ∘ join (T := (W ×)) (A := A) =
      map (W ×) (join (T := (W ×))) ∘ join ∘ map (W ×) (bdist (W ×) (W ×))
           ∘ cojoin (W ×) ∘ map (W ×) (cojoin (W ×)).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  #[export] Instance Bimonad_Writer : Bimonad (W ×) :=
    {| bimonad_monad := Monad_writer;
       bimonad_comonad := Comonad_env W;
       Bimonad.bimonad_dist_counit_l := @bimonad_dist_counit_l;
       Bimonad.bimonad_dist_counit_r := @bimonad_dist_counit_r;
       Bimonad.bimonad_distributive_law := BeckDistributiveLaw_strength;
       Bimonad.bimonad_cup := @bimonad_cup;
       Bimonad.bimonad_cap := @bimonad_cap;
       Bimonad.bimonad_baton := @bimonad_baton;
       Bimonad.bimonad_butterfly := @bimonad_butterfly;
    |}.

End writer_bimonad_instance.

(** ** <<incr>> *)
(******************************************************************************)
Section incr.

  Lemma extract_incr `{Monoid W} {A : Type} :
    forall (w : W), extract (W ×) A ∘ incr w = extract (W ×) A.
  Proof.
    intros. now ext [w' a].
  Qed.

End incr.

(** ** Miscellaneous properties *)
(******************************************************************************)
Section Writer_miscellaneous.

  Context
    `{Monoid W}.

  (* This rewrite is useful when proving decoration-traversal compatibility
     in the binder case. *)
  Theorem strength_shift1 : forall (F : Type -> Type) `{Functor F} (w : W) (A : Type),
      σ ∘ μ (T := (W ×)) ∘ pair w = map F (μ (T := (W ×)) ∘ pair w) ∘ strength (F := F) (B := A).
  Proof.
    intros. ext [w' x]. unfold compose; cbn.
    compose near x. now rewrite fun_map_map.
  Qed.

  (* TODO Cleanup where this gets used *)
  Lemma incr_spec `{Monoid W} : forall A, uncurry incr = join (T := (W ×)) (A := A).
  Proof.
    intros. ext [w1 [w2 a]]. reflexivity.
  Qed.

End Writer_miscellaneous.
