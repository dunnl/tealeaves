From Tealeaves Require Export
  Classes.Monoid
  Functors.Early.Reader.

From Tealeaves Require Import
  Classes.Kleisli.Monad
  Classes.Kleisli.Comonad
  Classes.Categorical.Monad
  Classes.Categorical.Comonad
  Classes.Categorical.Bimonad.

Import Product.Notations.
Import Functor.Notations.
Import Monoid.Notations.
Import Categorical.Monad.Notations.
Import Categorical.Comonad.Notations.
Import Kleisli.Monad.Notations.
Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables W T F A M.

(** * Writer monad *)
(**********************************************************************)

(** ** Categorical instance *)
(** In the even that [A] is a monoid, the product functor forms a
    monad. The return operation maps <<b>> to <<(1, b)>> where <<1>>
    is the monoid unit.  The join operation monoidally combines the
    two monoid values. *)
(**********************************************************************)
Section writer_monad.

  Context
    `{Monoid M}.

  #[export] Instance Join_writer: Join (prod M) :=
    fun (A: Type) (p: M * (M * A)) =>
      map_fst (uncurry (@monoid_op M _)) (α^-1 p).

  #[export] Instance Return_writer: Return (prod M) :=
    fun A (a: A) => (Ƶ, a).

  #[export] Instance Natural_ret_writer:
    Natural (@ret (prod M) Return_writer).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. now ext a.
  Qed.

  #[export] Instance Natural_join_writer:
    Natural (@join (prod M) Join_writer).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [x [x' a]].
  Qed.

  #[export, program] Instance Monad_Categorical_writer:
    Monad (prod M).

  Solve Obligations with
    (intros; unfold transparent tcs; ext p;
     unfold compose in *; destruct_all_pairs;
     cbn; now simpl_monoid).

End writer_monad.

(** ** Tensor Strength Makes any <<T ∘ (W ×)>> a Monad *)
(**********************************************************************)
#[export] Instance BeckDistribution_strength
  (W: Type) (T: Type -> Type)
  `{Map_T: Map T}:
  BeckDistribution (W ×) T := (@strength T _ W).

Section strength_as_writer_distributive_law.

  Import Strength.Notations.

  Context
    `{Monoid W}.

  Lemma strength_ret_l `{Functor F}: forall A: Type,
      σ ∘ ret (T := (W ×)) (A := F A) =
        map (F := F) (ret (T := (W ×)) (A := A)).
  Proof.
    reflexivity.
  Qed.

  Lemma strength_join_l `{Functor F}: forall A: Type,
      σ ∘ join (T := (W ×)) (A := F A) =
        map (F := F) (join (T := (W ×)) (A := A)) ∘
          σ ∘ map (F := (W ×)) σ.
  Proof.
    intros. ext [w1 [w2 t]]. unfold compose; cbn.
    compose near t. rewrite fun_map_map.
    compose near t on right. rewrite fun_map_map.
    reflexivity.
  Qed.

  Context
    `{Categorical.Monad.Monad T}.

  #[export, program] Instance BeckDistributiveLaw_strength:
    BeckDistributiveLaw (W ×) T :=
    {| bdist_join_r := strength_join T W;
       bdist_unit_r := strength_ret T W;
       bdist_join_l := strength_join_l;
       bdist_unit_l := strength_ret_l;
    |}.

  #[export] Instance Monad_Compose_Writer:
    Monad (T ∘ (W ×)) := Monad_Beck.

End strength_as_writer_distributive_law.

(** ** Writer Bimonad Instances *)
(**********************************************************************)

Section writer_bimonad_instance.

  Context
    `{Monoid W}.

  Lemma writer_dist_involution: forall (A: Type),
      bdist (prod W) (prod W) ∘ bdist (prod W) (prod W) =
        @id (W * (W * A)).
  Proof.
    intros. now ext [? [? ?]].
  Qed.

  Lemma bimonad_dist_counit_l: forall A,
      extract (W := (W ×)) (A := W * A) ∘ bdist (W ×) (W ×) =
        map (F := (W ×)) (extract (W := (W ×)) (A := A)).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_dist_counit_r: forall A,
      map (F := (W ×))
        (extract (W := (W ×)) (A := A)) ∘ bdist (W ×) (W ×) =
        extract (W := (W ×)) (A := W * A).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_baton: forall A,
      extract (W := (W ×)) (A := A) ∘ ret (T := (W ×)) = @id A.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma bimonad_cup: forall A,
      cojoin (W := (W ×)) ∘ ret (T := (W ×)) =
        ret (T := (W ×)) (A := W * A) ∘ ret (T := (W ×)).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma bimonad_cap: forall A,
      extract (W := (W ×)) (A := A) ∘ join (T := (W ×)) =
        extract (W := (W ×)) (A := A) ∘
          extract (W := (W ×)) (A := W * A).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  Lemma bimonad_butterfly: forall (A: Type),
      cojoin (W := (W ×)) ∘ join (T := (W ×)) (A := A) =
        map (F := (W ×)) (join (T := (W ×))) ∘ join ∘
          map (F := (W ×)) (bdist (W ×) (W ×))
          ∘ cojoin (W := (W ×)) ∘
          map (F := (W ×)) (cojoin (W := (W ×))).
  Proof.
    intros. now ext [w1 [w2 a]].
  Qed.

  #[export] Instance Bimonad_Writer: Bimonad (W ×) :=
    {| bimonad_monad := Monad_Categorical_writer;
       bimonad_comonad := Comonad_reader W;
       Bimonad.bimonad_dist_counit_l := @bimonad_dist_counit_l;
       Bimonad.bimonad_dist_counit_r := @bimonad_dist_counit_r;
       Bimonad.bimonad_distributive_law := BeckDistributiveLaw_strength;
       Bimonad.bimonad_cup := @bimonad_cup;
       Bimonad.bimonad_cap := @bimonad_cap;
       Bimonad.bimonad_baton := @bimonad_baton;
       Bimonad.bimonad_butterfly := @bimonad_butterfly;
    |}.

End writer_bimonad_instance.

(** ** Kleisli Monad Instance *)
(**********************************************************************)
Section writer_monad.

  Context
    `{Monoid W}.

  #[export] Instance Return_Writer: Return (W ×) :=
    fun A (a: A) => (Ƶ, a).

  #[export] Instance Bind_Writer: Bind (W ×) (W ×) :=
    fun A B (f: A -> W * B) (p: W * A) =>
      map_fst (uncurry (@monoid_op W _)) (α^-1 (map_snd f p)).

  #[export] Instance Natural_ret_Writer:
    Natural (@ret (W ×) Return_Writer).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. now ext a.
  Qed.

  Lemma Writer_kmon_bind0:
    forall (A B: Type) (f: A -> W * B),
      bind f ∘ ret = f.
  Proof.
    intros. ext a.
    unfold compose.
    unfold transparent tcs.
    cbn. destruct (f a).
    cbn. now simpl_monoid.
  Qed.

  Lemma Writer_kmon_bind1:
    forall (A: Type), bind (ret (A := A)) = id.
  Proof.
    intros. ext [m a]. unfold transparent tcs.
    cbn. now simpl_monoid.
  Qed.

  Lemma Writer_kmon_bind2:
    forall (A B C: Type) (g: B -> W * C) (f: A -> W * B),
      bind g ∘ bind f = bind (g ⋆ f).
  Proof.
    intros. ext [m a]. unfold_ops @Bind_Writer.
    unfold kc, bind, compose. cbn.
    unfold id. destruct (f a). cbn. unfold id. destruct (g b).
    cbn. unfold id.
    now simpl_monoid.
  Qed.

  #[export] Instance RightPreModule_writer:
    Kleisli.Monad.RightPreModule (W ×) (W ×) :=
    {| kmod_bind1 := Writer_kmon_bind1;
       kmod_bind2 := Writer_kmon_bind2;
    |}.

  #[export] Instance Monad_writer: Kleisli.Monad.Monad (W ×) :=
    {| kmon_bind0 := Writer_kmon_bind0;
    |}.

  (** ** Miscellaneous Properties *)
  (********************************************************************)
  Lemma extract_pair {A: Type}:
    forall (w: W), extract ∘ pair w = @id A.
  Proof.
    reflexivity.
  Qed.

  Lemma extract_incr {A: Type}:
    forall (w: W), extract ∘ incr w (A := A) = extract.
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma extract_preincr {A: Type}:
    forall (w: W), extract ⦿ w = extract (A := A).
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma extract_preincr2 {A B: Type} (f: A -> B):
    forall (w: W), (f ∘ extract) ⦿ w = f ∘ extract.
  Proof.
    intros. now ext [w' a].
  Qed.

  Lemma preincr_ret {A B: Type}:
    forall (f: W * A -> B) (w: W),
      (f ⦿ w) ∘ ret = f ∘ pair w.
  Proof.
    intros. ext a. cbv.
    change (op w unit0) with (w ● Ƶ).
    now simpl_monoid.
  Qed.

  Lemma incr_spec `{Monoid W}:
    forall A, uncurry incr = join (T := (W ×)) (A := A).
  Proof.
    intros. ext [w1 [w2 a]]. reflexivity.
  Qed.

End writer_monad.
