(** This file implements bimonads. A [Bimonad] is a functor equipped with a monad/comonad structure and  a
    distributive law over itself, which ensures the composition (W ∘ W) is
    also a monad and a comonad. Additionally there are some coherence
    laws, below, which may be read into several equivalent ways: *)
(**
    - The cojoin is a monad homomorphism (W → W ∘ W) and the counit a homomorphism (W → 1)
    - The join is a comonad homomorphism (W ∘ W → W) and the unit a homomorphism (1 → W)
    - W is a monoid in the category of comonoids (in the category of endofunctors)
    - W is a comonoid in the category of monoids (in the category of endofunctors)
 *)

From Tealeaves.Singlesorted.Classes Require Export
     Monad Comonad BeckDistributiveLaw.

Import Product.Notations.
Import Functor.Notations.
Import Monad.Notations.
Import Comonad.Notations.
#[local] Open Scope tealeaves_scope.

(** * Bimonad *)
(******************************************************************************)
Section Bimonad.

  Context
    (W : Type -> Type)
    `{Fmap W}
    `{Return W}
    `{Join W}
    `{Cojoin W}
    `{Extract W}
    `{BeckDistributiveLaw W W}.

  Class Bimonad :=
    { bimonad_monad :> Monad W;
      bimonad_comonad :> Comonad W;
      bimonad_distributive_law :> BeckDistributiveLaw W W _;
      bimonad_dist_counit_r :
        `(fmap W (extract W) ∘ dist W W = extract W (A := W A));
      bimonad_dist_counit_l :
        `(extract W ∘ dist W W = fmap W (extract W (A := A)));
      bimonad_cap :
        `(extract W ∘ join W = extract W ∘ extract W (A := W A));
      bimonad_baton :
        `(extract W ∘ ret W = @id A);
      bimonad_cup :
        `(cojoin W ∘ ret W = ret W ∘ ret W (A := A));
      bimonad_butterfly :
        `(cojoin W ∘ join W (A := A) =
          fmap W (join W) ∘ join W ∘ fmap W (dist W W) ∘ cojoin W ∘ fmap W (cojoin W));
    }.

End Bimonad.

(** * Bimonadic Kleisli operation *)
(******************************************************************************)
Section Bimonad_kleisli_operations.

  Context
    (W : Type -> Type)
    `{Fmap W} `{Join W} `{Cojoin W}
    `{BeckDistribution W W}.

  Definition bindbi {A B} : (W A -> W B) -> (W A -> W B) :=
    fun f => join W ∘ fmap W f ∘ cojoin W.

  Definition twist : W ∘ W ⇒ W ∘ W
    := fun A => fmap W (join W) ∘ dist W W ∘ fmap W (cojoin W).

  Definition kcomposebi {A B C} :
    (W B -> W C) ->
    (W A -> W B) ->
    (W A -> W C) :=
    fun g f => join W ∘ fmap W g ∘ twist B ∘ fmap W f ∘ cojoin W.

End Bimonad_kleisli_operations.

Module Notations.
  Notation "g ⋆bi f" := (kcomposebi _ g f) (at level 70) : tealeaves_scope.
End Notations.

Import Notations.

(** ** Suboperations *)
(******************************************************************************)
Section Bimonad_suboperations.

  Context
    `{Bimonad W}.

  Lemma cobind_to_bindbi {A B} : forall (f : W A -> B),
      cobind W f = bindbi W (ret W ∘ f).
  Proof.
    intros. unfold bindbi. unfold_ops @Cobind_Cojoin.
    rewrite <- (fun_fmap_fmap W). reassociate <-.
    now rewrite (mon_join_fmap_ret W).
  Qed.

  Lemma bind_to_bindbi {A B} : forall (f : A -> W B),
      bind W f = bindbi W (f ∘ extract W).
  Proof.
    intros. unfold bindbi. unfold_ops @Bind_Join.
    rewrite <- (fun_fmap_fmap W).
    reassociate <-. reassociate ->.
    now rewrite (com_fmap_extr_cojoin W).
  Qed.

  Lemma fmap_to_bindbi {A B} : forall (f : A -> B),
      fmap W f = bindbi W (ret W ∘ f ∘ extract W).
  Proof.
    intros. unfold bindbi.
    do 2 rewrite <- (fun_fmap_fmap W).
    repeat reassociate <-.
    rewrite (mon_join_fmap_ret W).
    reassociate ->.
    now rewrite (com_fmap_extr_cojoin W).
  Qed.

End Bimonad_suboperations.

(** ** Properties of Kleisli composition *)
(******************************************************************************)
Section Bimonad_kleisli_composition.

  Context
    `{Bimonad W}.

  Lemma kcomposebi_1 {A B C} : forall (g : B -> W C) (f : W A -> W B),
      (g ∘ extract W) ⋆bi f = g ⋆ f.
  Proof.
    intros. unfold kcomposebi, kcompose.
    rewrite <- (fun_fmap_fmap W).
    reassociate <-. unfold twist.
    repeat reassociate <-.
    reassociate -> near (fmap W (join W)).
    rewrite (fun_fmap_fmap W). rewrite (bimonad_cap W).
    rewrite <- (fun_fmap_fmap W).
    repeat reassociate <-.
    reassociate -> near (dist W W).
    rewrite (bimonad_dist_counit_r W).
    reassociate -> near (fmap W (cojoin W)).
    rewrite <- (natural (ϕ := @extract W _)); unfold_ops @Fmap_I.
    reassociate <-. reassociate -> near (cojoin W (A := B)).
    rewrite (com_fmap_extr_cojoin W).
    reassociate -> near (fmap W f).
    rewrite <- (natural (ϕ := @extract W _)); unfold_ops @Fmap_I.
    repeat reassociate ->. rewrite (com_extract_cojoin W).
    reflexivity.
  Qed.

  Lemma kcomposebi_2 {A B C} : forall (g : W B -> W C) (f : W A -> B),
      g ⋆bi (ret W ∘ f) = g co⋆ f.
  Proof.
    intros. unfold kcomposebi, kcompose.
    rewrite <- (fun_fmap_fmap W).
    reassociate <-. unfold twist.
    repeat reassociate <-.
    reassociate -> near (fmap W (ret W)).
    rewrite (fun_fmap_fmap W). rewrite (bimonad_cup W).
    rewrite <- (fun_fmap_fmap W).
    repeat reassociate <-.
    reassociate -> near (fmap W (ret W) (A := W B)).
    rewrite (dist_unit_r W W).
    reassociate -> near (ret W).
    rewrite (natural (ϕ := @ret W _)); unfold_ops @Fmap_I.
    reassociate <-. reassociate -> near (fmap W (ret W)).
    rewrite (mon_join_fmap_ret W).
    reassociate -> near (ret W).
    rewrite (natural (ϕ := @ret W _)); unfold_ops @Fmap_I.
    reassociate <-. rewrite (mon_join_ret W).
    reflexivity.
  Qed.

End Bimonad_kleisli_composition.

(** ** Functoriality of [bindbi] *)
(******************************************************************************)
Section Bimonad_bindbi.

  Context
    `{Bimonad W}.

  Lemma shuffle_monoids {A} :
      fmap W (join W) ∘ join W (A := W (W A)) = join W ∘ fmap (W ∘ W) (join W).
  Proof.
    now rewrite (natural (ϕ := @join W _)).
  Qed.

  Lemma shuffle_comonoids {A} :
      cojoin W ∘ fmap W (cojoin W) = fmap (W ∘ W) (cojoin W) ∘ cojoin W (A := W A).
  Proof.
    now rewrite (natural (ϕ := @cojoin W _)).
  Qed.

  Definition bind_functorial {A B C} : forall (g : W B -> W C) (f : W A -> W B),
      bindbi W (g ⋆bi f) = bindbi W g ∘ bindbi W f.
  Proof.
    intros. unfold bindbi. unfold kcomposebi.
    (** *)
    repeat reassociate -> on left.
    rewrite <- (fun_fmap_fmap W).
    repeat  reassociate <- on left.
    rewrite <- (mon_join_join W).
    (** *)
    rewrite <- (fun_fmap_fmap W).
    repeat reassociate -> on left.
    rewrite <- (com_cojoin_cojoin W).
    repeat  reassociate <- on left.
    (** *)
    repeat reassociate -> on left.
    rewrite <- (fun_fmap_fmap W).
    repeat  reassociate <- on left.
    reassociate -> near (fmap W (fmap W g)).
    change (fmap W (fmap W g)) with (fmap (W ∘ W) g).
    Set Keyed Unification.
    rewrite <- (natural (ϕ := @join W _)).
    Unset Keyed Unification.
    (** *)
    rewrite <- (fun_fmap_fmap W).
    repeat reassociate -> on left.
    reassociate <- near (fmap W (fmap W f)).
    change (fmap W (fmap W f)) with (fmap (W ∘ W) f).
    Set Keyed Unification.
    rewrite (natural (ϕ := @cojoin W _)).
    Unset Keyed Unification.
    repeat reassociate <- on left.
    repeat reassociate <- on right.
    (** *)
    reassociate -> near (join W).
    rewrite (bimonad_butterfly W).
    repeat reassociate <-.
    reassociate -> near (join W).
    Set Keyed Unification.
    rewrite shuffle_monoids.
    Unset Keyed Unification.
    reassociate -> near (fmap W (cojoin W)).
    Set Keyed Unification.
    rewrite shuffle_comonoids.
    Unset Keyed Unification.
    unfold twist.
    repeat reassociate <-.
    now repeat rewrite <- (fun_fmap_fmap W).
  Qed.

End Bimonad_bindbi.
