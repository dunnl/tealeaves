(** This file implements bimonads. A [Bimonad] is a functor equipped
    with a monad/comonad structure and a distributive law over itself,
    which ensures the composition (W ∘ W) is also a monad and a
    comonad. Additionally there are some coherence laws, below, which
    may be read into several equivalent ways: *)
(**
    - The cojoin is a monad homomorphism (W → W ∘ W) and the counit a homomorphism (W → 1)
    - The join is a comonad homomorphism (W ∘ W → W) and the unit a homomorphism (1 → W)
    - W is a monoid in the category of comonoids (in the category of endofunctors)
    - W is a comonoid in the category of monoids (in the category of endofunctors)
 *)

From Tealeaves Require Export
  Categorical.Classes.Monad
  Categorical.Classes.Comonad
  Categorical.Classes.BeckDistributiveLaw.

Import Product.Notations.
Import Functor.Notations.
Import Monad.Notations.
Import Comonad.Notations.

#[local] Generalizable Variables W A B.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.
#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

(** * Bimonad typeclass *)
(******************************************************************************)
Section Bimonad.

  Context
    (W : Type -> Type)
    `{Map W}
    `{Return W}
    `{Join W}
    `{Cojoin W}
    `{Extract W}
    `{BeckDistributiveLaw W W}.

  Class Bimonad :=
    { bimonad_monad :> Monad W;
      bimonad_comonad :> Comonad W;
      bimonad_distributive_law :> BeckDistributiveLaw W W;
      bimonad_dist_counit_r :
        `(map W (extract W A) ∘ bdist W W = extract W (W A));
      bimonad_dist_counit_l :
        `(extract W (W A) ∘ bdist W W = map W (extract W A));
      bimonad_cap :
        `(extract W A ∘ join W = extract W A ∘ extract W (W A));
      bimonad_baton :
        `(extract W A ∘ ret W = @id A);
      bimonad_cup :
        `(cojoin W ∘ ret W = ret W ∘ ret W (A := A));
      bimonad_butterfly :
        `(cojoin W ∘ join W (A := A) =
          map W (join W) ∘ join W ∘ map W (bdist W W) ∘ cojoin W ∘ map W (cojoin W));
    }.

End Bimonad.

(** * Kleisli lifting operation <<bibind>> *)
(******************************************************************************)
Section Bimonad_kleisli_operations.

  Context
    (W : Type -> Type)
    `{Map W} `{Join W} `{Cojoin W}
    `{BeckDistribution W W}.

  Definition bibind {A B} : (W A -> W B) -> (W A -> W B) :=
    fun f => join W ∘ map W f ∘ cojoin W.

  Definition twist : W ∘ W ⇒ W ∘ W
    := fun A => map W (join W) ∘ bdist W W ∘ map W (cojoin W).

  Definition kcomposebi {A B C} :
    (W B -> W C) ->
    (W A -> W B) ->
    (W A -> W C) :=
    fun g f => join W ∘ map W g ∘ twist B ∘ map W f ∘ cojoin W.

End Bimonad_kleisli_operations.

Module Notations.
  Notation "g ⋆bi f" := (kcomposebi _ g f) (at level 70) : tealeaves_scope.
End Notations.

Import Notations.

(*
(** ** Specifications for suboperations *)
(******************************************************************************)
Section Bimonad_suboperations.

  Context
    `{Bimonad W}.

  Lemma cobind_to_bibind : forall `(f : W A -> B),
      cobind W f = bibind W (ret W ∘ f).
  Proof.
    intros. unfold bibind. unfold_ops @Cobind_Cojoin.
    rewrite <- (fun_map_map W). reassociate <-.
    now rewrite (mon_join_map_ret W).
  Qed.

  Lemma bind_to_bibind : forall `(f : A -> W B),
      bind W f = bibind W (f ∘ extract W).
  Proof.
    intros. unfold bibind. unfold_ops @Bind_Join.
    rewrite <- (fun_map_map W).
    reassociate <-. reassociate ->.
    now rewrite (com_map_extr_cojoin W).
  Qed.

  Lemma map_to_bibind : forall `(f : A -> B),
      map W f = bibind W (ret W ∘ f ∘ extract W).
  Proof.
    intros. unfold bibind.
    do 2 rewrite <- (fun_map_map W).
    repeat reassociate <-.
    rewrite (mon_join_map_ret W).
    reassociate ->.
    now rewrite (com_map_extr_cojoin W).
  Qed.

End Bimonad_suboperations.

(** ** Bimonadic Kleisli composition laws *)
(******************************************************************************)
Section Bimonad_kleisli_composition.

  Context
    `{Bimonad W}.

  (** Composition where <<g>> is a co-Kleisli arrow reduces to usual
      Kleisli composition. *)
  Lemma bi_kcompose1 {A B C} : forall (g : B -> W C) (f : W A -> W B),
      (g ∘ extract W) ⋆bi f = g ⋆ f.
  Proof.
    intros. unfold kcomposebi, kcompose.
    rewrite <- (fun_map_map W).
    reassociate <-. unfold twist.
    repeat reassociate <-.
    reassociate -> near (map W (join W)).
    rewrite (fun_map_map W). rewrite (bimonad_cap W).
    rewrite <- (fun_map_map W).
    repeat reassociate <-.
    reassociate -> near (bdist W W).
    rewrite (bimonad_dist_counit_r W).
    reassociate -> near (map W (cojoin W)).
    rewrite <- (natural (ϕ := @extract W _)); unfold_ops @Map_I.
    reassociate <-. reassociate -> near (cojoin W (A := B)).
    rewrite (com_map_extr_cojoin W).
    reassociate -> near (map W f).
    rewrite <- (natural (ϕ := @extract W _)); unfold_ops @Map_I.
    repeat reassociate ->. rewrite (com_extract_cojoin W).
    reflexivity.
  Qed.

  (** Composition where <<f>> is a Kleisli arrow reduces to usual
      co-Kleisli composition. *)
  Lemma bi_kcompose2 {A B C} : forall (g : W B -> W C) (f : W A -> B),
      g ⋆bi (ret W ∘ f) = g co⋆ f.
  Proof.
    intros. unfold kcomposebi, kcompose.
    rewrite <- (fun_map_map W).
    reassociate <-. unfold twist.
    repeat reassociate <-.
    reassociate -> near (map W (ret W)).
    rewrite (fun_map_map W). rewrite (bimonad_cup W).
    rewrite <- (fun_map_map W).
    repeat reassociate <-.
    reassociate -> near (map W (ret W) (A := W B)).
    rewrite (dist_unit_r W W).
    reassociate -> near (ret W).
    rewrite (natural (ϕ := @ret W _)); unfold_ops @Map_I.
    reassociate <-. reassociate -> near (map W (ret W)).
    rewrite (mon_join_map_ret W).
    reassociate -> near (ret W).
    rewrite (natural (ϕ := @ret W _)); unfold_ops @Map_I.
    reassociate <-. rewrite (mon_join_ret W).
    reflexivity.
  Qed.

End Bimonad_kleisli_composition.

(** ** Functoriality of [bibind] *)
(******************************************************************************)
Section Bimonad_bibind.

  Context
    `{Bimonad W}.

  Definition bind_id {A} :
    bibind W (ret W ∘ extract W) = @id (W A).
  Proof.
    intros. unfold bibind.
    rewrite <- (fun_map_map W).
    do 2 reassociate -> on left.
    rewrite (com_map_extr_cojoin W).
    reassociate <- on left.
    now rewrite (mon_join_map_ret W).
  Qed.

  Definition bind_functorial {A B C} : forall (g : W B -> W C) (f : W A -> W B),
      bibind W (g ⋆bi f) = bibind W g ∘ bibind W f.
  Proof.
    intros. unfold bibind. unfold kcomposebi.
    (** *)
    repeat reassociate -> on left.
    rewrite <- (fun_map_map W).
    repeat  reassociate <- on left.
    rewrite <- (mon_join_join W).
    (** *)
    rewrite <- (fun_map_map W).
    repeat reassociate -> on left.
    rewrite <- (com_cojoin_cojoin W).
    repeat  reassociate <- on left.
    (** *)
    repeat reassociate -> on left.
    rewrite <- (fun_map_map W).
    repeat  reassociate <- on left.
    reassociate -> near (map W (map W g)).
    change (map W (map W g)) with (map (W ∘ W) g).
    Set Keyed Unification.
    rewrite <- (natural (ϕ := @join W _)).
    Unset Keyed Unification.
    (** *)
    rewrite <- (fun_map_map W).
    repeat reassociate -> on left.
    reassociate <- near (map W (map W f)).
    change (map W (map W f)) with (map (W ∘ W) f).
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
    rewrite (natural (ϕ := @join W _) (μ W)).
    Unset Keyed Unification.
    reassociate -> near (map W (cojoin W)).
    Set Keyed Unification.
    rewrite <- (natural (ϕ := @cojoin W _) (cojoin W)).
    Unset Keyed Unification.
    unfold twist.
    repeat reassociate <-.
    now repeat rewrite <- (fun_map_map W).
  Qed.

End Bimonad_bibind.
*)
