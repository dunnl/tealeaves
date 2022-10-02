(** This file contains a formalization of distributive laws in the
    sense of Beck, i.e.  a distribution of one monad over another with
    compatibility properties such that the composition of the two also
    forms a monad. *)
(** # <a href="https://ncatlab.org/nlab/show/distributive+law">https://ncatlab.org/nlab/show/distributive+law</a># *)

From Tealeaves Require Export
  Classes.Algebraic.Monad
  Functors.Compose.

#[local] Generalizable Variables T U A B.

(** * Beck distribution laws *)
(******************************************************************************)
Class BeckDistribution (U T : Type -> Type)
  := bdist : forall {A : Type}, U (T A) -> T (U A).

Arguments bdist U T%function_scope {BeckDistribution} {A}%type_scope _.

#[local] Notation "'δ'" := (bdist) : tealeaves_scope.

Section BeckDistributiveLaw.

  Context
    (U T : Type -> Type)
    `{Monad U}
    `{Monad T}
    `{BeckDistribution U T}.

  Class BeckDistributiveLaw :=
    { bdist_monad_l : Monad T;
      bdist_monad_r : Monad U;
      bdist_natural :> Natural (@bdist U T _);
      bdist_join_l :
        `(bdist U T ∘ join U = fmap T (join U) ∘ bdist U T ∘ fmap U (bdist U T (A := A)));
      bdist_join_r :
        `(bdist U T ∘ fmap U (join T) = join T ∘ fmap T (bdist U T) ∘ bdist U T (A := T A));
      bdist_unit_l :
        `(bdist U T ∘ ret U (A := T A) = fmap T (ret U));
      bdist_unit_r :
        `(bdist U T ∘ fmap U (ret T) = ret T (A := U A));
    }.

End BeckDistributiveLaw.

(** * Beck distributive laws induce a composite monad *)
(******************************************************************************)
Section BeckDistributivelaw_composite_monad.

  Context
    `{BeckDistributiveLaw U T}.

  Existing Instance bdist_monad_l.
  Existing Instance bdist_monad_r.

  #[export] Instance Ret_Beck : Return (T ∘ U) :=
    fun A => ret T ∘ ret U.

  (* we join <<T>> before <<U>> *)
  #[export] Instance Join_Beck : Join (T ∘ U) :=
    fun A => fmap T (join U) ∘ join T ∘ fmap T (bdist U T).

  Lemma slide_joins :
    `(fmap T (join U) ∘ join T (A := U (U A))
      = join T ∘ fmap (T ∘ T) (join U)).
  Proof.
    intros; now rewrite (natural (ϕ := @join T _)).
  Qed.

  Lemma Natural_ret_Beck : Natural (@ret (T ∘ U) _).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold_ops @Fmap_compose @Ret_Beck.
    reassociate <- on left.
    unfold_compose_in_compose.
    rewrite (natural (G := T) (F := fun A => A)).
    unfold_ops @Fmap_I. reassociate -> on left.
    now rewrite (natural (G := U) (F := fun A => A)).
  Qed.

  #[local] Set Keyed Unification.
  Lemma Natural_join_Beck : Natural (@join (T ∘ U) _).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold_ops @Fmap_compose @Join_Beck.
    change_left (fmap T (fmap U f) ∘ fmap T (join U) ∘ join T ∘ fmap T (bdist U T)).
    rewrite (fun_fmap_fmap T).
    rewrite (natural (G := T) (F := T ∘ T)).
    rewrite (natural (G := U) (F := U ∘ U)).
    rewrite <- (fun_fmap_fmap (T ∘ T)).
    unfold_ops @Fmap_compose.
    change_left ((join T ∘ fmap T (fmap T (join U))) ∘
    (fmap T (fmap T (fmap U (fmap U f))) ∘ fmap T (bdist U T))).
    rewrite (natural (G := T)).
    rewrite (fun_fmap_fmap T).
    rewrite (natural (G := T ∘ U) (Natural := bdist_natural U T)).
    now rewrite <- (fun_fmap_fmap T).
  Qed.
  #[local] Unset Keyed Unification.

  Lemma join_ret_Beck {A} :
      join (T ∘ U) ∘ ret (T ∘ U) = @id ((T ∘ U) A).
  Proof.
    intros. unfold_ops @Join_Beck @Ret_Beck.
    reassociate ->. reassociate <- near (fmap T (bdist U T)).
    rewrite (natural (F := fun A => A)). unfold_ops @Fmap_I.
    repeat reassociate ->. reassociate <- near (join T).
    rewrite (mon_join_ret T).
    unfold_compose_in_compose. rewrite (bdist_unit_l U T).
    change (id ∘ ?f) with f. rewrite (fun_fmap_fmap T).
    rewrite (mon_join_ret U).
    now rewrite (fun_fmap_id T).
  Qed.

  Lemma join_fmap_ret_Beck {A} :
    join (T ∘ U) ∘ fmap (T ∘ U) (ret (T ∘ U)) = @id (T (U A)).
  Proof.
    intros. unfold_ops @Join_Beck @Ret_Beck.
    rewrite (natural (G := T) (Natural := mon_join_natural T)).
    unfold_ops @Fmap_compose.
    do 2 reassociate ->.
    #[local] Set Keyed Unification.
    rewrite 2(fun_fmap_fmap T).
    #[local] Unset Keyed Unification.
    rewrite <- (fun_fmap_fmap U).
    reassociate <- near (bdist U T).
    rewrite (bdist_unit_r U T).
    reassociate <-. rewrite (natural (G := T) (F := fun A => A)).
    unfold_ops @Fmap_I.
    reassociate ->. rewrite (mon_join_fmap_ret U).
    rewrite <-(fun_fmap_fmap T). reassociate <-.
    rewrite (mon_join_fmap_ret T).
    now rewrite (fun_fmap_id T).
  Qed.

  Lemma join_join_Beck {A} :
    join (T ∘ U) ∘ join (T ∘ U) =
    join (T ∘ U) ∘ fmap (T ∘ U) (join (T ∘ U) (A:=A)).
  Proof.
    intros. unfold_ops @Join_Beck @Ret_Beck.
    (* Pull one <<join U>> to the same side as the other *)
    repeat change (?x ∘ (?y ∘ ?z)) with (x ∘ y ∘ z).
    change (?x ∘ fmap T (bdist U T) ∘ fmap T (join U) ∘ ?y)
      with (x ∘ (fmap T (bdist U T) ∘ fmap T (join U)) ∘ y).
    rewrite (fun_fmap_fmap T).
    rewrite (bdist_join_l U T).
    rewrite <- (fun_fmap_fmap T).
    rewrite <- (fun_fmap_fmap T).
    repeat reassociate <- on left.
    (* Re-associate <<join U>> *)
    change (?x ∘ join T ∘ fmap T (fmap T (join U)) ∘ ?y)
      with (x ∘ (join T ∘ fmap (T ∘ T) (join U)) ∘ y).
    rewrite <- (natural (ϕ := @join T _ )).
    repeat reassociate <- on left.
    rewrite (fun_fmap_fmap T).
    rewrite (mon_join_join U).
    rewrite <- (fun_fmap_fmap T).
    change (?x ∘ fmap T (fmap U (join U)) ∘ join T ∘ ?y)
      with (x ∘ (fmap T (fmap U (join U)) ∘ join T) ∘ y).
    rewrite (natural (ϕ := @join T _ )).
    repeat reassociate <- on left.
    (* Pull one <<join T>> to next to the other (past distributions) *)
    change (?x ∘ fmap (T ∘ T) (fmap U (join U)) ∘ fmap T (bdist U T) ∘ ?y)
      with (x ∘ (fmap T (fmap (T ∘ U) (join U)) ∘ fmap T (bdist U T)) ∘ y).
    rewrite (fun_fmap_fmap T).
    reassociate -> near (fmap T (fmap U (bdist U T))).
    rewrite (fun_fmap_fmap T).
    change (?x ∘ fmap T (?etc) ∘ join T ∘ ?y)
      with (x ∘ (fmap T (etc) ∘ join T) ∘ y).
    rewrite (natural (ϕ := @join T _ )) at 1.
    reassociate <- on left.
    (* Re-associate <<join T>> *)
    reassociate -> near (join T).
    rewrite (mon_join_join T).
    reassociate <-.
    (* Unite everything under the top-level <<fmap T>> *)
    change (?x ∘ fmap T (join T) ∘ fmap (T ∘ T) (?etc) ∘ ?y)
      with (x ∘ (fmap T (join T) ∘ fmap T (fmap T etc)) ∘ y).
    rewrite (fun_fmap_fmap T).
    change (?x ∘ ?y  ∘ ?z = ?etc) with (x ∘ (y ∘ z) = etc).
    rewrite (fun_fmap_fmap T).
    (* Unite everything under the top-level <<fmap T>> on the RHS too *)
    change (fmap (T ∘ U) ?etc) with (fmap T (fmap U etc)) at 2.
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (fun_fmap_fmap T).
    (* Simplify remaining goal by cancelling out equals *)
    fequal. fequal.
    (* Move join over distributions *)
    repeat rewrite <- (fun_fmap_fmap T).
    repeat reassociate <-.
    change (fmap T (fmap (T ∘ U) (@join U _ ?A)))
      with (fmap (T ∘ T) (fmap U (@join U _ A))).
    #[local] Set Keyed Unification.
    rewrite <- (natural (ϕ := @join T _ ) (fmap U (join U))).
    reassociate -> near (fmap T (bdist U T)).
    reassociate -> on left.
    change (fmap T (fmap U (@bdist U T _ ?A)))
      with (fmap (T ∘ U) (@bdist U T _ A)).
    rewrite (natural (ϕ := @bdist U T _ ) (bdist U T) (G := T ∘ U)).
    #[local] Unset Keyed Unification.
    unfold_ops @Fmap_compose.
    do 3 reassociate <-.
    change (?x ∘ join T ∘ fmap T (bdist U T) ∘ bdist U T ∘ ?y)
      with (x ∘ (join T ∘ fmap T (bdist U T) ∘ bdist U T) ∘ y).
    rewrite <- (bdist_join_r U T).
    (* Make some final naturality pulls *)
    repeat reassociate <-.
    change (fmap T (fmap U ?f)) with (fmap (T ∘ U) f).
    rewrite (natural (ϕ := @bdist U T _ )).
    unfold_ops @Fmap_compose.
    reassociate -> on left.
    rewrite (fun_fmap_fmap U).
    reassociate -> on left.
    now rewrite (fun_fmap_fmap U).
  Qed.

  #[export, program] Instance Monad_Beck : Monad (T ∘ U)  :=
    {| mon_ret_natural := Natural_ret_Beck;
       mon_join_natural := Natural_join_Beck;
       mon_join_ret := fun A => join_ret_Beck;
       mon_join_fmap_ret := fun A => join_fmap_ret_Beck;
       mon_join_join := fun A => join_join_Beck; |}.

End BeckDistributivelaw_composite_monad.
