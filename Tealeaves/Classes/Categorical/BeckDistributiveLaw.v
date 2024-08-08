(** This file contains a formalization of distributive laws in the
    sense of Beck, i.e.  a distribution of one monad over another with
    compatibility properties such that the composition of the two also
    forms a monad. *)
(** # <a href="https://ncatlab.org/nlab/show/distributive+law">https://ncatlab.org/nlab/show/distributive+law</a># *)

From Tealeaves Require Export
  Classes.Categorical.Monad
  Functors.Compose.

#[local] Generalizable Variables T U A B.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.
#[local] Arguments ret T%function_scope {Return} {A}%type_scope _.

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
        `(bdist U T ∘ join U = map T (join U) ∘ bdist U T ∘ map U (bdist U T (A := A)));
      bdist_join_r :
        `(bdist U T ∘ map U (join T) = join T ∘ map T (bdist U T) ∘ bdist U T (A := T A));
      bdist_unit_l :
        `(bdist U T ∘ ret U (A := T A) = map T (ret U));
      bdist_unit_r :
        `(bdist U T ∘ map U (ret T) = ret T (A := U A));
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
    fun A => map T (join U) ∘ join T ∘ map T (bdist U T).

  Lemma slide_joins :
    `(map T (join U) ∘ join T (A := U (U A))
      = join T ∘ map (T ∘ T) (join U)).
  Proof.
    intros; now rewrite (natural (ϕ := @join T _)).
  Qed.

  Lemma Natural_ret_Beck : Natural (@ret (T ∘ U) _).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold_ops @Map_compose @Ret_Beck.
    reassociate <- on left.
    unfold_compose_in_compose.
    rewrite (natural (G := T) (F := fun A => A)).
    unfold_ops @Map_I. reassociate -> on left.
    now rewrite (natural (G := U) (F := fun A => A)).
  Qed.

  #[local] Set Keyed Unification.
  Lemma Natural_join_Beck : Natural (@join (T ∘ U) _).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold_ops @Map_compose @Join_Beck.
    change_left (map T (map U f) ∘ map T (join U) ∘ join T ∘ map T (bdist U T)).
    rewrite (fun_map_map (F := T)).
    rewrite (natural (G := T) (F := T ∘ T)).
    rewrite (natural (G := U) (F := U ∘ U)).
    rewrite <- (fun_map_map (F := (T ∘ T))).
    unfold_ops @Map_compose.
    change_left ((join T ∘ map T (map T (join U))) ∘
    (map T (map T (map U (map U f))) ∘ map T (bdist U T))).
    rewrite (natural (G := T)).
    rewrite (fun_map_map (F := T)).
    rewrite (natural (G := T ∘ U) (Natural := bdist_natural U T)).
    now rewrite <- (fun_map_map (F := T)).
  Qed.
  #[local] Unset Keyed Unification.

  Lemma join_ret_Beck {A} :
      join (T ∘ U) ∘ ret (T ∘ U) = @id ((T ∘ U) A).
  Proof.
    intros. unfold_ops @Join_Beck @Ret_Beck.
    reassociate ->. reassociate <- near (map T (bdist U T)).
    rewrite (natural (F := fun A => A)). unfold_ops @Map_I.
    repeat reassociate ->. reassociate <- near (join T).
    rewrite (mon_join_ret).
    unfold_compose_in_compose. rewrite (bdist_unit_l U T).
    change (id ∘ ?f) with f. rewrite (fun_map_map (F := T)).
    rewrite (mon_join_ret (T := U)).
    now rewrite (fun_map_id (F := T)).
  Qed.

  Lemma join_map_ret_Beck {A} :
    join (T ∘ U) ∘ map (T ∘ U) (ret (T ∘ U)) = @id (T (U A)).
  Proof.
    intros. unfold_ops @Join_Beck @Ret_Beck.
    rewrite (natural (G := T) (Natural := mon_join_natural (T := T))).
    unfold_ops @Map_compose.
    do 2 reassociate ->.
    #[local] Set Keyed Unification.
    rewrite 2(fun_map_map (F := T)).
    #[local] Unset Keyed Unification.
    rewrite <- (fun_map_map (F := U)).
    reassociate <- near (bdist U T).
    rewrite (bdist_unit_r U T).
    reassociate <-. rewrite (natural (G := T) (F := fun A => A)).
    unfold_ops @Map_I.
    reassociate ->. rewrite (mon_join_map_ret (T := U)).
    rewrite <-(fun_map_map (F := T)). reassociate <-.
    rewrite (mon_join_map_ret (T := T)).
    now rewrite (fun_map_id (F := T)).
  Qed.

  Lemma join_join_Beck {A} :
    join (T ∘ U) ∘ join (T ∘ U) =
    join (T ∘ U) ∘ map (T ∘ U) (join (T ∘ U) (A:=A)).
  Proof.
    intros. unfold_ops @Join_Beck @Ret_Beck.
    (* Pull one <<join U>> to the same side as the other *)
    repeat change (?x ∘ (?y ∘ ?z)) with (x ∘ y ∘ z).
    change (?x ∘ map T (bdist U T) ∘ map T (join U) ∘ ?y)
      with (x ∘ (map T (bdist U T) ∘ map T (join U)) ∘ y).
    rewrite (fun_map_map (F := T)).
    rewrite (bdist_join_l U T).
    rewrite <- (fun_map_map (F := T)).
    rewrite <- (fun_map_map (F := T)).
    repeat reassociate <- on left.
    (* Re-associate <<join U>> *)
    change (?x ∘ join T ∘ map T (map T (join U)) ∘ ?y)
      with (x ∘ (join T ∘ map (T ∘ T) (join U)) ∘ y).
    rewrite <- (natural (ϕ := @join T _ )).
    repeat reassociate <- on left.
    rewrite (fun_map_map (F := T)).
    rewrite (mon_join_join (T := U)).
    rewrite <- (fun_map_map (F := T)).
    change (?x ∘ map T (map U (join U)) ∘ join T ∘ ?y)
      with (x ∘ (map T (map U (join U)) ∘ join T) ∘ y).
    rewrite (natural (ϕ := @join T _ )).
    repeat reassociate <- on left.
    (* Pull one <<join T>> to next to the other (past distributions) *)
    change (?x ∘ map (T ∘ T) (map U (join U)) ∘ map T (bdist U T) ∘ ?y)
      with (x ∘ (map T (map (T ∘ U) (join U)) ∘ map T (bdist U T)) ∘ y).
    rewrite (fun_map_map (F := T)).
    reassociate -> near (map T (map U (bdist U T))).
    rewrite (fun_map_map (F := T)).
    change (?x ∘ map T (?etc) ∘ join T ∘ ?y)
      with (x ∘ (map T (etc) ∘ join T) ∘ y).
    rewrite (natural (ϕ := @join T _ )) at 1.
    reassociate <- on left.
    (* Re-associate <<join T>> *)
    reassociate -> near (join T).
    rewrite (mon_join_join (T := T)).
    reassociate <-.
    (* Unite everything under the top-level <<map T>> *)
    change (?x ∘ map T (join T) ∘ map (T ∘ T) (?etc) ∘ ?y)
      with (x ∘ (map T (join T) ∘ map T (map T etc)) ∘ y).
    rewrite (fun_map_map (F := T)).
    change (?x ∘ ?y ∘ ?z = ?etc) with (x ∘ (y ∘ z) = etc).
    rewrite (fun_map_map (F := T)).
    (* Unite everything under the top-level <<map T>> on the RHS too *)
    change (map (T ∘ U) ?etc) with (map T (map U etc)) at 2.
    reassociate -> on right.
    unfold_compose_in_compose.
    rewrite (fun_map_map (F := T)).
    (* Simplify remaining goal by cancelling out equals *)
    fequal. fequal.
    (* Move join over distributions *)
    repeat rewrite <- (fun_map_map (F := T)).
    repeat reassociate <-.
    change (map T (map (T ∘ U) (@join U _ ?A)))
      with (map (T ∘ T) (map U (@join U _ A))).
    #[local] Set Keyed Unification.
    rewrite <- (natural (ϕ := @join T _ ) (map U (join U))).
    reassociate -> near (map T (bdist U T)).
    reassociate -> on left.
    change (map T (map U (@bdist U T _ ?A)))
      with (map (T ∘ U) (@bdist U T _ A)).
    rewrite (natural (ϕ := @bdist U T _ ) (bdist U T) (G := T ∘ U)).
    #[local] Unset Keyed Unification.
    unfold_ops @Map_compose.
    do 3 reassociate <-.
    change (?x ∘ join T ∘ map T (bdist U T) ∘ bdist U T ∘ ?y)
      with (x ∘ (join T ∘ map T (bdist U T) ∘ bdist U T) ∘ y).
    rewrite <- (bdist_join_r U T).
    (* Make some final naturality pulls *)
    repeat reassociate <-.
    change (map T (map U ?f)) with (map (T ∘ U) f).
    rewrite (natural (ϕ := @bdist U T _ )).
    unfold_ops @Map_compose.
    reassociate -> on left.
    rewrite (fun_map_map (F := U)).
    reassociate -> on left.
    now rewrite (fun_map_map (F := U)).
  Qed.

  #[export, program] Instance Monad_Beck : Monad (T ∘ U) :=
    {| mon_ret_natural := Natural_ret_Beck;
       mon_join_natural := Natural_join_Beck;
       mon_join_ret := fun A => join_ret_Beck;
       mon_join_map_ret := fun A => join_map_ret_Beck;
       mon_join_join := fun A => join_join_Beck; |}.

End BeckDistributivelaw_composite_monad.
