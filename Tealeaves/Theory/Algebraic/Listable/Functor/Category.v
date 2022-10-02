From Tealeaves Require Import
  Classes.Algebraic.Listable.Functor
  Theory.Algebraic.Listable.Shape.

Import List.ListNotations.
#[local] Open Scope list_scope.
#[local] Generalizable Variables F G.

(** * Listable functors form a monoidal category *)
(******************************************************************************)

(** ** The identity functor is listable *)
(******************************************************************************)
#[export] Instance Tolist_I : Tolist (fun x => x) := fun A x => [x].

#[export] Instance: Natural (@tolist (fun x => x) _).
Proof.
  constructor; try typeclasses eauto.
  reflexivity.
Qed.

Theorem shapeliness_I : shapeliness (fun x => x).
Proof.
  intros A t1 t2. cbv. intros [? heq]. now inversion heq.
Qed.

#[export] Instance ListableFunctor_I : ListableFunctor (fun x => x) :=
  {| lfun_shapeliness := shapeliness_I; |}.

(** ** Listable functors are closed under composition *)
(******************************************************************************)
Section listable_compose.

  Context
    `{ListableFunctor F}
    `{ListableFunctor G}.

  #[export] Instance Tolist_compose : Tolist (F ∘ G) :=
    fun A => join list ∘ tolist F ∘ fmap F (tolist G).

  #[local] Unset Keyed Unification.

  Lemma Tolist_compose_natural : Natural (F := F ∘ G) Tolist_compose.
  Proof.
    constructor; try typeclasses eauto.
    introv. unfold Tolist_compose.
    repeat reassociate <- on left. rewrite natural.
    repeat reassociate -> on left;
      reassociate <- near (fmap (list ∘ list) f).
    unfold_ops @Fmap_compose; unfold_compose_in_compose;
      rewrite (natural).
    repeat reassociate -> on left. rewrite (fun_fmap_fmap F).
    repeat reassociate -> on right. rewrite (fun_fmap_fmap F).
    now rewrite natural.
  Qed.

  Lemma shape_compose_spec {A} :
    shape (F ∘ G) (A := A) = fmap F (shape G).
  Proof.
    reflexivity.
  Qed.

  Lemma shape_compose_1 : forall A (t u : F (G A)),
      shape (F ∘ G) t = shape (F ∘ G) u ->
      shape F t = shape F u.
  Proof.
    introv hyp. rewrite shape_compose_spec in hyp.
    now apply (shape_fmap_1 F) in hyp.
  Qed.

  Lemma shape_compose_2 : forall A (t u : F (G A)),
      shape (F ∘ G) t = shape (F ∘ G) u ->
      fmap list (shape G) (tolist F t) = fmap list (shape G) (tolist F u).
  Proof.
    intros. compose near t. compose near u.
    rewrite natural. unfold compose.
    fequal. assumption.
  Qed.

  Lemma shapeliness_compose_1 : forall A (l1 l2 : list (G A)),
      fmap list (shape G) l1 = fmap list (shape G) l2 ->
      join list (fmap list (tolist G) l1) = join list (fmap list (tolist G) l2) ->
      l1 = l2.
  Proof.
    intros. generalize dependent l2.
    induction l1; intros l2 hshape hcontents.
    - destruct l2.
      + reflexivity.
      + inversion hshape.
    - destruct l2.
      + inversion hshape.
      + autorewrite with tea_list in *.
        inversion hshape.
        assert (heq : tolist G a = tolist G g)
          by eauto using (shape_l G).
        rewrite heq in hcontents. fequal.
        * auto using (lfun_shapeliness G).
        * eauto using list_app_inv_r.
  Qed.

  Theorem shapeliness_compose : shapeliness (F ∘ G).
  Proof.
    intros A t1 t2 [hshape hcontents].
      unfold tolist, Tolist_compose in hcontents.
      reassociate -> in hcontents.
      #[local] Set Keyed Unification.
      rewrite <- (natural (F := F) (G := list)) in hcontents.
      #[local] Unset Keyed Unification.
      unfold compose in hcontents.
      apply (lfun_shapeliness F); split.
      + auto using shape_compose_1.
      + auto using shapeliness_compose_1, shape_compose_2.
  Qed.

  #[export] Instance ListableFunctor_compose : ListableFunctor (F ∘ G) :=
    {| lfun_natural := Tolist_compose_natural;
       lfun_functor := Functor_compose;
       lfun_shapeliness := shapeliness_compose;
    |}.

End listable_compose.
