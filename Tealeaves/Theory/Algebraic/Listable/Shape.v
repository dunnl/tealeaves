From Tealeaves Require Export
  Classes.Algebraic.Listable.Functor.

Import List.ListNotations.
#[local] Open Scope list_scope.
#[local] Generalizable Variables F A B.

(** ** Basic reasoning principles for <<shape>> *)
(******************************************************************************)
Theorem shape_fmap `{Functor F} : forall (A B : Type) (f : A -> B) (t : F A),
    shape F (fmap F f t) = shape F t.
Proof.
  intros. compose near t on left.
  unfold shape. now rewrite (fun_fmap_fmap F).
Qed.

Theorem shape_shape `{Functor F} : forall A (t : F A),
    shape F (shape F t) = shape F t.
Proof.
  intros.  compose near t on left.
  unfold shape. now rewrite (fun_fmap_fmap F).
Qed.

(** * Properties of <<shape>> *)
(******************************************************************************)

(** ** Rewriting [shape] on lists *)
(******************************************************************************)
Section list_shape_rewrite.

  Lemma shape_nil : forall A,
      shape list (@nil A) = @nil unit.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_cons : forall A (a : A) (l : list A),
      shape list (a :: l) = tt :: shape list l.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_one : forall A (a : A),
      shape list [ a ] = [ tt ].
  Proof.
    reflexivity.
  Qed.

  Lemma shape_app : forall A (l1 l2 : list A),
      shape list (l1 ++ l2) = shape list l1 ++ shape list l2.
  Proof.
    intros. unfold shape. now rewrite fmap_list_app.
  Qed.

  Lemma shape_nil_iff : forall A (l : list A),
      shape list l = @nil unit <-> l = [].
  Proof.
    induction l. intuition.
    split; intro contra; now inverts contra.
  Qed.

End list_shape_rewrite.

#[export] Hint Rewrite @shape_nil @shape_cons @shape_one @shape_app : tea_rw_list.

(** ** Reasoning princples for <<shape>> on lists *)
(******************************************************************************)
Section list_shape_lemmas.

  Theorem shape_eq_app_r : forall A (l1 l2 r1 r2: list A),
      shape list r1 = shape list r2 ->
      (shape list (l1 ++ r1) = shape list (l2 ++ r2) <->
       shape list l1 = shape list l2).
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split. intros; eauto using List.app_inv_tail.
    intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_eq_app_l : forall A (l1 l2 r1 r2: list A),
      shape list l1 = shape list l2 ->
      (shape list (l1 ++ r1) = shape list (l2 ++ r2) <->
       shape list r1 = shape list r2).
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split. intros; eauto using List.app_inv_head.
    intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_eq_cons_iff : forall A (l1 l2 : list A) (x y : A),
      shape list (x :: l1) = shape list (y :: l2) <->
      shape list l1 = shape list l2.
  Proof.
    intros. rewrite 2(shape_cons).
    split; intros hyp. now inverts hyp.
    now rewrite hyp.
  Qed.

  Theorem inv_app_eq_ll : forall A (l1 l2 r1 r2 : list A),
      shape list l1 = shape list l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| ? ? IHl1 ];
                induction l2 as [| ? ? IHl2 ].
    - reflexivity.
    - introv shape_eq. now inverts shape_eq.
    - introv shape_eq. now inverts shape_eq.
    - introv shape_eq heq.
      rewrite shape_eq_cons_iff in shape_eq.
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem inv_app_eq_rl : forall A (l1 l2 r1 r2 : list A),
      shape list r1 = shape list r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| ? ? IHl1 ];
                induction l2 as [| ? ? IHl2 ].
    - reflexivity.
    - introv shape_eq heq. apply (inv_app_eq_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- shape_eq_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq. apply (inv_app_eq_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- shape_eq_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq.
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem inv_app_eq_lr : forall A (l1 l2 r1 r2 : list A),
      shape list l1 = shape list l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eauto using List.app_inv_head. }
    { eauto using inv_app_eq_ll. }
  Qed.

  Theorem inv_app_eq_rr : forall A (l1 l2 r1 r2 : list A),
      shape list r1 = shape list r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eauto using List.app_inv_head. }
    { eauto using inv_app_eq_rl. }
  Qed.

  Theorem inv_app_eq : forall A (l1 l2 r1 r2 : list A),
      shape list l1 = shape list l2 \/ shape list r1 = shape list r2 ->
      (l1 ++ r1 = l2 ++ r2) <-> (l1 = l2 /\ r1 = r2).
  Proof.
    introv [hyp | hyp]; split.
    - introv heq. split. eapply inv_app_eq_ll; eauto.
      eapply inv_app_eq_lr; eauto.
    - introv [? ?]. now subst.
    - introv heq. split. eapply inv_app_eq_rl; eauto.
      eapply inv_app_eq_rr; eauto.
    - introv [? ?]. now subst.
  Qed.

  Lemma list_app_inv_r : forall A (l l1 l2 : list A),
      l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    introv hyp. induction l.
    - cbn in hyp. auto.
    - inversion hyp. auto.
  Qed.

  Lemma list_app_inv_l : forall A (l l1 l2 : list A),
      l1 ++ l = l2 ++ l -> l1 = l2.
  Proof.
    introv hyp. eapply inv_app_eq_rl.
    2: eauto. reflexivity.
  Qed.

  Lemma list_app_inv_l2 : forall A (l1 l2 : list A) (a1 a2 : A),
      l1 ++ ret list a1 = l2 ++ ret list a2 ->
      l1 = l2.
  Proof.
    intros. eapply inv_app_eq_rl; [|eauto]; auto.
  Qed.

  Lemma list_app_inv_r2 : forall A (l1 l2 : list A) (a1 a2 : A),
      l1 ++ [a1] = l2 ++ [a2] ->
      a1 = a2.
  Proof.
    introv. introv hyp.
    apply inv_app_eq_rr in hyp.
    now inversion hyp. easy.
  Qed.

End list_shape_lemmas.

(** ** Reasoning principles for <<shape>> on listable functors *)
(** These principles are predicated just on <<tolist>> being a natural
    transformation and can be used to prove [shapeliness] for a given
    functor. *)
(******************************************************************************)
Section listable_shape_lemmas.

  Context
    (F : Type -> Type)
    `{Functor F}
    `{Tolist F} `{! Natural (@tolist F _)}.

  Lemma shape_fmap_1 : forall A1 A2 B (f : A1 -> B) (g : A2 -> B) t u,
      fmap F f t = fmap F g u ->
      shape F t = shape F u.
  Proof.
    introv hyp. cut (shape F (fmap F f t) = shape F (fmap F g u)).
    - now rewrite 2(shape_fmap).
    - now rewrite hyp.
  Qed.

  Lemma shape_tolist_1 : forall `(t : F A) `(u : F B),
      shape F t = shape F u ->
      shape list (tolist F t) = shape list (tolist F u).
  Proof.
    introv heq. compose near t. compose near u.
    unfold shape in *. rewrite 2(natural). unfold compose.
    now rewrite heq.
  Qed.

  Theorem shape_eq_impl_tolist : forall A (t s : F A),
      shape F t = shape F s ->
      shape list (tolist F t) = shape list (tolist F s).
  Proof.
    introv heq. compose near t on left; compose near s on right.
    unfold shape in *. rewrite natural.
    unfold compose. now rewrite heq.
  Qed.

  Corollary shape_l : forall A (l1 l2 : F A) (x y : list A),
      shape F l1 = shape F l2 ->
      (tolist F l1 ++ x = tolist F l2 ++ y) ->
      tolist F l1 = tolist F l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_ll, shape_eq_impl_tolist.
  Qed.

  Corollary shape_r : forall A (l1 l2 : F A) (x y : list A),
      shape F l1 = shape F l2 ->
      (x ++ tolist F l1 = y ++ tolist F l2) ->
      tolist F l1 = tolist F l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_rr, shape_eq_impl_tolist.
  Qed.

End listable_shape_lemmas.
