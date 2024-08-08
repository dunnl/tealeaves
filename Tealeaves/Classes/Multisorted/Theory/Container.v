 From Tealeaves Require Import
  Classes.Multisorted.DecoratedTraversableMonad
  Functors.List
  Functors.Constant.

Import TypeFamily.Notations.
Import Monoid.Notations.
Import List.ListNotations.
#[local] Open Scope list_scope.

#[local] Generalizable Variables A B C F G W T U K.

(** * Sorted lists with context *)
(******************************************************************************)
Section list.

  Context
    `{ix : Index}
    `{Monoid W}.

  Instance: MReturn (fun k A => list (W * (K * A))) :=
    fun A (k : K) (a : A) =>
      [(Ƶ, (k, a))].

  (** This operation is a context- and tag-sensitive substitution operation
   on lists of annotated values. It is used internally to reason about the
   interaction between <<mbinddt>> and <<tolistmd>>. *)
  Fixpoint mbinddt_list
           `(f : forall (k : K), W * A -> list (W * (K * B)))
           (l : list (W * (K * A))) : list (W * (K * B)) :=
    match l with
    | nil => nil
    | cons (w, (k, a)) rest =>
      map (F := list) (incr w) (f k (w, a)) ++ mbinddt_list f rest
    end.

  Lemma mbinddt_list_nil : forall
      `(f : forall (k : K), W * A -> list (W * (K * B))),
      mbinddt_list f nil = nil.
  Proof.
    intros. easy.
  Qed.

  Lemma mbinddt_list_ret : forall
      `(f : forall (k : K), W * A -> list (W * (K * B))) (k : K) (a : A),
      mbinddt_list f (mret (fun k A => list (W * (K * A))) k a) = f k (Ƶ, a).
  Proof.
    intros. cbn. List.simpl_list.
    replace (incr (Ƶ : W)) with (@id (W * (K * B))).
    - now rewrite (fun_map_id).
    - ext [w [k2 b]]. cbn. now simpl_monoid.
  Qed.

  Lemma mbinddt_list_cons : forall
      `(f : forall (k : K), W * A -> list (W * (K * B)))
      (w : W) (k : K) (a : A)
      (l : list (W * (K * A))),
      mbinddt_list f ((w, (k, a)) :: l) = map (F := list) (incr w) (f k (w, a)) ++ mbinddt_list f l.
  Proof.
    intros. easy.
  Qed.

  Lemma mbinddt_list_app : forall
      `(f : forall (k : K), W * A -> list (W * (K * B)))
      (l1 l2 : list (W * (K * A))),
      mbinddt_list f (l1 ++ l2) = mbinddt_list f l1 ++ mbinddt_list f l2.
  Proof.
    intros. induction l1.
    - easy.
    - destruct a as [w [k a]].
      cbn. rewrite IHl1.
      now rewrite List.app_assoc.
  Qed.

  #[global] Instance : forall `(f : forall (k : K), W * A -> list (W * (K * B))),
      ApplicativeMorphism (const (list (W * (K * A))))
                          (const (list (W * (K * B))))
                          (const (mbinddt_list f)).
  Proof.
    intros. eapply ApplicativeMorphism_monoid_morphism.
    Unshelve. constructor; try typeclasses eauto.
    - easy.
    - intros. apply mbinddt_list_app.
  Qed.

End list.


(** * Shape and contents *)
(******************************************************************************)
From Tealeaves Require Import
  Classes.Categorical.ContainerFunctor.

Import ContainerFunctor.Notations.
Import Misc.Subset.Notations.

(** ** Operations *)
(******************************************************************************)
Section shape_and_contents.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Definition shape {A} : U A -> U unit :=
    mmap U (allK (const tt)).

  Definition tolistmd_gen_loc {A}: K -> W * A -> list (W * (K * A)) :=
    fun k '(w, a) => [(w, (k, a))].

  Definition tolistmd_gen {A} (fake : Type) : U A -> list (W * (K * A)) :=
    mmapdt (B := fake) U (const (list (W * (K * A))))
           tolistmd_gen_loc.

  Definition tolistmd {A} : U A -> list (W * (K * A)) :=
    tolistmd_gen False.

  Definition tosetmd {A} : U A -> W * (K * A) -> Prop :=
    tosubset (F := list) ∘ tolistmd.

  Definition tolistm {A} : U A -> list (K * A) :=
    map (F := list) extract ∘ tolistmd.

  Definition tosetm {A} : U A -> K * A -> Prop :=
    tosubset (F := list) ∘ tolistm.

  Fixpoint filterk {A} (k : K) (l : list (W * (K * A))) : list (W * A) :=
    match l with
    | nil => nil
    | cons (w, (j, a)) ts =>
      if k == j then (w, a) :: filterk k ts else filterk k ts
    end.

  Definition toklistd {A} (k : K) : U A -> list (W * A) :=
    filterk k ∘ tolistmd.

  Definition toksetd {A} (k : K) : U A -> W * A -> Prop :=
    tosubset (F := list) ∘ toklistd k.

  Definition toklist {A} (k : K) : U A -> list A :=
    map (F := list) extract ∘ @toklistd A k.

End shape_and_contents.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈md t" :=
    (tosetmd _ t x) (at level 50) : tealeaves_multi_scope.

  Notation "x ∈m t" :=
    (tosetm _ t x) (at level 50) : tealeaves_multi_scope.

End Notations.

Import Notations.

(** ** Rewriting rules for <<filterk>> *)
(******************************************************************************)
Section rw_filterk.

  Context
    `{ix : Index} {W A : Type} (k : K).

  Implicit Types (l : list (W * (K * A))) (w : W) (a : A).

  Lemma filterk_nil : filterk k (nil : list (W * (K * A))) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filterk_cons_eq : forall l w a, filterk k (cons (w, (k, a)) l) = (w, a) :: filterk k l.
  Proof.
    intros. cbn. compare values k and k.
  Qed.

  Lemma filterk_cons_neq : forall l w a j, j <> k -> filterk k (cons (w, (j, a)) l) = filterk k l.
  Proof.
    intros. cbn. compare values k and j.
  Qed.

  Lemma filterk_app : forall l1 l2, filterk k (l1 ++ l2) = filterk k l1 ++ filterk k l2.
  Proof.
    intros. induction l1.
    - reflexivity.
    - destruct a as [w [i a]].
      compare values i and k.
      + rewrite <- (List.app_comm_cons l1).
        rewrite filterk_cons_eq.
        rewrite filterk_cons_eq.
        rewrite <- (List.app_comm_cons (filterk k l1)).
        now rewrite <- IHl1.
      + rewrite <- (List.app_comm_cons l1).
        rewrite filterk_cons_neq; auto.
        rewrite filterk_cons_neq; auto.
  Qed.

End rw_filterk.

#[export] Hint Rewrite @filterk_nil @filterk_cons_eq @filterk_cons_neq @filterk_app : tea_list.

From Tealeaves Require Import
  Functors.List
  Functors.Constant.

Import Product.Notations.
Import Monoid.Notations.
Import List.ListNotations.

Open Scope list_scope.


(** ** Auxiliary lemmas for allKant applicative functors *)
(******************************************************************************)
Section lemmas.

  #[local] Generalizable Variable M.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma mbinddt_constant_applicative1
        `{Monoid M} {B : Type}
        `(f : forall (k : K), W * A -> const M (T k B)) :
    mbinddt (B := B) U (const M) f =
    mbinddt (B := False) U (const M) (f : forall (k : K), W * A -> const M (T k False)).
  Proof.
    change_right (map (F := const M) (B := U B) (mmap U (const exfalso))
                       ∘ (mbinddt (B := False) U (const M) (f : forall (k : K), W * A -> const M (T k False)))).
    rewrite (mmap_mbinddt U (F := const M)).
    reflexivity.
  Qed.

  Lemma mbinddt_constant_applicative2 (fake1 fake2 : Type) `{Monoid M}
        `(f : forall (k : K), W * A -> const M (T k B)) :
    mbinddt (B := fake1) U (const M)
            (f : forall (k : K), W * A -> const M (T k fake1))
    = mbinddt (B := fake2) U (const M)
              (f : forall (k : K), W * A -> const M (T k fake2)).
  Proof.
    intros.
    rewrite (mbinddt_constant_applicative1 (B := fake1)).
    rewrite (mbinddt_constant_applicative1 (B := fake2)). easy.
  Qed.

  Lemma tolistmd_equiv1 : forall (fake : Type) (A : Type),
      tolistmd_gen U (A := A) False = tolistmd_gen U fake.
  Proof.
    intros. unfold tolistmd_gen at 2, mmapdt.
    now rewrite (mbinddt_constant_applicative2 fake False).
  Qed.

  Lemma tolistmd_equiv : forall (fake1 fake2 : Type) (A : Type),
      tolistmd_gen U (A := A) fake1 = tolistmd_gen U fake2.
  Proof.
    intros. rewrite <- tolistmd_equiv1.
    rewrite <- (tolistmd_equiv1 fake2).
    easy.
  Qed.

End lemmas.

(** ** Relating <<∈m>> and <<∈md>> *)
(******************************************************************************)
Section DTM_membership_lemmas.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma inmd_iff_in : forall (k : K) (A : Type) (a : A) (t : U A),
      (k, a) ∈m t <-> exists w, (w, (k, a)) ∈md t.
  Proof.
    intros. unfold tosetm, tosetmd, tolistm, compose.
    induction (tolistmd U t).
    - cbv; split; intros []; easy.
    - destruct a0 as [w' [k' a']].
      rewrite map_list_cons.
      rewrite tosubset_list_cons.
      rewrite tosubset_list_cons.
      rewrite subset_in_add.
      rewrite IHl.
      split; [ intros [Hfst|[w Hrest]] | intros [w [rest1|rest2]]].
      + exists w'. left.
        rewrite Hfst. easy.
      + exists w. now right.
      + left.
        cbv in rest1.
        now inversion rest1.
      + right. rewrite <- IHl.
        compose near l.
        rewrite tosubset_list_map.
        unfold compose.
        exists (w, (k, a)).
        easy.
  Qed.

  Corollary inmd_implies_in : forall (k : K) (A : Type) (a : A) (w : W) (t : U A),
      (w, (k, a)) ∈md t -> (k, a) ∈m t.
  Proof.
    intros. rewrite inmd_iff_in. eauto.
  Qed.

End DTM_membership_lemmas.

(** ** Characterizing membership in list operations *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma in_filterk_iff : forall (A : Type) (l : list (W * (K * A))) (k : K) (a : A) (w : W),
      (w, a) ∈ filterk k l <-> (w, (k, a)) ∈ l.
  Proof.
    intros. induction l.
    - cbn. easy.
    - destruct a0 as [w' [j a']]. cbn. compare values k and j.
      + cbn. rewrite IHl. clear. split.
        { intros [hyp1 | hyp2].
          - inverts hyp1. now left.
          - now right.
        }
        { intros [hyp1 | hyp2].
          - inverts hyp1. now left.
          - now right. }
      + rewrite <- IHl. split.
        { intro hyp. now right. }
        { intros [hyp1 | hyp2].
          - inverts hyp1. contradiction.
          - auto. }
  Qed.

  Lemma inmd_iff_in_tolistmd : forall (A : Type) (k : K) (a : A) (w : W) (t : U A),
      (w, (k, a)) ∈md t <-> (w, (k, a)) ∈ tolistmd U t.
  Proof.
    reflexivity.
  Qed.

  Lemma in_iff_in_tolistmd : forall (A : Type) (k : K) (a : A) (t : U A),
      (k, a) ∈m t <-> (k, a) ∈ tolistm U t.
  Proof.
    reflexivity.
  Qed.

  Lemma inmd_iff_in_toklistd : forall (A : Type) (k : K) (a : A) (w : W) (t : U A),
      (w, (k, a)) ∈md t <-> (w, a) ∈ toklistd U k t.
  Proof.
    intros. unfold toklistd. unfold compose.
    rewrite in_filterk_iff. reflexivity.
  Qed.

  Lemma in_iff_in_toklist : forall (A : Type) (k : K) (a : A) (t : U A),
      (k, a) ∈m t <-> a ∈ toklist U k t.
  Proof.
    intros. unfold toklist. unfold compose.
    rewrite (in_map_iff list). split.
    - intro hyp. rewrite inmd_iff_in in hyp.
      destruct hyp as [w' hyp].
      exists (w', a). rewrite inmd_iff_in_toklistd in hyp.
      auto.
    - intros [[w' a'] [hyp1 hyp2]]. rewrite inmd_iff_in.
      exists w'. rewrite <- inmd_iff_in_toklistd in hyp1. cbn in hyp2.
      now subst.
  Qed.

End DTM_tolist.

(** ** Interaction between <<tolistmd>> and <<mret>>/<<mbindd>> *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma tolistmd_gen_mret : forall (A B : Type) (a : A) (k : K),
      tolistmd_gen (T k) B (mret T k a) = [ (Ƶ, (k, a)) ].
  Proof.
    intros. unfold tolistmd_gen.
    compose near a on left.
    now rewrite mmapdt_comp_mret.
  Qed.

  Corollary tolistmd_mret : forall (A : Type) (a : A) (k : K),
      tolistmd (T k) (mret T k a) = [ (Ƶ, (k, a)) ].
  Proof.
    intros. unfold tolistmd. apply tolistmd_gen_mret.
  Qed.

  Corollary tosetmd_mret : forall (A : Type) (a : A) (k : K),
      tosetmd (T k) (mret T k a) = {{ (Ƶ, (k, a)) }}.
  Proof.
    intros. unfold tosetmd, compose. rewrite tolistmd_mret.
    rewrite tosubset_list_one.
    reflexivity.
  Qed.

  Corollary tolistm_mret : forall (A : Type) (a : A) (k : K),
      tolistm (T k) (mret T k a) = [ (k, a) ].
  Proof.
    intros. unfold tolistm, compose.
    rewrite tolistmd_mret. easy.
  Qed.

  Corollary tosetm_mret : forall (A : Type) (a : A) (k : K),
      tosetm (T k) (mret T k a) = {{ (k, a) }}.
  Proof.
    intros. unfold tosetm, compose.
    rewrite tolistm_mret.
    apply tosubset_list_ret.
  Qed.

  Lemma tolistmd_gen_mbindd :
    forall (fake : Type)
      `(f : forall k, W * A -> T k B) (t : U A),
      tolistmd_gen U fake (mbindd U f t) =
      mbinddt_list (fun k '(w, a) => tolistmd_gen (T k) fake (f k (w, a))) (tolistmd_gen U fake t).
  Proof.
    intros. unfold tolistmd_gen, mmapdt.
    compose near t on left.
    rewrite (mbinddt_mbindd U).
    compose near t on right.
    change (mbinddt_list ?f) with (const (mbinddt_list f) (U fake)).
    #[local] Set Keyed Unification. (* TODO figure out why this is here. *)
    rewrite (dtp_mbinddt_morphism W T U
                                  (const (list (W * (K * A))))
                                  (const (list (W * (K * B))))
                                  (A := A) (B := fake)).
    #[local] Unset Keyed Unification.
    fequal. ext k [w a].
    cbn.
    change (map (F := list) ?f) with (const (map (F := list) f) (U B)).
    List.simpl_list.
    compose near (f k (w, a)) on right.
    (* for some reason I can't rewrite without posing first. *)
    pose (rw := dtp_mbinddt_morphism
                  W T (T k)
                  (const (list (W * (K * B))))
                  (const (list (W * (K * B))))
                  (ϕ := (const (map (F := list) (incr w))))
                  (A := B) (B := fake)).
    rewrite rw. fequal. now ext k2 [w2 b].
  Qed.

  Corollary tolistmd_mbindd : forall
      `(f : forall k, W * A -> T k B) (t : U A),
      tolistmd U (mbindd U f t) =
      mbinddt_list (fun k '(w, a) => tolistmd (T k) (f k (w, a))) (tolistmd U t).
  Proof.
    intros. unfold tolistmd. apply tolistmd_gen_mbindd.
  Qed.

End DTM_tolist.

(** ** Characterizing occurrences post-operation *)
(******************************************************************************)
Section DTM_membership.

  Context
    (U : Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  (** *** Occurrences in <<mret>> *)
  (******************************************************************************)
  Lemma inmd_mret_iff : forall (A : Type) (a1 a2 : A) (k1 k2 : K) (w : W),
      (w, (k2, a2)) ∈md mret T k1 a1 <-> w = Ƶ /\ k1 = k2 /\ a1 = a2.
  Proof.
    intros. rewrite (tosetmd_mret).
    autorewrite with tea_set.
    split.
    - inversion 1; now subst.
    - introv [? [? ?]]. now subst.
  Qed.

  Corollary in_mret_iff : forall (A : Type) (a1 a2 : A) (k1 k2 : K),
      (k2, a2) ∈m mret T k1 a1 <-> k1 = k2 /\ a1 = a2.
  Proof.
    intros. rewrite inmd_iff_in. setoid_rewrite inmd_mret_iff.
    firstorder.
  Qed.

  Lemma inmd_mret_eq_iff : forall (A : Type) (a1 a2 : A) (k : K) (w : W),
      (w, (k, a2)) ∈md mret T k a1 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros. rewrite inmd_mret_iff. clear. firstorder.
  Qed.

  Lemma inmd_mret_neq_iff : forall (A : Type) (a1 a2 : A) (k j : K) (w : W),
      k <> j ->
      (w, (j, a2)) ∈md mret T k a1 <-> False.
  Proof.
    intros. rewrite inmd_mret_iff. firstorder.
  Qed.

  Corollary in_mret_eq_iff : forall (A : Type) (a1 a2 : A) (k : K),
      (k, a2) ∈m mret T k a1 <-> a1 = a2.
  Proof.
    intros. rewrite in_mret_iff. firstorder.
  Qed.

  Corollary in_mret_neq_iff : forall (A : Type) (a1 a2 : A) (k j : K),
      k <> j ->
      (j, a2) ∈m mret T k a1 <-> False.
  Proof.
    intros. rewrite inmd_iff_in. setoid_rewrite inmd_mret_iff.
    firstorder.
  Qed.

  Lemma tosubset_map_iff: forall {A B:Type} (l: list A) (f: A -> B),
      tosubset (map f l) = map f (tosubset l).
  Proof.
    intros.
    compose near l.
    rewrite tosubset_list_map.
    reflexivity.
  Qed.

  (** *** Occurrences in <<mbindd>> with context *)
  (******************************************************************************)
  Lemma inmd_mbindd_iff1 :
    forall `(f : forall k, W * A -> T k B) (t : U A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbindd U f t ->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold tosetmd, compose in *.
    rewrite (tolistmd_mbindd U) in hyp. induction (tolistmd U t).
    - inversion hyp.
    - destruct a as [w [k a]]. rewrite mbinddt_list_cons in hyp.
      rewrite tosubset_list_app in hyp. destruct hyp as [hyp1 | hyp2].
      + rewrite tosubset_map_iff in hyp1.
        destruct hyp1 as [[w2 [k2' b']] [hyp1 hyp2]].
        inversion hyp2; subst. exists k w w2 a. splits.
        { rewrite tosubset_list_cons. now left. }
        { auto. }
        { easy. }
      + apply IHl in hyp2. clear IHl.
        destruct hyp2 as [k1 [w1 [w2 [a' [hyp1 [hyp2 hyp3]] ]]]].
        subst. repeat eexists.
        { rewrite tosubset_list_cons. right. eauto. }
        { auto. }
  Qed.

  Lemma inmd_mbindd_iff2 :
    forall `(f : forall k, W * A -> T k B) (t : U A) (k2 : K) (wtotal : W) (b : B),
    (exists (k1 : K) (w1 w2 : W) (a : A),
      (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2) ->
      (wtotal, (k2, b)) ∈md mbindd U f t.
  Proof.
    introv [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]. subst.
    unfold tosetmd, compose in *. rewrite (tolistmd_mbindd U).
    induction (tolistmd U t).
    - inversion hyp1.
    - destruct a0 as [w [k' a']]. rewrite mbinddt_list_cons.
      simpl_list. rewrite tosubset_list_cons in hyp1. destruct hyp1 as [hyp1 | hyp1].
      + inverts hyp1. left. rewrite (tosubset_map_iff). exists (w2, (k2, b)).
        now splits.
      + right. now apply IHl in hyp1.
  Qed.

  Theorem inmd_mbindd_iff :
    forall `(f : forall k, W * A -> T k B) (t : U A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbindd U f t <->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using inmd_mbindd_iff1, inmd_mbindd_iff2.
  Qed.

  (** *** Corollaries for other operations *)
  (******************************************************************************)
  Corollary inmd_mbind_iff :
    forall `(f : forall k, A -> T k B) (t : U A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbind U f t <->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 a
        /\ wtotal = w1 ● w2.
  Proof.
    intros.
    rewrite mbind_to_mbindd.
    rewrite inmd_mbindd_iff.
    reflexivity.
  Qed.

  Corollary inmd_mmapd_iff :
    forall `(f : forall k, W * A -> B) (t : U A) (k : K) (w : W) (b : B),
      (w, (k, b)) ∈md mmapd U f t <->
      exists (a : A), (w, (k, a)) ∈md t /\ b = f k (w, a).
  Proof.
    intros. unfold mmapd, compose. setoid_rewrite inmd_mbindd_iff.
    unfold_ops @Map_I. setoid_rewrite inmd_mret_iff.
    split.
    - intros [k1 [w1 [w2 [a [hyp1 [[hyp2 [hyp2' hyp2'']] hyp3]]]]]].
      subst. exists a. simpl_monoid. auto.
    - intros [a [hyp1 hyp2]]. subst. repeat eexists.
      easy. now simpl_monoid.
  Qed.

  Corollary inmd_mmap_iff :
    forall `(f : K -> A -> B) (t : U A) (k : K) (w : W) (b : B),
      (w, (k, b)) ∈md mmap U f t <->
      exists (a : A), (w, (k, a)) ∈md t /\ b = f k a.
  Proof.
    intros. rewrite (mmap_to_mmapd U).
    rewrite inmd_mmapd_iff. easy.
  Qed.

  (** *** Occurrences without context *)
  (******************************************************************************)
  Theorem in_mbindd_iff :
    forall `(f : forall k, W * A -> T k B) (t : U A) (k2 : K) (b : B),
      (k2, b) ∈m mbindd U f t <->
      exists (k1 : K) (w1 : W) (a : A),
        (w1, (k1, a)) ∈md t
        /\ (k2, b) ∈m (f k1 (w1, a)).
  Proof.
    intros.
    rewrite inmd_iff_in. setoid_rewrite inmd_mbindd_iff. split.
    - intros [wtotal [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]].
      exists k1 w1 a. split; [auto|].
      apply (inmd_implies_in) in hyp2. auto.
    - intros [k1 [w1 [a [hyp1 hyp2]]]].
      rewrite inmd_iff_in in hyp2. destruct hyp2 as [w2 rest].
      exists (w1 ● w2) k1 w1 w2 a. intuition.
  Qed.

  (** *** Corollaries for other operations *)
  (******************************************************************************)
  Corollary in_mbind_iff :
    forall `(f : forall k, A -> T k B) (t : U A) (k2 : K) (b : B),
      (k2, b) ∈m mbind U f t <->
      exists (k1 : K) (a : A), (k1, a) ∈m t /\ (k2, b) ∈m f k1 a.
  Proof.
    intros. unfold mbind, compose. setoid_rewrite inmd_iff_in.
    setoid_rewrite inmd_mbindd_iff. cbn. split.
    - firstorder.
    - intros [k1 [a [[w1 hyp1] [w hyp2]]]].
      repeat eexists; eauto.
  Qed.

  Corollary in_mmapd_iff :
    forall `(f : forall k, W * A -> B) (t : U A) (k : K) (b : B),
      (k, b) ∈m mmapd U f t <->
      exists (w : W) (a : A), (w, (k, a)) ∈md t /\ b = f k (w, a).
  Proof.
    intros. setoid_rewrite inmd_iff_in.
    now setoid_rewrite inmd_mmapd_iff.
  Qed.

  Corollary in_mmap_iff :
    forall `(f : forall k, A -> B) (t : U A) (k : K) (b : B),
      (k, b) ∈m mmap U f t <->
      exists (a : A), (k, a) ∈m t /\ b = f k a.
  Proof.
    intros. setoid_rewrite inmd_iff_in.
    setoid_rewrite inmd_mmap_iff.
    firstorder.
  Qed.

End DTM_membership.
