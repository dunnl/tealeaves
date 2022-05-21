From Tealeaves Require Export
     Classes.Applicative
     Classes.SetlikeFunctor
     Functors.Batch.

From Multisorted Require Import
     Classes.DTM
     Functors.Tag
     Functors.MList2.

Import Product.Notations. (* for (W ×) *)
Import Monoid.Notations.
Import Multisorted.Theory.Category.Notations.
Import Batch.Notations.
Import List.ListNotations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.
#[local] Open Scope list_scope.

(*
Import SetlikeFunctor.Notations.
*)

(** * Shape and contents *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section shape_and_contents.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Definition shape {A} : S A -> S unit :=
    mfmap S (const (const tt)).

  Definition tomlistd_gen {A} (fake : Type) : S A -> list (W * Tag A) :=
    mfmapdt (B := fake) S (const (list (W * Tag A))) (fun k '(w, a) => [(w, (k, a))]).

  Definition tomlistd {A} : S A -> list (W * Tag A) :=
    tomlistd_gen False.

  Definition tomsetd {A} : S A -> W * Tag A -> Prop :=
    toset list ∘ tomlistd.

  Definition tomlist {A} : S A -> list (Tag A) :=
    fmap list snd ∘ tomlistd.

  Definition tomset {A} : S A -> Tag A -> Prop :=
    toset list ∘ tomlist.

  Fixpoint filterk {A} (k : K) (l : list (W * Tag A)) : list (W * A) :=
    match l with
    | nil => nil
    | cons (w, (j, a)) ts =>
      if k == j then (w, a) :: filterk k ts else filterk k ts
    end.

  Definition toklistd {A} (k : K) : S A -> list (W * A) :=
    filterk k ∘ tomlistd.

  Definition toksetd {A} (k : K) : S A -> W * A -> Prop :=
    toset list ∘ toklistd k.

  Definition toklist {A} (k : K) : S A -> list A :=
    fmap list (extract (W ×)) ∘ @toklistd A k.

End shape_and_contents.

(* TODO This is only for <<exfalso>> *)
Require Tealeaves.Classes.TraversableFunctor.

(** ** Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mbinddt_constant_applicative1
        `{Monoid M} {B : Type}
        `(f : forall (k : K), W * A -> const M (T k B)) :
    mbinddt (B := B) S (const M) f =
    mbinddt (B := False) S (const M) (f : forall (k : K), W * A -> const M (T k False)).
  Proof.
    change_right (fmap (B := S B) (const M) (mfmap S (const TraversableFunctor.exfalso))
                       ∘ (mbinddt (B := False) S (const M) (f : forall (k : K), W * A -> const M (T k False)))).
    rewrite (mfmap_mbinddt S (F := const M)).
    fequal. ext k [w a]. easy.
  Qed.

  Lemma mbinddt_constant_applicative2 (fake1 fake2 : Type) `{Monoid M}
        `(f : forall (k : K), W * A -> const M (T k B)) :
    mbinddt (B := fake1) S (const M)
            (f : forall (k : K), W * A -> const M (T k fake1))
    = mbinddt (B := fake2) S (const M)
              (f : forall (k : K), W * A -> const M (T k fake2)).
  Proof.
    intros. rewrite (mbinddt_constant_applicative1 (B := fake1)).
    rewrite (mbinddt_constant_applicative1 (B := fake2)). easy.
  Qed.

  Lemma tomlistd_equiv1 : forall (fake : Type) (A : Type),
      tomlistd_gen S (A := A) False = tomlistd_gen S fake.
  Proof.
    intros. unfold tomlistd_gen at 2, mfmapdt.
    now rewrite (mbinddt_constant_applicative2 fake False).
  Qed.

  Lemma tomlistd_equiv : forall (fake1 fake2 : Type) (A : Type),
      tomlistd_gen S (A := A) fake1 = tomlistd_gen S fake2.
  Proof.
    intros. rewrite <- tomlistd_equiv1.
    rewrite <- (tomlistd_equiv1 fake2).
    easy.
  Qed.

End lemmas.

(** ** Interaction between <tomlistd>> and <<mbindd>> *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma tomlistd_gen_mbindd : forall
      `(f : forall k, W * A -> T k B) (t : S A),
      tomlistd_gen S B (mbindd S f t) =
      mbinddt_list (fun k '(w, a) => tomlistd_gen (T k) B (f k (w, a))) (tomlistd_gen S B t).
  Proof.
    intros. unfold tomlistd_gen, mfmapdt.
    compose near t on left.
    rewrite (mbinddt_mbindd S).
    compose near t on right.
    change (mbinddt_list ?f) with (const (mbinddt_list f) (S B)).
    #[local] Set Keyed Unification. (* TODO figure out why this is here. *)
    rewrite (dtp_mbinddt_morphism W S T
                                  (const (list (W * Tag A)))
                                  (const (list (W * Tag B)))
                                  (A := A) (B := B)).
    #[local] Unset Keyed Unification.
    fequal. ext k [w a].
    cbn.
    change (fmap list ?f) with (const (fmap list f) (S B)).
    List.simpl_list.
    compose near (f k (w, a)) on right.
    (* for some reason I can't rewrite without posing first. *)
    pose (rw := dtp_mbinddt_morphism
                  W (T k) T
                  (const (list (W * Tag B)))
                  (const (list (W * Tag B)))
                  (ϕ := (const (fmap list (incr w))))
                  (A := B) (B := B)).
    rewrite rw. fequal. now ext k2 [w2 b].
  Qed.

End DTM_tolist.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Notation "x ∈md t" :=
    (tomsetd _ t x) (at level 50) : tealeaves_multi_scope.

  Notation "x ∈m t" :=
    (tomset _ t x) (at level 50) : tealeaves_multi_scope.

End Notations.

Import Notations.

(** ** Relating <<∈m>> and <<∈md>> *)
(******************************************************************************)
Section DTM_membership.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma ind_iff_in : forall (k : K) (A : Type) (a : A) (t : S A),
      (k, a) ∈m t <-> exists w, (w, (k, a)) ∈md t.
  Proof.
    intros. unfold tomset, tomsetd, tomlist, compose.
    induction (tomlistd S t).
    - cbv; split; intros []; easy.
    - rewrite fmap_list_cons, in_list_cons. rewrite IHl.
      setoid_rewrite in_list_cons.
      split; [ intros [Hfst|[w Hrest]] | intros [w [rest1|rest2]]].
      + destruct a0 as [w [k' a']]. exists w. left.
        rewrite Hfst. easy.
      + exists w. now right.
      + left. now rewrite <- rest1.
      + right. rewrite <- IHl.
        rewrite (in_fmap_iff list). now exists (w, (k, a)).
  Qed.

  Corollary ind_implies_in : forall (k : K) (A : Type) (a : A) (w : W) (t : S A),
      (w, (k, a)) ∈md t -> (k, a) ∈m t.
  Proof.
    intros. rewrite ind_iff_in. eauto.
  Qed.

End DTM_membership.

(** ** Characterizing occurrences post-operation *)
(******************************************************************************)
Section DTM_membership2.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Occurrences with context *)
  (******************************************************************************)
  Theorem ind_mbindd_iff :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md (mbindd S f t) <->
      exists (k1 : K) (w1 w2 : W) (a : A), (w1, (k1, a)) ∈md t
                                      /\ (w2, (k2, b)) ∈md (f k1 (w1, a))
                                      /\ wtotal = w1 ● w2.
  Proof.
    intros. unfold tomsetd, tomlistd. unfold compose.
    repeat rewrite (tomlistd_equiv S False B).
    rewrite (tomlistd_gen_mbindd S).
    induction (tomlistd_gen S B t).
    - cbn. split; try easy. intros [k [w1 [w2 [a rest]]]]. intuition.
    - split.
      + destruct a as [w [k a]].
        rewrite mbinddt_list_cons. rewrite in_list_app.
        setoid_rewrite in_list_cons.
        { intros [hyp|hyp]. exists k w. admit.
  Admitted.

  (** *** Occurrences without context *)
  (******************************************************************************)
  Corollary in_mbindd_iff :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (b : B),
      (k2, b) ∈m mbindd S f t <->
      exists (k1 : K) (w1 : W) (a : A),
        (w1, (k1, a)) ∈md t
        /\ (k2, b) ∈m (f k1 (w1, a)).
  Proof.
    intros.
    rewrite ind_iff_in. setoid_rewrite ind_mbindd_iff. split.
    - intros [wtotal [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]].
      exists k1 w1 a. split; [auto|].
      apply (ind_implies_in) in hyp2. auto.
    - intros [k1 [w1 [a [hyp1 hyp2]]]].
      rewrite ind_iff_in in hyp2. destruct hyp2 as [w2 rest].
      exists (w1 ● w2) k1 w1 w2 a. intuition.
  Qed.

End DTM_membership2.

(** * DTMs as (particular) <<Batch>> coalgebras *)
(******************************************************************************)
Section traversals_coalgebras.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Definition batch {A : Type} (B : Type) : K -> A -> @Batch (Tag A) B B :=
    fun k a => Go (@id B) ⧆ (k, a).
  Definition iterate {A : Type} (B : Type) : S A -> @Batch (Tag A) B (S B) :=
    mfmapt S (@Batch (Tag A) B) (batch B).

  Definition batchd {A : Type} (B : Type) : K -> W * A -> @Batch (W * Tag A) B B :=
    fun k '(w, a) => Go (@id B) ⧆ (w, (k, a)).
  Definition iterated {A : Type} (B : Type) : S A -> @Batch (W * Tag A) B (S B) :=
    mfmapdt S (@Batch (W * Tag A) B) (batchd B).

End traversals_coalgebras.

(** ** Decomposing traversals in terms of <<iterate>> *)
(******************************************************************************)
Section traversal_iterate.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma iterate_to_iterated `{Applicative F} `(f : K -> A -> F B) (t : S A) :
    runBatch (uncurry f) (iterate B t) = runBatch (fun '(w, (k, a)) => f k a) (iterated B t).
  Proof.
    unfold iterated. unfold iterate. unfold mfmapt. unfold mfmapdt. unfold mbindt.
    compose near t.
    rewrite (dtp_mbinddt_morphism W S T _ _ (ϕ := @runBatch (W * Tag A) F B _ _ _ _)).
    rewrite (dtp_mbinddt_morphism W S T _ _ (ϕ := @runBatch (Tag A) F B _ _ _ _)).
    fequal. now ext k [w a].
  Qed.

  Lemma iterate_to_iterated2 `(f : K -> A -> B) (t : S A) :
    runBatch (uncurry f) (iterate B t) = runBatch (fun '(w, (k, a)) => f k a) (iterated B t).
  Proof.
    apply (iterate_to_iterated (F := fun x => x)).
  Qed.

  (** ** Identities for <<mfmapdt>>, <<mfmapd>> *)
  (******************************************************************************)
  Lemma mfmapdt_to_runBatch `{Applicative F} `(f : K -> W * A -> F B) (t : S A) :
    mfmapdt S F f t = runBatch (fun '(w, (k, a)) => f k (w, a)) (iterated B t).
  Proof.
    unfold iterated, mfmapdt.
    compose near t on right.
    rewrite (dtp_mbinddt_morphism W S T _ _ (ϕ := @runBatch (W * Tag A) F B _ _ _ _)).
    fequal. ext k [w a]. unfold compose; cbn. now rewrite <- fmap_to_ap.
  Qed.

  Lemma mfmapd_to_runBatch `(f : K -> W * A -> B) (t : S A) :
    mfmapd S f t = runBatch (fun '(w, (k, a)) => f k (w, a)) (iterated B t).
  Proof.
    unfold mfmapd.
    now rewrite mfmapdt_to_runBatch.
  Qed.

  (** ** Identities for <<mfmapt>>, <<mfmap>> *)
  (******************************************************************************)
  Lemma mfmapt_to_runBatch `{Applicative F} `(f : K -> A -> F B) (t : S A) :
    mfmapt S F f t = runBatch (uncurry f) (iterate B t).
  Proof.
    unfold iterate, mfmapt, mbindt.
    compose near t on right.
    rewrite (dtp_mbinddt_morphism W S T _ _ (ϕ := @runBatch (Tag A) F B (uncurry f) _ _ _)).
    fequal. ext k [w a]. unfold compose; cbn. now rewrite <- fmap_to_ap.
  Qed.

  Lemma mfmap_to_runBatch `(f : K -> A -> B) (t : S A) :
    mfmap S f t = runBatch (uncurry f) (iterate B t).
  Proof.
    unfold mfmap, mfmapd.
    rewrite mfmapdt_to_runBatch.
    rewrite (iterate_to_iterated (F := fun x => x)).
    easy.
  Qed.

  (** ** Identities for <<tolist>> and <<foldMap>> *)
  (******************************************************************************)
  Lemma tomlistd_gen_to_runBatch `{Applicative F} `(t : S A) (fake : Type) :
    tomlistd_gen S fake t = runBatch (ret list : _ -> const (list (W * Tag A)) _) (iterated fake t).
  Proof.
  Admitted.

  Lemma tomlistd_to_runBatch `{Applicative F} `(t : S A) :
    tomlistd S t = runBatch (ret list : _ -> const (list (W * Tag A)) _) (iterated (W * Tag A) t).
  Proof.
    unfold iterate. unfold tomlistd, tomlistd_gen.
    rewrite mfmapdt_to_runBatch. admit.
  Admitted.

  Lemma tomlist_to_runBatch `{Applicative F} `(t : S A) :
    tomlist S t = runBatch (ret list : Tag A -> const (list (Tag A)) (Tag A)) (iterate (Tag A) t).
  Proof.
    unfold iterate. unfold tomlist.
  Admitted.

  (** ** Other identities *)
  (******************************************************************************)
  Lemma id_to_runBatch `{Applicative F} `(t : S A) (fake : Type) :
    t = runBatch (F := fun x => x) (fun '(w, (k, a)) => a)
                 (iterated A t : @Batch (W * Tag A) A (S A)).
  Proof.
    change t with (id t).
    rewrite <- (dtp_mbinddt_mret W S T).
    unfold iterated.
  Admitted.

End traversal_iterate.

(** * Shapeliness *)
(******************************************************************************)
Section shapeliness.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Theorem shapeliness : forall A (t1 t2 : S A),
      shape S t1 = shape S t2 /\
      tomlistd S t1 = tomlistd S t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    unfold shape in hyp1.
    do 2 rewrite mfmap_to_runBatch in hyp1.
    do 2 rewrite (iterate_to_iterated (F := fun x => x)) in hyp1.
    unfold tomlistd in hyp2.
    rewrite (tomlistd_equiv S False unit) in hyp2.
    rewrite (tomlistd_gen_to_runBatch t1 unit) in hyp2.
    rewrite (tomlistd_gen_to_runBatch t2 unit) in hyp2.
    rewrite (id_to_runBatch t1 unit).
    rewrite (id_to_runBatch t2 unit).

  Qed.


  Lemma shapeliness_tactical : forall A (b1 b2 : @Batch A A (T A)),
      runBatch_monoid (ret list) b1 = runBatch_monoid (ret list) b2 ->
      mapfst_Batch (const tt) b1 = mapfst_Batch (const tt) b2 ->
      runBatch id b1 = runBatch id b2.
  Proof.
    intros. induction b1, b2; cbn in *.
    - now inversion H3.
    - now inversion H2.
    - now inversion H2.
    - specialize (list_app_inv_l2 _ _ _ _ _ H2).
      specialize (list_app_inv_r2 _ _ _ _ _ H2).
      introv hyp1 hyp2. subst.
      erewrite IHb1. eauto. eauto.
      now inversion H3.
  Qed.

End traversal_shapeliness.

(*
(** * Multisorted variation of [Batch] idiom *)
(******************************************************************************)
Section fix_parameters.

  Context
    `{ix : Index}
    {X : Type} {Y : K -> Type}.

  Inductive Batch A : Type :=
  | Go : A -> Batch A
  | Ap : forall k : K, Batch (Y k -> A) -> X -> Batch A.

  Fixpoint fmap_Batch `{f : A -> B} (c : Batch A) : Batch B :=
    match c with
    | Go a => Go (f a)
    | @Ap _ k rest a =>
      Ap (@fmap_Batch (Y k -> A) (Y k -> B) (compose f) rest) a
    end.

  #[global] Instance Fmap_Batch : Fmap Batch := @fmap_Batch.

  #[global, program] Instance Functor_Batch : Functor Batch.

  Next Obligation.
    ext j. induction j. easy.
    cbn; unfold id; now fequal.
  Qed.

  Next Obligation.
    ext j. unfold compose. generalize dependent C.
    generalize dependent B. induction j.
    - easy.
    - intros. cbn. fequal. unfold compose.
      now rewrite  (@IHj (Y k -> B) _ (Y k -> C)).
  Qed.

End fix_parameters.

Arguments Ap {ix} {X}%type_scope {Y}%function_scope [A]%type_scope {k} _ _.

Infix "⧆" := Ap (at level 51, left associativity) : tealeaves_scope.
*)
