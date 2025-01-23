From Tealeaves Require Import
  Classes.Categorical.Monad
  Classes.Coalgebraic.TraversableFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor
  Classes.Kleisli.Monad
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.TraversableMonad
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor.

From Tealeaves Require Export
  Functors.Early.List
  Functors.Subset.

Import ContainerFunctor.Notations.
Import TraversableMonad.Notations.
Import List.ListNotations.
Import Monoid.Notations.
Import Subset.Notations.
Import Applicative.Notations.
Export EqNotations.

#[local] Generalizable Variables M A B G ϕ.

(** * <<toBatch>> Instance *)
(******************************************************************************)
#[export] Instance ToBatch_list: ToBatch list :=
  DerivedOperations.ToBatch_Traverse.

(** * List algebras and folds *)
(******************************************************************************)

(** ** Some homomorphisms *)
(******************************************************************************)


(** * <<map>> equality inversion lemmas *)
(** Some lemmas for reasoning backwards from equality between two
    similarly-concatenated lists.  *)
(******************************************************************************)
Lemma map_app_inv_l: forall {A B} {f g: A -> B} (l1 l2: list A),
    map f (l1 ++ l2) = map g (l1 ++ l2) ->
    map f l1 = map g l1.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl_list in *. rewrite IHl1.
    + fequal. simpl in H. inversion H; auto.
    + simpl in H. inversion H. auto.
Qed.

Lemma map_app_inv_r: forall {A B} {f g: A -> B} (l1 l2: list A),
    map f (l1 ++ l2) = map g (l1 ++ l2) ->
    map f l2 = map g l2.
Proof.
  intros.
  assert (heads_equal: map f l1 = map g l1).
  { eauto using map_app_inv_l. }
  simpl_list in *.
  rewrite heads_equal in H.
  eauto using List.app_inv_head.
Qed.

Lemma map_app_inv: forall {A B} {f g: A -> B} (l1 l2: list A),
    map f (l1 ++ l2) = map g (l1 ++ l2) ->
    map f l1 = map g l1 /\ map f l2 = map g l2.
Proof.
  intros; split; eauto using map_app_inv_l, map_app_inv_r.
Qed.

#[local] Generalizable Variable F.

(** * Shapely instance for [list] *)
(** As a reasonability check, we prove that [list] is a listable functor. *)
(******************************************************************************)
Section ShapelyFunctor_list.

  Instance Tolist_list: Tolist list := fun A l => l.

  Instance: Natural (@tolist list _).
  Proof.
    constructor; try typeclasses eauto.
    reflexivity.
  Qed.

  Theorem shapeliness_list: shapeliness list.
  Proof.
    intros A t1 t2. intuition.
  Qed.

  Instance: ShapelyFunctor list :=
    {| shp_shapeliness := shapeliness_list; |}.

End ShapelyFunctor_list.

(** ** Rewriting [shape] on lists *)
(******************************************************************************)
Section list_shape_rewrite.

  Lemma shape_nil: forall A,
      shape (@nil A) = @nil unit.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_cons: forall A (a: A) (l: list A),
      shape (a :: l) = tt :: shape l.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_one: forall A (a: A),
      shape [ a ] = [ tt ].
  Proof.
    reflexivity.
  Qed.

  Lemma shape_app: forall A (l1 l2: list A),
      shape (l1 ++ l2) = shape l1 ++ shape l2.
  Proof.
    intros. unfold shape. now rewrite map_list_app.
  Qed.

  Lemma shape_nil_iff: forall A (l: list A),
      shape l = @nil unit <-> l = [].
  Proof.
    induction l. intuition.
    split; intro contra; now inverts contra.
  Qed.

End list_shape_rewrite.

#[export] Hint Rewrite @shape_nil @shape_cons @shape_one @shape_app: tea_list.

(** ** Reasoning princples for <<shape>> on lists *)
(******************************************************************************)
Section list_shape_lemmas.

  Theorem list_shape_equal_iff: forall (A: Type) (l1 l2: list A),
      shape l1 = shape l2 <->
        List.length l1 = List.length l2.
  Proof.
    intros. generalize dependent l2.
    induction l1.
    - destruct l2.
      + split; reflexivity.
      + split; inversion 1.
    - cbn. intro l2; destruct l2.
      + cbn. split; inversion 1.
      + cbn. split; inversion 1.
        * fequal. apply IHl1. auto.
        * fequal. apply IHl1. auto.
  Qed.

  Theorem shape_eq_app_r: forall A (l1 l2 r1 r2: list A),
      shape r1 = shape r2 ->
      (shape (l1 ++ r1) = shape (l2 ++ r2) <->
       shape l1 = shape l2).
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split. intros; eauto using List.app_inv_tail.
    intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_eq_app_l: forall A (l1 l2 r1 r2: list A),
      shape l1 = shape l2 ->
      (shape (l1 ++ r1) = shape (l2 ++ r2) <->
       shape r1 = shape r2).
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split. intros; eauto using List.app_inv_head.
    intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_eq_cons_iff: forall A (l1 l2: list A) (x y: A),
      shape (x :: l1) = shape (y :: l2) <->
      shape l1 = shape l2.
  Proof.
    intros. rewrite 2(shape_cons).
    split; intros hyp. now inverts hyp.
    now rewrite hyp.
  Qed.

  Theorem inv_app_eq_ll: forall A (l1 l2 r1 r2: list A),
      shape l1 = shape l2 ->
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

  Theorem inv_app_eq_rl: forall A (l1 l2 r1 r2: list A),
      shape r1 = shape r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| ? ? IHl1 ];
                induction l2 as [| ? ? IHl2 ].
    - reflexivity.
    - introv shape_eq heq. apply inv_app_eq_ll with (r1 := r1) (r2 := r2).
      + rewrite <- shape_eq_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq. apply inv_app_eq_ll with (r1 := r1) (r2 := r2).
      + rewrite <- shape_eq_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq.
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem inv_app_eq_lr: forall A (l1 l2 r1 r2: list A),
      shape l1 = shape l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eauto using List.app_inv_head. }
    { eauto using inv_app_eq_ll. }
  Qed.

  Theorem inv_app_eq_rr: forall A (l1 l2 r1 r2: list A),
      shape r1 = shape r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eauto using List.app_inv_head. }
    { eauto using inv_app_eq_rl. }
  Qed.

  Theorem inv_app_eq: forall A (l1 l2 r1 r2: list A),
      shape l1 = shape l2 \/ shape r1 = shape r2 ->
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

  Lemma list_app_inv_r: forall A (l l1 l2: list A),
      l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    introv hyp. induction l.
    - cbn in hyp. auto.
    - inversion hyp. auto.
  Qed.

  Lemma list_app_inv_l: forall A (l l1 l2: list A),
      l1 ++ l = l2 ++ l -> l1 = l2.
  Proof.
    introv hyp. eapply inv_app_eq_rl.
    2: eauto. reflexivity.
  Qed.

  Lemma list_app_inv_l2: forall A (l1 l2: list A) (a1 a2: A),
      l1 ++ ret a1 = l2 ++ ret a2 ->
      l1 = l2.
  Proof.
    intros. eapply inv_app_eq_rl; [|eauto]; auto.
  Qed.

  Lemma list_app_inv_r2: forall A (l1 l2: list A) (a1 a2: A),
      l1 ++ [a1] = l2 ++ [a2] ->
      a1 = a2.
  Proof.
    introv. introv hyp.
    apply inv_app_eq_rr in hyp.
    now inversion hyp. easy.
  Qed.

End list_shape_lemmas.

(** * Reasoning principles for <<shape>> on listable functors *)
(******************************************************************************)
Section listable_shape_lemmas.

  Context
    `{Functor F}
    `{Tolist F}
    `{! Natural (@tolist F _)}.

  (* Values with the same shape have equal-length contents *)
  Lemma shape_tolist: forall `(t: F A) `(u: F B),
      shape t = shape u ->
      shape (tolist t) = shape (tolist u).
  Proof.
    introv heq. compose near t. compose near u.
    unfold shape in *. rewrite 2(natural).
    unfold compose.
    fequal. apply heq.
  Qed.

  Corollary shape_l: forall A (l1 l2: F A) (x y: list A),
      shape l1 = shape l2 ->
      (tolist l1 ++ x = tolist l2 ++ y) ->
      tolist l1 = tolist l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_ll, shape_tolist.
  Qed.

  Corollary shape_r: forall A (l1 l2: F A) (x y: list A),
      shape l1 = shape l2 ->
      (x ++ tolist l1 = y ++ tolist l2) ->
      tolist l1 = tolist l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_rr, shape_tolist.
  Qed.

End listable_shape_lemmas.

(** * Quantification over elements *)
(* TODO: There is no real purpose for this at this point is there? *)
(******************************************************************************)
Section quantification.

  Definition Forall_List `(P: A -> Prop): list A -> Prop :=
    foldMap_list (op := Monoid_op_and) (unit := Monoid_unit_true) P.

  Definition Forany_List `(P: A -> Prop): list A -> Prop :=
    foldMap_list (op := Monoid_op_or) (unit := Monoid_unit_false) P.

  Lemma forall_iff `(P: A -> Prop) (l: list A) :
    Forall_List P l <-> forall (a: A), a ∈ l -> P a.
  Proof.
    unfold Forall_List.
    induction l; autorewrite with tea_list tea_set.
    - split.
      + intros tt a contra. inversion contra.
      + intros. exact I.
    - setoid_rewrite element_of_list_cons.
      rewrite IHl. split.
      + intros [Hpa Hrest].
        intros x [Heq | Hin].
        now subst. auto.
      + intros H. split; auto.
  Qed.

  Lemma forany_iff `(P: A -> Prop) (l: list A) :
    Forany_List P l <-> exists (a: A), a ∈ l /\ P a.
  Proof.
    unfold Forany_List.
    induction l.
    - split.
      + intros [].
      + intros [x [contra Hrest]]. inversion contra.
    - autorewrite with tea_list tea_set.
      setoid_rewrite element_of_list_cons.
      unfold subset_one.
      rewrite IHl. split.
      + intros [Hpa | Hrest].
        exists a. auto.
        destruct Hrest as [x [H1 H2]].
        exists x. auto.
      + intros [x [[H1 | H2] H3]].
        subst. now left.
        right. eexists; eauto.
  Qed.

End quantification.

(** ** <<Element>> in terms of <<foldMap_list>> *)
(******************************************************************************)
Lemma element_to_foldMap_list1: forall (A: Type),
    tosubset = foldMap_list (ret (T := subset) (A := A)).
Proof.
  intros. ext l. induction l.
  - reflexivity.
  - cbn. autorewrite with tea_list.
    rewrite IHl.
    reflexivity.
Qed.

Lemma element_to_foldMap_list2: forall (A: Type) (l: list A) (a: A),
    tosubset l a = foldMap_list (op := or) (unit := False) (eq a) l.
Proof.
  intros. rewrite element_to_foldMap_list1.
  (*
    change_left ((evalAt a ∘ foldMap_list (ret (T := subset))) l).
   *)
  induction l.
  - reflexivity.
  - rewrite foldMap_list_cons.
    rewrite foldMap_list_cons.
    rewrite <- IHl.
    replace (a = a0) with (a0 = a) by (propext; auto).
    reflexivity.
Qed.

(** * Specification of <<Permutation>> *)
(******************************************************************************)
From Coq Require Import Sorting.Permutation.

Theorem permutation_spec: forall {A} {l1 l2: list A},
    Permutation l1 l2 -> (forall a, a ∈ l1 <-> a ∈ l2).
Proof.
  introv perm. induction perm; firstorder.
Qed.


(** * SameSet *)

Inductive SameSetRight {A: Type}: list A -> list A -> Prop :=
| ssetr_nil: SameSetRight [] []
| ssetr_skip: forall (x: A) (l l': list A), SameSetRight l l' -> SameSetRight (x :: l) (x :: l')
| ssetr_swap: forall (x y: A) (l: list A), SameSetRight (y :: x :: l) (x :: y :: l)
| ssetr_dup_r: forall (x: A) (l: list A), SameSetRight (x :: l) (x :: x :: l)
| ssetr_trans: forall l l' l'': list A, SameSetRight l l' -> SameSetRight l' l'' -> SameSetRight l l''.


Inductive SameSet {A: Type}: list A -> list A -> Prop :=
| sset_nil: SameSet [] []
| sset_skip: forall (x: A) (l l': list A), SameSet l l' -> SameSet (x :: l) (x :: l')
| sset_swap: forall (x y: A) (l: list A), SameSet (y :: x :: l) (x :: y :: l)
| sset_dup_r: forall (x: A) (l: list A), SameSet (x :: l) (x :: x :: l)
| sset_dup_l: forall (x: A) (l: list A), SameSet (x :: x :: l) (x :: l)
| sset_trans: forall l l' l'': list A, SameSet l l' -> SameSet l' l'' -> SameSet l l''.

From Tealeaves Require Import Classes.EqDec_eq.

Lemma sameset_refl: forall (A: Type) (l: list A),
    SameSet l l.
Proof.
  intros. induction l.
  - apply sset_nil.
  - apply sset_skip.
    assumption.
Qed.

Lemma sameset_nil: forall (A: Type) (l: list A),
    SameSet [] l -> l = [].
Proof.
  intros. remember [] as l'.
  induction H; subst; try solve [inversion Heql'].
  - reflexivity.
  - specialize (IHSameSet1 ltac:(reflexivity)).
    subst. auto.
Qed.

Lemma sametset_dup_right: forall (A: Type) (a: A) (l: list A),
    SameSet (a :: l) (a :: a :: l).
Proof.
  intros. apply sset_dup_r.
Qed.

Example ex1: forall (A: Type) (a: A),
    SameSet [a; a] [a].
Proof.
  intros. apply sset_dup_l.
Qed.

Lemma sameset_sym: forall (A: Type) (l l': list A),
    SameSet l l' -> SameSet l' l.
Proof.
  intros. induction H.
  - apply sset_nil.
  - apply sset_skip. auto.
  - apply sset_swap.
  - apply sset_dup_l.
  - apply sset_dup_r.
  - eapply sset_trans; eauto.
Qed.

(*
Lemma sameset_spec_one: forall (A: Type) `{EqDec_eq A} (l: list A) (a: A),
  (forall (a0: A), a0 ∈ l <-> a0 = a) -> SameSet [a] l.
Proof.
  introv Heq Hsame. induction l.
  - specialize (Hsame a).
    autorewrite with tea_list in Hsame. tauto.
  - assert (a0 = a).
    { apply (Hsame a0). now left. }
    subst; clear Hsame.
    destruct l.
    + apply sameset_refl.
    + destruct_eq_args a a0.
      * admit.
      * admit.
Abort.

Theorem sameset_spec: forall {A} `{EqDec_eq A} {l1 l2: list A},
    (forall a, a ∈ l1 <-> a ∈ l2) -> SameSet l1 l2.
Proof.
  introv Heqdec Hsame.
  assert (Hsame1: forall a: A, a ∈ l1 -> a ∈ l2).
  { intro a. apply Hsame. }
  assert (Hsame2: forall a: A, a ∈ l2 -> a ∈ l1).
  { intro a. apply Hsame. }
  clear Hsame.
  generalize dependent l2.
  induction l1; intros l2 Hsame1 Hsame2.
  - induction l2.
    + apply sset_nil.
    + false.
      apply (Hsame2 a).
      now left.
  - destruct l1.
    + clear IHl1.
Abort.

TODO Cleanup
 *)

(** * Misc *)
(******************************************************************************)
Lemma map_preserve_length:
  forall (A B: Type) (f: A -> B) (l: list A),
    length (map f l) = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - cbn.
    rewrite <- IHl.
    reflexivity.
Qed.

Definition decide_length {A}: forall (n: nat) (l: list A),
    {length l = n} + { length l = n -> False}.
Proof.
  intros.
  remember (Nat.eqb (length l) n) as b.
  symmetry in Heqb.
  destruct b.
  - left.
    apply (PeanoNat.Nat.eqb_eq (length l) n).
    assumption.
  - right.
    apply (PeanoNat.Nat.eqb_neq (length l) n).
    assumption.
Defined.

(** * Un-con-sing non-empty lists *)
(******************************************************************************)
Lemma S_uncons {n m}: S n = S m -> n = m.
Proof.
  now inversion 1.
Defined.

Definition zero_not_S {n} {anything}:
  0 = S n -> anything :=
  fun pf => match pf with
         | eq_refl =>
             let false: False :=
               eq_ind 0 (fun e: nat => match e with
                           | 0 => True
                           | S _ => False
                           end) I (S n) pf
             in (False_rect anything false)
         end.

Lemma list_uncons_exists:
  forall (A: Type) (n: nat)
    (v: list A) (vlen: length v = S n),
    exists (a: A) (v': list A),
    v = cons a v'.
Proof.
  intros.
  destruct v.
  - inversion vlen.
  - exists a v. reflexivity.
Qed.

Definition list_uncons {n A} (l: list A) (vlen: length l = S n):
  A * list A :=
  match l return (length l = S n -> A * list A) with
  | nil => zero_not_S
  | cons a rest => fun vlen => (a, rest)
  end vlen.

Definition list_uncons_sigma {n A} (l: list A) (vlen: length l = S n):
  A * {l: list A | length l = n} :=
  match l return (length l = S n -> A * {l: list A | length l = n}) with
  | nil => zero_not_S
  | cons hd tl => fun vlen => (hd, exist _ tl (S_uncons vlen))
  end vlen.

Definition list_uncons_sigma2 {n A} (l: list A) (vlen: length l = S n):
  {p: A * list A | l = uncurry cons p} :=
  match l return (length l = S n -> {p: A * list A | l = uncurry cons p}) with
  | nil => zero_not_S
  | cons hd tl => fun vlen => exist _ (hd, tl) eq_refl
  end vlen.

(** ** Total list head and tail functions for non-empty lists *)
(******************************************************************************)
Definition list_hd {n A} :=
  fun (l: list A) (vlen: length l = S n) =>
  fst (list_uncons l vlen).

Definition list_tl {n A} :=
  fun (l: list A) (vlen: length l = S n) =>
    snd (list_uncons l vlen).

(** *** Proof independence and rewriting laws *)
(******************************************************************************)
Lemma list_hd_proof_irrelevance
        {n m A}
        (l: list A)
        (vlen1: length l = S n)
        (vlen2: length l = S m):
  list_hd l vlen1 = list_hd l vlen2.
Proof.
  induction l.
  - inversion vlen1.
  - reflexivity.
Qed.

Lemma list_tl_proof_irrelevance
        {n m A}
        (l: list A)
        (vlen1: length l = S n)
        (vlen2: length l = S m):
  list_tl l vlen1 = list_tl l vlen2.
Proof.
  induction l.
  - inversion vlen1.
  - reflexivity.
Qed.

(** Rewrite a [list_hd] subterm by pushing a type coercion into the
    length proof *)
Lemma list_hd_rw
        {n A}
        {l1 l2: list A}
        (Heq: l1 = l2)
        {vlen: length l1 = S n}:
  list_hd l1 vlen = list_hd l2 (rew [fun l1 => length l1 = S n] Heq in vlen).
Proof.
  subst.
  apply list_hd_proof_irrelevance.
Qed.

(** Rewrite a [list_tl] subterm by pushing a type coercion into the
    length proof *)
Lemma list_tl_rw
        {n A}
        {l1 l2: list A}
        (Heq: l1 = l2)
        {vlen: length l1 = S n}:
  list_tl l1 vlen = list_tl l2 (rew [fun l1 => length l1 = S n] Heq in vlen).
Proof.
  subst.
  apply list_tl_proof_irrelevance.
Qed.

Lemma list_tl_length {n} `(l: list A) (vlen: length l = S n):
  length (list_tl l vlen) = n.
Proof.
  destruct l.
  - inversion vlen.
  - cbn. now inversion vlen.
Qed.

(** *** Surjective pairing properties *)
(******************************************************************************)
Lemma list_surjective_pairing {n} `(l: list A) `(vlen: length l = S n):
  list_uncons l vlen = (list_hd l vlen, list_tl l vlen).
Proof.
  destruct l.
  - inversion vlen.
  - reflexivity.
Qed.

Lemma list_surjective_pairing2 {n} `(l: list A) `(vlen: length l = S n):
  l = cons (list_hd l vlen) (list_tl l vlen).
Proof.
  destruct l.
  - inversion vlen.
  - reflexivity.
Qed.

(** * Filtering lists *)
(******************************************************************************)
Fixpoint filter `(P: A -> bool) (l: list A): list A :=
  match l with
  | nil => nil
  | cons a rest =>
    if P a then a :: filter P rest else filter P rest
  end.

(** ** Rewriting lemmas for [filter] *)
(******************************************************************************)
Section filter_lemmas.

  Context
    `(P: A -> bool).

  Lemma filter_nil :
    filter P nil = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_cons: forall (a: A) (l: list A),
      filter P (a :: l) = if P a then a :: filter P l else filter P l.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_one: forall (a: A),
      filter P [a] = if P a then [a] else nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_app: forall (l1 l2: list A),
      filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
  Proof.
    intros. induction l1.
    - reflexivity.
    - cbn. rewrite IHl1. now destruct (P a).
  Qed.

End filter_lemmas.

#[export] Hint Rewrite @filter_nil @filter_cons @filter_app @filter_one: tea_list.
