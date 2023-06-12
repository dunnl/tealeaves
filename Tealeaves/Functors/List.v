From Tealeaves Require Import
  Classes.Monoid
  Classes.Traversable.Monad
  Functors.Sets
  Definitions.List.

From Coq Require Import
  Sorting.Permutation.

Import List.ListNotations.
Import Monoid.Notations.
Import Sets.Notations.
Import Applicative.Notations.

Create HintDb tea_list.

#[local] Generalizable Variables M A B G ϕ.
#[local] Arguments bindt T {U}%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(** * [list] traversable monad *)
(******************************************************************************)
#[export] Instance Return_list : Return list := fun A a => cons a nil.

Fixpoint bindt_list (G : Type -> Type) `{Map G} `{Pure G} `{Mult G} (A B : Type) (f : A -> G (list B)) (l : list A)
  : G (list B) :=
  match l with
  | nil => pure G (@nil B)
  | x :: xs =>
      pure G (@List.app B) <⋆> (f x) <⋆> (bindt_list G A B f xs)
  end.

#[export] Instance Bindt_list : Bindt list list := @bindt_list.

(** ** Rewriting lemmas for <<bindt>> *)
(******************************************************************************)
Section bindt_rewriting_lemmas.

  Context
    (G : Type -> Type)
      `{Applicative G}
      (A B : Type).

  Lemma bindt_list_nil : forall (f : A -> G (list B)),
      bindt list G A B f (@nil A) = pure G (@nil B).
  Proof.
    reflexivity.
  Qed.

  Lemma bindt_list_one : forall (f : A -> G (list B)) (a : A),
      bindt list G A B f (ret list A a) = f a.
  Proof.
    intros.
    cbn.
    rewrite (ap3).
    rewrite <- (ap4).
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap1.
    unfold compose; do 2 fequal;
      ext l; rewrite (List.app_nil_end).
    reflexivity.
  Qed.

  Lemma bindt_list_cons : forall (f : A -> G (list B)) (a : A) (l : list A),
      bindt list G A B f (cons a l) =
        pure G (@app B) <⋆> f a <⋆> bindt list G A B f l.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma bindt_list_app : forall (f : A -> G (list B)) (l1 l2 : list A),
      bindt list G A B f (l1 ++ l2) =
        pure G (@app B) <⋆> (bindt list G A B f l1) <⋆> (bindt list G A B f l2).
  Proof.
    intros.
    induction l1.
    - cbn. rewrite ap2.
      rewrite ap1.
      reflexivity.
    - cbn.
      rewrite IHl1.
      repeat rewrite <- ap4.
      repeat rewrite (ap2).
      rewrite ap3.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      repeat fequal.
      ext x y z. unfold compose.
      now rewrite (List.app_assoc).
  Qed.

End bindt_rewriting_lemmas.

Section bindt_laws.

  Context
    (G : Type -> Type)
    `{Applicative G}
    (G1 G2 : Type -> Type)
    `{Applicative G1}
    `{Applicative G2}
    (A B C : Type).

  Lemma list_bindt0 : forall (f : A -> G (list B)), bindt list G A B f ∘ ret list A = f.
  Proof.
    intros. ext a.
    apply (bindt_list_one G).
  Qed.

  Lemma list_bindt1 : bindt (U := list) list (fun A => A) A A (ret list A) = id.
  Proof.
    ext l. induction l.
    - reflexivity.
    - cbn. rewrite IHl.
      reflexivity.
  Qed.

  Lemma list_bindt2 :
    forall (g : B -> G2 (list C)) (f : A -> G1 (list B)),
      map G1 (bindt list G2 B C g) ∘ bindt list G1 A B f =
        bindt list (G1 ∘ G2) A C (kc3 list G1 G2 g f).
  Proof.
    intros. ext l. induction l.
    - unfold compose; cbn.
      rewrite (app_pure_natural G1).
      rewrite (bindt_list_nil).
      reflexivity.
    - unfold compose at 1.
      rewrite (bindt_list_cons).
      rewrite map_to_ap.
      do 3 rewrite <- ap4.
      do 4 rewrite (ap2).
      rewrite (bindt_list_cons).
      rewrite <- IHl.
      unfold compose at 7.
      do 2 rewrite (ap_compose1 G2 G1).
      unfold_ops @Pure_compose.
      rewrite map_to_ap.
      rewrite <- ap4.
      rewrite <- ap4.
      rewrite <- ap4.
      rewrite <- ap4.
      repeat rewrite (ap2).
      unfold kc3.
      unfold compose at 8.
      rewrite map_to_ap.
      rewrite <- ap4.
      repeat rewrite ap2.

      rewrite ap3.
      rewrite <- ap4.
      repeat rewrite ap2.
      fequal.
      fequal.
      fequal. ext l1 l2.
      unfold compose. rewrite (bindt_list_app G2).
      reflexivity.
  Qed.

  Lemma list_morph : forall (ϕ : forall A : Type, G1 A -> G2 A)
                       (morph : ApplicativeMorphism G1 G2 ϕ),
      forall (A B : Type) (f : A -> G1 (list B)),
        ϕ (list B) ∘ bindt list G1 A B f = bindt list G2 A B (ϕ (list B) ∘ f).
  Proof.
    intros. unfold compose at 1 2. ext l.
    inversion morph.
    induction l.
    - cbn. rewrite appmor_pure. reflexivity.
    - cbn. do 2 rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHl.
      reflexivity.
  Qed.

End bindt_laws.

  #[export] Instance TM_list : TraversableMonad list :=
  {| ktm_bindt0 := list_bindt0;
    ktm_bindt1 := list_bindt1;
    ktm_bindt2 := list_bindt2;
    ktm_morph := list_morph;
  |}.

#[export] Hint Rewrite bindt_list_nil bindt_list_cons bindt_list_one bindt_list_app :
  tea_list.

#[export] Instance Map_list : Map list := Traversable.Monad.DerivedInstances.Map_Bindt list.
#[export] Instance Bind_list : Bind list list := Traversable.Monad.DerivedInstances.Bind_Bindt list.
#[export] Instance Traverse_list : Traverse list := Traversable.Monad.DerivedInstances.Traverse_Bindt list.
#[export] Instance Functor_list : Functor list := Traversable.Monad.DerivedInstances.Functor_TM list.
#[export] Instance Monad_list : Bind list list := Traversable.Monad.DerivedInstances.Bind_Bindt list.
#[export] Instance TraversableFunctor_list : Traverse list := Traversable.Monad.DerivedInstances.Traverse_Bindt list.

(** ** Rewriting lemmas for <<map>> *)
(******************************************************************************)
Section map_list_rw.

  Context
    {A B : Type}
    (f : A -> B).

  Lemma map_list_nil : map list f (@nil A) = @nil B.
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_cons : forall (x : A) (xs : list A),
      map list f (x :: xs) = f x :: map list f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_one (a : A) : map list f [ a ] = [f a].
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_app : forall (l1 l2 : list A),
      map list f (l1 ++ l2) = map list f l1 ++ map list f l2.
  Proof.
    intros.
    unfold Map_list.
    rewrite (DerivedInstances.map_to_bindt list).
    rewrite (bindt_list_app (fun A => A)).
    reflexivity.
  Qed.

End map_list_rw.

#[export] Hint Rewrite @map_list_nil @map_list_cons
     @map_list_one @map_list_app : tea_list.

Tactic Notation "simpl_list" := (autorewrite with tea_list).
Tactic Notation "simpl_list" "in" hyp(H) := (autorewrite with tea_list H).
Tactic Notation "simpl_list" "in" "*" := (autorewrite with tea_list in *).

(** ** [map] is a monoid homomorphism *)
(******************************************************************************)
#[export, program] Instance Monmor_list_fmap `(f : A -> B) :
  Monoid_Morphism (map list f) := {| monmor_op := map_list_app f; |}.

(** ** Other properties of <<fold>> *)
(******************************************************************************)

Lemma fold_mon_hom : forall `(ϕ : M1 -> M2) `{Monoid_Morphism M1 M2 ϕ},
    ϕ ∘ fold M1 = fold M2 ∘ map list ϕ.
Proof.
  intros ? ? ϕ ? ? ? ? ?. unfold compose. ext l.
  induction l as [| ? ? IHl].
  - cbn. apply (monmor_unit ϕ).
  - cbn. now rewrite (monmor_op ϕ), IHl.
Qed.

(*
(** * [list] is set-like *)
(** A [list] can be reduced to a [set] by discarding the ordering, or more
    concretely by applying [List.In]. This makes [list] into a quantifiable
    monad. The lemmas involved in proving this fact form a key step in proving
    that all listables are quantifiable, below. *)
(******************************************************************************)
#[export] Instance Toset_list : Toset list :=
  fun _ l a => List.In a l.

(** ** Rewriting lemmas for <<toset>>\<<∈>>*)
(******************************************************************************)
Lemma toset_list_nil : forall A, toset list (@nil A) = ∅.
Proof.
  reflexivity.
Qed.

Lemma toset_list_cons : forall A (x : A) (xs : list A),
    toset list (x :: xs) = ret set x ∪ toset list xs.
Proof.
  reflexivity.
Qed.

Lemma toset_list_one : forall A (a : A), toset list [ a ] = ret set a.
Proof.
  intros. ext b; propext; cbv; intuition.
Qed.

Lemma toset_list_ret : forall A (a : A), toset list (ret list a) = ret set a.
Proof.
  intros. ext b; propext; cbv; intuition.
Qed.

Lemma toset_list_app : forall A (l1 l2 : list A),
    toset list (l1 ++ l2) = toset list l1 ∪ toset list l2.
Proof.
  intros. ext b. change (toset list ?l b) with (List.In b l).
  propext; rewrite -> List.in_app_iff; auto.
Qed.

#[export] Hint Rewrite toset_list_nil toset_list_cons
     toset_list_one toset_list_ret toset_list_app : tea_list.

Lemma in_list_nil {A} : forall (p : A), p ∈ @nil A <-> False.
Proof.
  reflexivity.
Qed.

Lemma in_list_cons {A} : forall (a1 a2 : A) (xs : list A),
    a1 ∈ (a2 :: xs) <-> a1 = a2 \/ a1 ∈ xs.
Proof.
  intros; simpl_list. unfold_set. intuition congruence.
Qed.

Lemma in_list_one {A} (a1 a2 : A) : a1 ∈ [ a2 ] <-> a1 = a2.
Proof.
  intros. simpl_list. simpl_set. intuition congruence.
Qed.

Lemma in_list_ret {A} (a1 a2 : A) : a1 ∈ ret list a2 <-> a1 = a2.
Proof.
  intros. simpl_list. intuition.
Qed.

Lemma in_list_app {A} : forall (a : A) (xs ys : list A),
    a ∈ (xs ++ ys) <-> a ∈ xs \/ a ∈ ys.
Proof.
  intros. simpl_list. simpl_set. reflexivity.
Qed.

#[export] Hint Rewrite @in_list_nil @in_list_cons
     @in_list_one @in_list_ret @in_list_app : tea_list.

Theorem perm_set_eq : forall {A} {l1 l2 : list A},
    Permutation l1 l2 -> (forall a, a ∈ l1 <-> a ∈ l2).
Proof.
  introv perm. induction perm; firstorder.
Qed.

(** ** [toset] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_toset_list (A : Type) : Monoid_Morphism (toset list (A := A)) :=
  {| monmor_unit := @toset_list_nil A;
     monmor_op := @toset_list_app A;
  |}.

(** ** Respectfulness conditions *)
(******************************************************************************)
#[export] Instance Natural_toset_list: Natural (@toset list _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold compose. ext l. induction l.
  - simpl_list; simpl_set. trivial.
  - simpl_list; simpl_set. now rewrite IHl.
Qed.

Theorem map_rigidly_respectful_list : forall A B (f g : A -> B) (l : list A),
    (forall (a : A), a ∈ l -> f a = g a) <-> map list f l = map list g l.
Proof.
  intros. induction l.
  - simpl_list. setoid_rewrite set_in_empty. tauto.
  - simpl_list. setoid_rewrite set_in_add.
    setoid_rewrite set_in_ret.
    destruct IHl. split.
    + intro; fequal; auto.
    + injection 1; intuition (subst; auto).
Qed.

Corollary map_respectful_list : forall A B (l : list A) (f g : A -> B),
    (forall (a : A), a ∈ l -> f a = g a) -> map list f l = map list g l.
Proof.
  intros. now rewrite <- map_rigidly_respectful_list.
Qed.

#[export] Instance SetlikeFunctor_list : SetlikeFunctor list :=
  {| xfun_respectful := map_respectful_list; |}.

(** ** Set-like monad instance *)
(******************************************************************************)
Theorem toset_ret_list :
  `(toset list ∘ ret list (A:=A) = ret set).
Proof.
  intros. unfold compose. ext a.
  now simpl_list.
Qed.

Theorem toset_join_list :
  `(toset (A:=A) list ∘ join list = join set ∘ toset list ∘ map list (toset list)).
Proof.
  intros. unfold compose. ext l. induction l.
  - simpl_list; simpl_set; trivial.
  - simpl_list. simpl_set. rewrite IHl. trivial.
Qed.

Theorem return_injective_list : forall A (a b : A),
    [a] = [b] -> a = b.
Proof.
  introv hyp. now inverts hyp.
Qed.

#[export] Instance SetlikeMonad_list : SetlikeMonad list :=
  {| xmon_ret := toset_ret_list;
     xmon_join := toset_join_list;
     xmon_ret_injective := return_injective_list;
  |}.

(** ** Monoids form list (monad-)algebras *)
(** In fact, list algebras are precisely monoids. *)
(******************************************************************************)
Section foldable_list.

  Context
    `{Monoid M}.

  Lemma fold_ret : forall (x : M),
      fold (ret list x : list M) = x.
  Proof.
    apply monoid_id_l.
  Qed.

  Lemma fold_join : forall (l : list (list M)),
      fold (join list l) = fold (map list fold l).
  Proof.
    intro l. rewrite <- fold_equal_join.
    compose near l on left.
    now rewrite (fold_mon_hom fold).
  Qed.

  Lemma fold_constant_unit : forall (l : list M),
      fold (map list (fun _ => Ƶ) l) = Ƶ.
  Proof.
    intro l. induction l.
    - reflexivity.
    - cbn. now simpl_monoid.
  Qed.

End foldable_list.
*)

(** * <<map>> equality inversion lemmas *)
(** Some lemmas for reasoning backwards from equality between two
    similarly-concatenated lists.  *)
(******************************************************************************)
Lemma map_app_inv_l : forall {A B} {f g : A -> B} (l1 l2 : list A),
    map list f (l1 ++ l2) = map list g (l1 ++ l2) ->
    map list f l1 = map list g l1.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl_list in *. rewrite IHl1.
    + fequal. simpl in H. inversion H; auto.
    + simpl in H. inversion H. auto.
Qed.

Lemma map_app_inv_r : forall {A B} {f g : A -> B} (l1 l2 : list A),
    map list f (l1 ++ l2) = map list g (l1 ++ l2) ->
    map list f l2 = map list g l2.
Proof.
  intros.
  assert (heads_equal : map list f l1 = map list g l1).
  { eauto using map_app_inv_l. }
  simpl_list in *.
  rewrite heads_equal in H.
  eauto using List.app_inv_head.
Qed.

Lemma map_app_inv : forall {A B} {f g : A -> B} (l1 l2 : list A),
    map list f (l1 ++ l2) = map list g (l1 ++ l2) ->
    map list f l1 = map list g l1 /\ map list f l2 = map list g l2.
Proof.
  intros; split; eauto using map_app_inv_l, map_app_inv_r.
Qed.
