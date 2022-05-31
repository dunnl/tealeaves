From Tealeaves Require Import
     Classes.Monoid
     Functors.Sets
     Classes.SetlikeModule.

From Coq Require Import
     Sorting.Permutation.

Import List.ListNotations.
#[local] Open Scope list_scope.

Import Monoid.Notations.
Import Sets.Notations.
Import SetlikeFunctor.Notations.
#[local] Open Scope tealeaves_scope.

Create HintDb tea_list.

(** * [list] monoid *)
(******************************************************************************)
Instance Monoid_op_app {A} : Monoid_op (list A) := @app A.

Instance Monoid_op_nil {A} : Monoid_unit (list A) := nil.

#[program] Instance Monoid_list {A} :
  @Monoid (list A) (@Monoid_op_app A) (@Monoid_op_nil A).

Solve Obligations with (intros; unfold transparent tcs; auto with datatypes).

(** * [list] functor *)
(******************************************************************************)
Instance Fmap_list : Fmap list :=
  fun A B f => List.map f.

(** ** Rewriting lemmas for <<fmap>> *)
(******************************************************************************)
Section fmap_list_rw.

  Context
    {A B : Type}
    (f : A -> B).

  Lemma fmap_list_nil : fmap list f (@nil A) = @nil B.
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_list_cons : forall (x : A) (xs : list A),
      fmap list f (x :: xs) = f x :: fmap list f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_list_one (a : A) : fmap list f [ a ] = [f a].
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_list_app : forall (l1 l2 : list A),
      fmap list f (l1 ++ l2) = fmap list f l1 ++ fmap list f l2.
  Proof.
    unfold transparent tcs. now rewrites List.map_app.
  Qed.

End fmap_list_rw.

Hint Rewrite @fmap_list_nil @fmap_list_cons
     @fmap_list_one @fmap_list_app : tea_list.

Tactic Notation "simpl_list" := (autorewrite with tea_list).
Tactic Notation "simpl_list" "in" hyp(H) := (autorewrite with tea_list H).
Tactic Notation "simpl_list" "in" "*" := (autorewrite with tea_list in *).

(** ** [fmap] is a monoid homomorphism *)
(******************************************************************************)
#[program] Instance Monmor_list_fmap `(f : A -> B) :
  Monoid_Morphism (fmap list f) :=
  {| monmor_op := fmap_list_app f; |}.

(** ** Functor instance *)
(******************************************************************************)
Theorem fmap_id_list {A} : fmap list (@id A) = id.
Proof.
  ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

Theorem fmap_fmap_list {A B C} : forall (f : A -> B) (g : B -> C),
    fmap list g ∘ fmap list f = fmap list (g ∘ f).
Proof.
  intros. unfold compose. ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

Instance Functor_list : Functor list :=
  {| fun_fmap_id := @fmap_id_list;
     fun_fmap_fmap := @fmap_fmap_list;
  |}.

(** * [list] monad *)
(******************************************************************************)
Instance Return_list : Return list := fun A a => cons a nil.

Instance Join_list : Join list := @List.concat.

(** ** Rewriting lemmas for <<join>> *)
(******************************************************************************)
Lemma join_list_nil :
  `(join list ([ ] : list (list A)) = []).
Proof.
  reflexivity.
Qed.

Lemma join_list_cons : forall A (l : list A) (ll : list (list A)),
    join list (l :: ll) = l ++ join list ll.
Proof.
  reflexivity.
Qed.

Lemma join_list_one : forall A (l : list A),
    join list [ l ] = l.
Proof.
  intros. cbn. now List.simpl_list.
Qed.

Lemma join_list_app : forall A (l1 l2 : list (list A)),
    join list (l1 ++ l2) = join list l1 ++ join list l2.
Proof.
  apply List.concat_app.
Qed.

Hint Rewrite join_list_nil join_list_cons join_list_one join_list_app :
  tea_list.

(** ** [join] is a monoid homomorphism *)
(** The <<join>> operation is a monoid homomorphism from <<list (list A)>> to
    <<list A>>. This is just a special case of the fact that monoid homomorphisms
    on free monoids are precisely of the form <<foldMap f>> for any <<f : A -> M>>,
    specialized to <<f = id>> case, but we don't need that much generality. *)
(******************************************************************************)
Instance Monmor_join (A : Type) : Monoid_Morphism (join list (A := A)) :=
  {| monmor_unit := @join_list_nil A;
     monmor_op := @join_list_app A;
  |}.

(** ** Monad instance *)
(******************************************************************************)
Instance Natural_ret_list : Natural (@ret list _).
Proof.
  constructor; try typeclasses eauto.
  introv. now ext l.
Qed.

Instance Natural_join_list : Natural (@join list _).
Proof.
  constructor; try typeclasses eauto.
  intros ? ? f. ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

Theorem join_ret_list {A} :
  join list ∘ ret list = @id (list A).
Proof.
  ext l. unfold compose. destruct l.
  - reflexivity.
  - cbn. now List.simpl_list.
Qed.

Theorem join_fmap_ret_list {A} :
  join list ∘ fmap list (ret list) = @id (list A).
Proof.
  ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

Theorem join_join_list {A} :
  join list ∘ join list (A:=list A) =
  join list ∘ fmap list (join list).
Proof.
  ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

Instance Monad_list : Monad list :=
  {| mon_join_ret := @join_ret_list;
     mon_join_fmap_ret := @join_fmap_ret_list;
     mon_join_join := @join_join_list;
  |}.

(** ** [list]/[list] right module *)
(******************************************************************************)
(*
Instance RightAction_list : RightAction list list := RightAction_Join list.

Instance RightModule_list : RightModule list list := RightModule_Monad list.
*)

(** ** Rewriting lemmas for <<bind>> *)
(******************************************************************************)
Section bind_rewriting_lemmas.

  Context
    (A B : Type)
    (f : A -> list B).

  Lemma bind_list_nil : bind list f [] = [].
  Proof.
    reflexivity.
  Qed.

  Lemma bind_list_one : forall x, bind list f [ x ] = f x.
  Proof.
    unfold_ops @Bind_Join.
    unfold compose. intros. now autorewrite with tea_list.
  Qed.

  Lemma bind_list_cons : forall (x : A) (xs : list A),
      bind list f (x :: xs) = f x ++ bind list f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_list_app : forall (l1 l2 : list A),
      bind list f (l1 ++ l2) = bind list f l1 ++ bind list f l2.
  Proof.
    unfold_ops @Bind_Join.
    unfold compose. intros. now autorewrite with tea_list.
  Qed.

End bind_rewriting_lemmas.

Hint Rewrite bind_list_nil bind_list_one bind_list_cons bind_list_app :
  tea_list.

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
Instance Monmor_bind {A B f} : Monoid_Morphism (bind list f) :=
  {| monmor_unit := bind_list_nil A B f;
     monmor_op := bind_list_app A B f;
  |}.

(** * [list] is set-like *)
(** A [list] can be reduced to a [set] by discarding the ordering, or more
    concretely by applying [List.In]. This makes [list] into a quantifiable
    monad. The lemmas involved in proving this fact form a key step in proving
    that all listables are quantifiable, below. *)
(******************************************************************************)
Instance Toset_list : Toset list :=
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

Hint Rewrite toset_list_nil toset_list_cons
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

Hint Rewrite @in_list_nil @in_list_cons
     @in_list_one @in_list_ret @in_list_app : tea_list.

Theorem perm_set_eq : forall {A} {l1 l2 : list A},
    Permutation l1 l2 -> (forall a, a ∈ l1 <-> a ∈ l2).
Proof.
  introv perm. induction perm; firstorder.
Qed.

(** ** Respectfulness conditions *)
(******************************************************************************)
Instance Natural_toset_list: Natural (@toset list _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold compose. ext l. induction l.
  - simpl_list; simpl_set. trivial.
  - simpl_list; simpl_set. now rewrite IHl.
Qed.

Theorem fmap_rigidly_respectful_list : forall A B (f g : A -> B) (l : list A),
    (forall (a : A), a ∈ l -> f a = g a) <-> fmap list f l = fmap list g l.
Proof.
  intros. induction l.
  - simpl_list. setoid_rewrite set_in_empty. tauto.
  - simpl_list. setoid_rewrite set_in_add.
    setoid_rewrite set_in_ret.
    destruct IHl. split.
    + intro; fequal; auto.
    + injection 1; intuition (subst; auto).
Qed.

Corollary fmap_respectful_list : forall A B (l : list A) (f g : A -> B),
    (forall (a : A), a ∈ l -> f a = g a) -> fmap list f l = fmap list g l.
Proof.
  intros. now rewrite <- fmap_rigidly_respectful_list.
Qed.

Instance SetlikeFunctor_list : SetlikeFunctor list :=
  {| xfun_respectful := fmap_respectful_list; |}.

(** ** Set-like monad instance *)
(******************************************************************************)
Theorem toset_ret_list :
  `(toset list ∘ ret list (A:=A) = ret set).
Proof.
  intros. unfold compose. ext a.
  now simpl_list.
Qed.

Theorem toset_join_list :
  `(toset (A:=A) list ∘ join list = join set ∘ toset list ∘ fmap list (toset list)).
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

Instance SetlikeMonad_list : SetlikeMonad list :=
  {| xmon_ret := toset_ret_list;
     xmon_join := toset_join_list;
     xmon_ret_injective := return_injective_list;
  |}.

(*
Instance SetlikeModule_list : SetlikeModule list list :=
   SetlikeModule_Monad.
*)

(** * Folding over lists *)
(******************************************************************************)
Fixpoint fold `{op : Monoid_op M} `{unit : Monoid_unit M} (l : list M) : M :=
  match l with
  | nil => Ƶ
  | cons x l' => x ● fold l'
  end.

(** ** Rewriting lemmas for [fold] *)
(******************************************************************************)
Section fold_rewriting_lemmas.

  Context
    `{Monoid M}.

  Lemma fold_nil : fold (@nil M) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_cons : forall (m : M) (l : list M),
      fold (m :: l) = m ● fold l.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_one : forall (m : M), fold [ m ] = m.
  Proof.
    intro. cbn. now simpl_monoid.
  Qed.

  Lemma fold_app : forall (l1 l2 : list M),
      fold (l1 ++ l2) = fold l1 ● fold l2.
  Proof.
    intros l1 ?. induction l1 as [| ? ? IHl].
    - cbn. now simpl_monoid.
    - cbn. rewrite IHl. now simpl_monoid.
  Qed.

End fold_rewriting_lemmas.

(** ** Folding a list is a monoid homomorphism *)
(** <<fold : list M -> M>> is homomorphism of monoids. *)
(******************************************************************************)
Instance Monmor_fold `{Monoid M} : Monoid_Morphism fold :=
  {| monmor_unit := fold_nil;
     monmor_op := fold_app |}.

(** ** Other properties of <<fold>> *)
(******************************************************************************)

(** In the special case that we fold a list of lists, the result is equivalent
    to joining the list of lists. *)
Lemma fold_equal_join : forall {A},
    fold = join list (A:=A).
Proof.
  intros. ext l. induction l as [| ? ? IHl].
  - reflexivity.
  - cbn. now rewrite IHl.
Qed.

(** Folding across a list of monoidal values commutes with applying a monoid
    homomorphism to the elements. *)
Theorem fold_mon_hom : forall `(ϕ : M1 -> M2) `{Monoid_Morphism M1 M2 ϕ},
    ϕ ∘ fold = fold ∘ fmap list ϕ.
Proof.
  intros ? ? ϕ ? ? ? ? ?. unfold compose. ext l.
  induction l as [| ? ? IHl].
  - cbn. apply (monmor_unit ϕ).
  - cbn. now rewrite (monmor_op ϕ), IHl.
Qed.

Corollary fold_nat {A B : Type} (f : A -> B) :
  fmap list f ∘ fold = fold ∘ fmap list (fmap list f).
Proof.
  now rewrite (fold_mon_hom (fmap list f)).
Qed.

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
      fold (join list l) = fold (fmap list fold l).
  Proof.
    intro l. rewrite <- fold_equal_join.
    compose near l on left.
    now rewrite (fold_mon_hom fold).
  Qed.

  Lemma fold_constant_unit : forall (l : list M),
      fold (fmap list (fun _ => Ƶ) l) = Ƶ.
  Proof.
    intro l. induction l.
    - reflexivity.
    - cbn. now simpl_monoid.
  Qed.

End foldable_list.

(** * <<fmap>> equality inversion lemmas *)
(** Some lemmas for reasoning backwards from equality between two
    similarly-concatenated lists.  *)
(******************************************************************************)
Lemma fmap_app_inv_l : forall {A B} {f g : A -> B} (l1 l2 : list A),
    fmap list f (l1 ++ l2) = fmap list g (l1 ++ l2) ->
    fmap list f l1 = fmap list g l1.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl_list in *. rewrite IHl1.
    + fequal. simpl in H. inversion H; auto.
    + simpl in H. inversion H. auto.
Qed.

Lemma fmap_app_inv_r : forall {A B} {f g : A -> B} (l1 l2 : list A),
    fmap list f (l1 ++ l2) = fmap list g (l1 ++ l2) ->
    fmap list f l2 = fmap list g l2.
Proof.
  intros.
  assert (heads_equal : fmap list f l1 = fmap list g l1).
  { eauto using fmap_app_inv_l. }
  simpl_list in *.
  rewrite heads_equal in H.
  eauto using List.app_inv_head.
Qed.

Lemma fmap_app_inv : forall {A B} {f g : A -> B} (l1 l2 : list A),
    fmap list f (l1 ++ l2) = fmap list g (l1 ++ l2) ->
    fmap list f l1 = fmap list g l1 /\ fmap list f l2 = fmap list g l2.
Proof.
  intros; split; eauto using fmap_app_inv_l, fmap_app_inv_r.
Qed.
