From Tealeaves Require Export
  Misc.Subset
  Classes.Functor
  Classes.Kleisli.Monad.

Import Kleisli.Monad.Notations.
Import Subset.Notations.

#[local] Generalizable Variables A B.

(** * The <<subset>> functor *)
(******************************************************************************)

(** ** Functor instance *)
(******************************************************************************)
#[export] Instance Map_subset: Map subset :=
  fun A B f s b => exists (a: A), s a /\ f a = b.

(** *** Rewriting rules *)
(******************************************************************************)
Definition map_set_nil `{f: A -> B} :
  map f ∅ = ∅ := ltac:(solve_basic_subset).

Lemma map_set_one `{f: A -> B} {a: A} :
  map f {{ a }} = {{ f a }}.
Proof.
  ext b. propext.
  - intros [a' [Hin Heq]].
    cbv in Hin; subst.
    solve_basic_subset.
  - cbv. intro; subst.
    eauto.
Qed.

Definition map_set_add `{f: A -> B} {x y} :
  map f (x ∪ y) = map f x ∪ map f y
  := ltac:(solve_basic_subset).

#[export] Hint Rewrite
  @map_set_nil  @map_set_one  @map_set_add
 : tea_set.

(** *** Functor laws *)
(******************************************************************************)
Lemma map_id_subset: forall (A: Type), map id = id (A := subset A).
Proof.
  intros. ext s a.
  cbv. propext.
  - intros [a' [Hin Heq]]. now subst.
  - intros H. eauto.
Qed.

Lemma map_map_subset: forall (A B C: Type) (f: A -> B) (g: B -> C),
    map g ∘ map f = map (F := subset) (g ∘ f).
Proof.
  intros. ext s c.
  unfold compose. cbv.
  propext.
  - intros [b [[a [Hina Heqa]] Heq]].
    exists a. rewrite Heqa. eauto.
  - intros [a [Hin Heq]]. eauto.
Qed.

#[export] Instance Functor_subset: Functor subset :=
  {| fun_map_id := map_id_subset;
     fun_map_map := map_map_subset;
  |}.

(** ** Kleisli monad instance *)
(******************************************************************************)
#[export] Instance Return_subset: Return subset := fun A a b => a = b.

#[local] Notation "{{ x }}" := (@ret subset _ _ x).

#[export] Instance Bind_subset: Bind subset subset := fun A B f s_a =>
(fun b => exists (a: A), s_a a /\ f a b).

(** *** Rewriting laws *)
(******************************************************************************)
Definition set_in_ret: forall A (a b: A),
    (ret a) b = (a = b) := ltac:(reflexivity).

#[export] Hint Rewrite @set_in_ret: tea_set.

Lemma bind_set_nil `{f: A -> subset B} :
  bind f ∅ = ∅.
Proof.
  solve_basic_subset.
Qed.

Lemma bind_set_one `{f: A -> subset B} {a: A} :
  bind f {{ a }} = f a.
Proof.
  solve_basic_subset.
Qed.

Lemma bind_set_add `{f: A -> subset B} {x y} :
  bind f (x ∪ y) = bind f x ∪ bind f y.
Proof.
  solve_basic_subset.
Qed.

#[export] Hint Rewrite
  @bind_set_nil  @bind_set_one  @bind_set_add
 : tea_set.

(** *** Monad laws *)
(******************************************************************************)
Lemma set_bind0: forall (A B: Type) (f: A -> subset B),
    bind f ∘ ret = f.
Proof.
  intros. ext a. unfold compose.
  now autorewrite with tea_set.
Qed.

Lemma set_bind1: forall A: Type, bind ret = @id (subset A).
  intros. cbv. ext s a. propext.
  - intros [a' [h1 h2]]. now subst.
  - intro. eexists a. intuition.
Qed.

Lemma set_bind2: forall (A B C: Type) (g: B -> subset C) (f: A -> subset B),
    bind g ∘ bind f = bind (g ⋆1 f).
Proof.
  intros. ext a. unfold compose.
  cbv. ext c. propext.
  - intros [b [[a' [ha1 ha2]] hb2]].
    exists a'; split; [assumption | exists b; split; assumption].
  - intros [a' [ha1 [b [hb1 hb2]]]].
    exists b; split; [exists a'; split; assumption | assumption].
Qed.

#[export] Instance RightPreModule_subset: RightPreModule subset subset :=
  {| kmod_bind1 := set_bind1;
    kmod_bind2 := set_bind2;
  |}.

#[export] Instance Monad_subset: Monad subset :=
  {| kmon_bind0 := set_bind0;
  |}.

#[export] Instance RightModule_subset: RightModule subset subset :=
  {| kmod_monad := _;
  |}.

(** ** Misc laws *)
(******************************************************************************)
Theorem set_ret_injective: forall (A: Type) (a b: A),
    {{ a }} = {{ b }} -> a = b.
Proof.
  intros. assert (lemma: forall x, {{ a }} x = {{ b }} x).
  intros. now rewrite H. specialize (lemma a).
  cbv in lemma. symmetry. now rewrite <- lemma.
Qed.
