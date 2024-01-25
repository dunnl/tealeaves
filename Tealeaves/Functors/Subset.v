From Tealeaves Require Export
  Classes.Monoid
  Classes.Kleisli.Monad
  Classes.Categorical.Applicative
  Misc.Subset
  Misc.Prop.

Import Monad.Notations.
Import Product.Notations.
Import Applicative.Notations.
Import Misc.Subset.Notations.

#[local] Generalizable Variables A B.

(** * Monad instance *)
(******************************************************************************)
#[export] Instance Return_subset : Return subset := fun A a b => a = b.

#[local] Notation "{{ x }}" := (@ret subset _ _ x).

#[export] Instance Bind_subset : Bind subset subset := fun A B f s_a =>
(fun b => exists (a : A), s_a a /\ f a b).

(** ** Rewriting laws *)
(******************************************************************************)
Definition set_in_ret : forall A (a b : A),
    (ret a) b = (a = b) := ltac:(reflexivity).

#[export] Hint Rewrite @set_in_ret : tea_set.

Lemma bind_set_nil `{f : A -> subset B} :
  bind f ∅ = ∅.
Proof.
  solve_basic_subset.
Qed.

Lemma bind_set_one `{f : A -> subset B} {a : A} :
  bind f {{ a }} = f a.
Proof.
  solve_basic_subset.
Qed.

Lemma bind_set_add `{f : A -> subset B} {x y} :
  bind f (x ∪ y) = bind f x ∪ bind f y.
Proof.
  solve_basic_subset.
Qed.

#[export] Hint Rewrite
  @bind_set_nil  @bind_set_one  @bind_set_add
  : tea_set.

(** ** Monad laws *)
(******************************************************************************)
Lemma set_bind0 : forall (A B : Type) (f : A -> subset B),
    bind f ∘ ret = f.
Proof.
  intros. ext a. unfold compose.
  now autorewrite with tea_set.
Qed.

Lemma set_bind1 : forall A : Type, bind ret = @id (subset A).
  intros. cbv. ext s a. propext.
  - intros [a' [h1 h2]]. now subst.
  - intro. eexists a. intuition.
Qed.

Lemma set_bind2 : forall (A B C : Type) (g : B -> subset C) (f : A -> subset B),
    bind g ∘ bind f = bind (g ⋆1 f).
Proof.
  intros. ext a. unfold compose.
  cbv. ext c. propext.
  - intros [b [[a' [ha1 ha2]] hb2]].
    exists a'; split; [assumption | exists b; split; assumption].
  - intros [a' [ha1 [b [hb1 hb2]]]].
    exists b; split; [exists a'; split; assumption | assumption].
Qed.

#[export] Instance Monad_set : Monad subset :=
  {| kmon_bind0 := set_bind0;
    kmon_bind1 := set_bind1;
    kmon_bind2 := set_bind2;
  |}.

Lemma set_map_bind_compat : forall (A B : Type) (f : A -> B),
    map (F := subset) f = bind (ret ∘ f).
Proof.
  reflexivity.
Qed.

#[export] Instance MonadFull_set : MonadFull subset :=
  {| kmonf_map_to_bind := set_map_bind_compat; |}.

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind {A B f} :
  Monoid_Morphism (subset A) (subset B) (bind f) :=
  {| monmor_unit := @bind_set_nil A B f;
    monmor_op := @bind_set_add A B f;
  |}.

(** ** Querying for an element is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_el {A : Type} (a : A) :
  @Monoid_Morphism (subset A) Prop
    (@Monoid_op_subset A) (@Monoid_unit_subset A)
    (Monoid_op_or) (Monoid_unit_false)
    (evalAt a).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - reflexivity.
  - reflexivity.
Qed.

(** * Misc properties *)
(******************************************************************************)
Theorem set_ret_injective : forall (A : Type) (a b : A),
    {{ a }} = {{ b }} -> a = b.
Proof.
  intros. assert (lemma : forall x, {{ a }} x = {{ b }} x).
  intros. now rewrite H. specialize (lemma a).
  cbv in lemma. symmetry. now rewrite <- lemma.
Qed.
