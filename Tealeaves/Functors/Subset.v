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
#[local] Arguments bind (U T)%function_scope {Bind} (A B)%type_scope _%function_scope _.

(** * The <<subset>> monad *)
(******************************************************************************)

(** ** Monad instance *)
(******************************************************************************)
#[export] Instance Return_subset : Return subset := fun A a b => a = b.

#[export] Instance Bind_subset : Bind subset subset := fun A B f s_a =>
(fun b => exists (a : A), s_a a /\ f a b).

#[local] Notation "{{ x }}" := (ret subset _ x).

(** ** Rewriting laws *)
(******************************************************************************)
Lemma bind_set_nil `{f : A -> subset B} :
  bind subset subset A B f ∅ = ∅.
Proof.
  solve_basic_subset.
Qed.

Lemma bind_set_one `{f : A -> subset B} {a : A} :
  bind subset subset A B f {{ a }} = f a.
Proof.
  solve_basic_subset.
Qed.

Lemma bind_set_add `{f : A -> subset B} {x y} :
  bind subset subset A B f (x ∪ y) = bind subset subset A B f x ∪ bind subset subset A B f y.
Proof.
  solve_basic_subset.
Qed.

Import Monad.DerivedInstances.

#[export] Instance Map_subset : Map subset := DerivedInstances.Map_Bind subset.

Definition map_set_nil `{f : A -> B} :
  map subset f ∅ = ∅ := ltac:(solve_basic_subset).

Lemma map_set_one `{f : A -> B} {a : A} :
  map subset f {{ a }} = {{ f a }}.
Proof.
  solve_basic_subset.
Qed.

Definition map_set_add `{f : A -> B} {x y} :
  map subset f (x ∪ y) = map subset f x ∪ map subset f y
  := ltac:(solve_basic_subset).

#[export] Hint Rewrite
  @bind_set_nil @bind_set_one @bind_set_add
  @map_set_nil  @map_set_one  @map_set_add
  : tea_set.

Definition set_in_ret : forall A (a b : A),
    (ret subset A a) b = (a = b) := ltac:(reflexivity).

#[export] Hint Rewrite @set_in_ret : tea_set.

(** ** Monad laws *)
(******************************************************************************)

Lemma set_bind0 : forall (A B : Type) (f : A -> subset B),
    bind subset subset A B f ∘ ret subset A = f.
Proof.
  intros. ext a. unfold compose.
  now autorewrite with tea_set.
Qed.

Lemma set_bind1 : forall A : Type, bind subset subset A A (ret subset A) = id.
  intros. cbv. ext s a. propext.
  - intros [a' [h1 h2]]. now subst.
  - intro. eexists a. intuition.
Qed.

Lemma set_bind2 : forall (A B C : Type) (g : B -> subset C) (f : A -> subset B),
    bind subset subset B C g ∘ bind subset subset A B f = bind subset subset A C (g ⋆1 f).
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

#[export] Instance Functor_set : Functor subset := DerivedInstances.Monad_Functor.

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind {A B f} : Monoid_Morphism (bind subset subset A B f) :=
  {| monmor_unit := @bind_set_nil A B f;
    monmor_op := @bind_set_add A B f;
  |}.

(** ** Querying for an element is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_el {A : Type} (a : A) :
  @Monoid_Morphism _ _ (@Monoid_op_subset A) (@Monoid_unit_subset A)
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

(** * Toset operation *)
(******************************************************************************)
Import Functor.Notations.

Section ops.

  Context
    (F : Type -> Type).

  Class El :=
    el : F ⇒ subset.

  Class El_ctx (W : Type) :=
    el_ctx : forall (A : Type), F A -> subset (W * A).

End ops.

Module ElNotations.

  Notation "x ∈ t" :=
    (el _ _ t x) (at level 50) : tealeaves_scope.

  Notation "x ∈d t" :=
    (el_ctx _ _ t x) (at level 50) : tealeaves_scope.

End ElNotations.

(** * Set as an applicative functor *)
(******************************************************************************)
(*
TODO: This isn't really necessary because it is inferred from the monad instance.
Section set_applicative.

  Instance Pure_set : Pure set := @eq.

  #[export] Instance Mult_set : Mult set :=
    fun (A B : Type) (p : set A * set B) (v : A * B) =>
      (fst p) (fst v) /\ (snd p) (snd v).

  Theorem app_mult_pure_set : forall (A B : Type) (a : A) (b : B),
      mult set (pure set a, pure set b) = pure set (a, b).
  Proof.
    intros. unfold transparent tcs.
    ext [a1 b1]. cbn. propext; now rewrite pair_equal_spec.
  Qed.

  Theorem app_pure_natural_set : forall (A B : Type) (f : A -> B) (x : A),
      map set f (pure set x) = pure set (f x).
  Proof.
    intros. unfold transparent tcs. ext b.
    propext; firstorder (now subst).
  Qed.

  Theorem app_mult_natural_set : forall (A B C D: Type) (f : A -> C) (g : B -> D) (x : set A) (y : set B),
      mult set  (map set f x, map set g y) = map set (map_tensor f g) (mult set (x, y)).
  Proof.
    intros. unfold transparent tcs. ext [c d].
    cbn. propext.
    - intros [[a ?] [b ?]].
      exists (a, b). firstorder (now subst).
    - intros [[a b] rest]. cbn in *.
      rewrite pair_equal_spec in rest.
      split. exists a; tauto. exists b; tauto.
  Qed.

  Theorem app_assoc_set : forall (A B C : Type) (x : set A) (y : set B) (z : set C),
      map set α (x ⊗ y ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. ext [a [b c]]. unfold transparent tcs.
    cbn. propext.
    - intros [[[a1 b1] c1]]. cbn in *.
      now preprocess.
    - intros. now exists (a, b, c).
  Qed.

  Theorem app_unital_l_set : forall (A : Type) (x : set A),
      map set left_unitor (pure set tt ⊗ x) = x.
  Proof.
    intros. ext a. unfold transparent tcs. cbn. propext.
    + intros [[? a1] rest]. cbn in rest. now preprocess.
    + exists (tt, a). easy.
  Qed.

  Theorem app_unital_r_set : forall (A : Type) (x : set A),
      map set right_unitor (x ⊗ pure set tt) = x.
  Proof.
    intros. ext a. unfold transparent tcs. cbn. propext.
    + intros [[? a1] rest]. cbn in rest. now preprocess.
    + intros. exists (a, tt). easy.
  Qed.

  Instance Applicative_set : Applicative set :=
    {| app_mult_pure := app_mult_pure_set;
      app_pure_natural := app_pure_natural_set;
      app_mult_natural := app_mult_natural_set;
      app_assoc := app_assoc_set;
      app_unital_l := app_unital_l_set;
      app_unital_r := app_unital_r_set;
    |}.

End set_applicative.
 *)
