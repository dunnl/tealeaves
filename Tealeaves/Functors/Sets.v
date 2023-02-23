From Tealeaves.Classes Require Import
  Monoid Monad Applicative.
From Tealeaves Require Export
  Data.Sets.

Import Product.Notations.
Import Applicative.Notations.
Import Data.Sets.Notations.

#[local] Generalizable Variables A B.

(** * The <<set>> monad *)
(******************************************************************************)

(** ** Functor instance *)
(******************************************************************************)

(** [fmap f s] is the image of a set [s] under a morphism [f] *)
#[export] Instance Fmap_set : Fmap set :=
  fun A B (f : A -> B) (x : A -> Prop) (b : B) => exists a : A, x a /\ f a = b.

(** *** Rewriting lemmas for [fmap] *)
(******************************************************************************)
Definition fmap_set_nil `{f : A -> B} :
  fmap set f ∅ = ∅ := ltac:(solve_basic_set).

Definition fmap_set_add `{f : A -> B} {x y} :
  fmap set f (x ∪ y) = fmap set f x ∪ fmap set f y
  := ltac:(solve_basic_set).

#[export] Hint Rewrite @fmap_set_nil @fmap_set_add : tea_set.

(** *** Functor laws *)
(******************************************************************************)
Definition fun_fmap_id_set {A} : fmap set id = @id (set A) :=
  ltac:(solve_basic_set).

Definition fun_fmap_fmap_set {A B C} : forall (f : A -> B) (g : B -> C),
    fmap set g ∘ fmap set f = fmap set (g ∘ f)
    := ltac:(solve_basic_set).

#[export] Instance Functor_set : Functor set :=
  ltac:(constructor; solve_basic_set).

(** ** [fmap] is a monoid homomorphism *)
(******************************************************************************)
#[export, program] Instance Monmor_set_fmap `(f : A -> B) :
  Monoid_Morphism (fmap set f) :=
  {| monmor_unit := @fmap_set_nil A B f;
    monmor_op := @fmap_set_add A B f;
  |}.

(** ** Monad operations *)
(******************************************************************************)
#[export] Instance Return_set : Return set := fun A a b => a = b.

#[export] Instance Join_set : Join set :=
  fun A (x : (A -> Prop) -> Prop) => fun a => exists (y : A -> Prop) , x y /\ y a.

#[local] Notation "{{ x }}" := (ret set x).

Theorem set_ret_injective : forall A (a b : A),
    {{ a }} = {{ b }} -> a = b.
Proof.
  intros. assert (lemma : forall x, {{ a }} x = {{ b }} x).
  intros. now rewrite H. specialize (lemma a).
  cbv in lemma. symmetry. now rewrite <- lemma.
Qed.

(** ** Rewriting laws for [join] and [ret] *)
(******************************************************************************)
Definition set_in_ret : forall A (a b : A),
    (ret set a) b = (a = b)
  := ltac:(solve_basic_set).

Lemma join_set_nil : forall A,
    join (A:=A) set ∅ = ∅.
Proof.
  solve_basic_set.
Qed.

Lemma join_set_one : forall A (x : set A),
    join set {{ x }} = x.
Proof.
  solve_basic_set.
Qed.

Lemma join_set_add : forall A (x y : set (set A)),
    join set (x ∪ y) = join set x ∪ join set y.
Proof.
  solve_basic_set.
Qed.

Lemma fmap_set_one `{f : A -> B} {a : A} :
  fmap set f {{ a }} = {{ f a }}.
Proof.
  solve_basic_set.
Qed.

#[export] Hint Rewrite @set_in_ret @join_set_nil @join_set_one @join_set_add
     @fmap_set_add @fmap_set_one : tea_set.

(** ** Monad laws *)
(******************************************************************************)
Theorem join_ret {A} :
  join set ∘ ret set = @id (A -> Prop).
Proof.
  solve_basic_set.
Qed.

Theorem join_fmap_ret {A} :
  join set ∘ fmap set (ret set) = @id (A -> Prop).
Proof.
  unfold transparent tcs; unfold_set. unfold compose. setext.
  - firstorder (do 2 subst; auto).
  - firstorder eauto.
Qed.

Theorem join_join {A} :
  join set ∘ join set =
  join set ∘ fmap set (join set (A:=A)).
Proof.
  unfold transparent tcs; unfold_set. unfold compose. setext.
  - intros. preprocess. repeat eexists; eauto.
  - intros. preprocess. repeat eexists; eauto.
Qed.

#[export] Instance Natural_ret : Natural (@ret set _) :=
  ltac:(constructor; try typeclasses eauto;
       unfold compose; solve_basic_set).

#[export] Instance Natural_join : Natural (@join set _).
Proof.
  ltac:(constructor; try typeclasses eauto).
  intros. unfold compose. ext SS. ext b.
  propext.
  - unfold transparent tcs.
    intros [a [a_in_join a_to_b]].
    destruct a_in_join as [S [S1 S2]].
    exists (fmap set f S). split.
    + now (exists S).
    + unfold transparent tcs. now (exists a).
  - unfold transparent tcs.
    intros [Sb [H1 H2]].
    destruct H1 as [S [SS1 SS2]].
    rewrite <- SS2 in H2. destruct H2 as [a [a1 a2]].
    subst. exists a. split; auto. now (exists S).
Qed.

#[export] Instance Monad_set : Monad set :=
  {| mon_join_ret := @join_ret;
     mon_join_fmap_ret := @join_fmap_ret;
     mon_join_join := @join_join;
  |}.

(** * Set as an applicative functor *)
(******************************************************************************)
(*
TODO: This isn't really necessary because it is inferred from the monad instance.
 *)
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
      fmap set f (pure set x) = pure set (f x).
  Proof.
    intros. unfold transparent tcs. ext b.
    propext; firstorder (now subst).
  Qed.

  Theorem app_mult_natural_set : forall (A B C D: Type) (f : A -> C) (g : B -> D) (x : set A) (y : set B),
      mult set  (fmap set f x, fmap set g y) = fmap set (map_tensor f g) (mult set (x, y)).
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
      fmap set α (x ⊗ y ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. ext [a [b c]]. unfold transparent tcs.
    cbn. propext.
    - intros [[[a1 b1] c1]]. cbn in *.
      now preprocess.
    - intros. now exists (a, b, c).
  Qed.

  Theorem app_unital_l_set : forall (A : Type) (x : set A),
      fmap set left_unitor (pure set tt ⊗ x) = x.
  Proof.
    intros. ext a. unfold transparent tcs. cbn. propext.
    + intros [[? a1] rest]. cbn in rest. now preprocess.
    + exists (tt, a). easy.
  Qed.

  Theorem app_unital_r_set : forall (A : Type) (x : set A),
      fmap set right_unitor (x ⊗ pure set tt) = x.
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

Import Tealeaves.Classes.Kleisli.Monad.
Import Tealeaves.Classes.Monad.ToKleisli.

(** ** [set]/[set] right module *)
(******************************************************************************)
#[export] Instance Bind_set: Bind set set := Monad.ToKleisli.Bind_join set.
#[export] Instance KleisliMonad_list : Kleisli.Monad.Monad set := Kleisli_Monad set.

(** ** Rewriting lemmas for <<bind>> *)
(******************************************************************************)
Lemma bind_set_nil `{f : A -> set B} :
  bind set f ∅ = ∅.
Proof.
  solve_basic_set.
Qed.

Lemma bind_set_one `{f : A -> set B} (a : A) :
  bind set f {{ a }} = f a.
Proof.
  unfold_ops @Bind_set.
  unfold_ops @Bind_join.
  unfold compose; cbn.
  rewrite fmap_set_one.
  rewrite join_set_one.
  reflexivity.
Qed.

Lemma bind_set_add `{f : A -> set B} {x y} :
  bind set f (x ∪ y) = bind set f x ∪ bind set f y.
Proof.
  solve_basic_set.
Qed.

(** Since [bind] is defined tediously by composing <<join>> and
    <<fmap>>, we give a characterization of <<set>>'s <<bind>> that is
    easier to use. N.B. be mindful that this rewriting would have to
    be done ~before~ calling <<unfold transparent tcs>>, otherwise <<bind set>>
    will be unfolded to its definition first. *)
Lemma bind_set_spec : forall `(f : A -> set B) (s : set A) (b : B),
    bind set f s b = exists (a : A), s a /\ f a b.
Proof.
  unfold_ops @Bind_set.
  unfold_ops @Bind_join.
  solve_basic_set.
Qed.

#[export] Hint Rewrite @bind_set_nil @bind_set_one @bind_set_add : tea_set.

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind {A B f} : Monoid_Morphism (bind set f) :=
  {| monmor_unit := @bind_set_nil A B f;
     monmor_op := @bind_set_add A B f;
  |}.
