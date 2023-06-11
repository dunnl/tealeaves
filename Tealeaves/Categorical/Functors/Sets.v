
(** ** Functor instance *)
(******************************************************************************)

(** [map f s] is the image of a set [s] under a morphism [f] *)
#[export] Instance Map_set : Map set :=
  fun A B (f : A -> B) (x : A -> Prop) (b : B) => exists a : A, x a /\ f a = b.

(** *** Rewriting lemmas for [map] *)
(******************************************************************************)
Definition map_set_nil `{f : A -> B} :
  map set A B f ∅ = ∅ := ltac:(solve_basic_set).

Definition map_set_add `{f : A -> B} {x y} :
  map set A B f (x ∪ y) = map set A B f x ∪ map set A B f y
  := ltac:(solve_basic_set).

#[export] Hint Rewrite @map_set_nil @map_set_add : tea_set.

(** *** Functor laws *)
(******************************************************************************)
Definition fun_map_id_set {A} : map set A A id = @id (set A) :=
  ltac:(solve_basic_set).

Definition fun_map_map_set {A B C} : forall (f : A -> B) (g : B -> C),
    map set B C g ∘ map set A B f = map set A C (g ∘ f)
    := ltac:(solve_basic_set).

#[export] Instance Functor_set : Functor set :=
  ltac:(constructor; solve_basic_set).

(** ** [map] is a monoid homomorphism *)
(******************************************************************************)
#[export, program] Instance Monmor_set_map `(f : A -> B) :
  Monoid_Morphism (map set A B f) :=
  {| monmor_unit := @map_set_nil A B f;
    monmor_op := @map_set_add A B f;
  |}.

#[export] Instance Join_set : Join set :=
  fun A (x : (A -> Prop) -> Prop) => fun a => exists (y : A -> Prop) , x y /\ y a.


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


#[export] Hint Rewrite @set_in_ret @join_set_nil @join_set_one @join_set_add
  @map_set_add @map_set_one : tea_set.

(** ** Monad laws *)
(******************************************************************************)
Theorem join_ret {A} :
  join set ∘ ret set = @id (A -> Prop).
Proof.
  solve_basic_set.
Qed.

Theorem join_map_ret {A} :
  join set ∘ map set (ret set) = @id (A -> Prop).
Proof.
  unfold transparent tcs; unfold_set. unfold compose. setext.
  - firstorder (do 2 subst; auto).
  - firstorder eauto.
Qed.

Theorem join_join {A} :
  join set ∘ join set =
  join set ∘ map set (join set (A:=A)).
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
    exists (map set f S). split.
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
     mon_join_map_ret := @join_map_ret;
     mon_join_join := @join_join;
  |}.


(** ** [set]/[set] right module *)
(******************************************************************************)
#[export] Instance Bind_set: Bind set set := Monad.ToKleisli.Bind_join set.
#[export] Instance KleisliMonad_list : Kleisli.Monad.Monad set := Kleisli_Monad set.

(** ** Rewriting lemmas for <<bind>> *)
(******************************************************************************)

(** Since [bind] is defined tediously by composing <<join>> and
    <<map>>, we give a characterization of <<set>>'s <<bind>> that is
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
