From Tealeaves Require Export
  Misc.Prop
  Classes.Functor
  Classes.Monoid.

From Tealeaves Require Import
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Classes.Kleisli.Monad.

Import Kleisli.Monad.Notations.

#[local] Generalizable Variables A B.

(** * Subsets *)
(******************************************************************************)
#[local] Notation "( -> B )" := (fun A => A -> B) (at level 50).
#[local] Notation "'subset'" := ((-> Prop)).

(** ** Operations *)
(******************************************************************************)
Definition subset_one {A}: A -> subset A := eq.

Definition subset_empty {A}: subset A :=
  const False.

Definition subset_add {A}: subset A -> subset A -> subset A :=
  fun x y p => x p \/ y p.

(** ** Notations and tactics *)
(******************************************************************************)
Module Notations.
  Notation "∅" := subset_empty: tealeaves_scope.
  Notation "{{ x }}" := (subset_one x): tealeaves_scope.
  Infix "∪" := subset_add (at level 61, left associativity): tealeaves_scope.
  Notation "( -> B )" := (fun A => A -> B) (at level 50): tealeaves_scope.
  Notation "'subset'" := ((-> Prop)): tealeaves_scope.
End Notations.

Import Notations.

Tactic Notation "simpl_subset" := (autorewrite with tea_set).
Tactic Notation "simpl_subset" "in" hyp(H) := (autorewrite with tea_set H).
Tactic Notation "simpl_subset" "in" "*" := (autorewrite with tea_set in *).

Ltac unfold_subset :=
  unfold subset_empty; unfold subset_add; unfold const.

Ltac solve_basic_subset :=
  unfold transparent tcs; unfold_subset; unfold compose; try setext;
  first [tauto | firstorder (subst; (solve auto + eauto)) ].

(** * The <<subset>> Monoid *)
(******************************************************************************)
Section subset_monoid.

  Context
    {A: Type}.

  Implicit Types (s t: subset A) (a: A).

  Definition subset_add_nil_l: forall s, s ∪ ∅ = s :=
    ltac:(solve_basic_subset).
  Definition subset_add_nil_r: forall s, ∅ ∪ s = s :=
    ltac:(solve_basic_subset).
  Definition subset_add_assoc: forall s t u, s ∪ t ∪ u = s ∪ (t ∪ u) :=
    ltac:(solve_basic_subset).
  Definition subset_add_comm: forall s t, s ∪ t = t ∪ s :=
    ltac:(solve_basic_subset).

  Definition subset_in_empty: forall a, ∅ a = False
    := ltac:(solve_basic_subset).
  Definition subset_in_add: forall s t a, (s ∪ t) a = (s a \/ t a)
    := ltac:(solve_basic_subset).

End subset_monoid.

#[export] Hint Rewrite @subset_add_nil_l @subset_add_nil_r
     @subset_add_assoc @subset_in_empty @subset_in_add: tea_set.

#[export] Instance Monoid_op_subset {A}: Monoid_op (subset A) := @subset_add A.

#[export] Instance Monoid_unit_subset {A}: Monoid_unit (subset A) := subset_empty.

#[export, program] Instance Monoid_subset {A} :
  @Monoid (subset A) (@Monoid_op_subset A) (@Monoid_unit_subset A).

Solve Obligations with (intros; unfold transparent tcs; solve_basic_subset).

#[export] Instance CommutativeMonoidOp_subset: forall (A: Type),
    CommutativeMonoidOp (M := subset A) Monoid_op_subset.
Proof.
  intros; constructor; solve_basic_subset.
Qed.

(** ** Querying for an element is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_el {A: Type} (a: A) :
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

(** * The <<subset>> Functor *)
(******************************************************************************)

(** ** The Map Operation *)
(******************************************************************************)
#[export] Instance Map_subset: Map subset :=
  fun A B f s b => exists (a: A), s a /\ f a = b.

(** ** Rewriting rules *)
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

(** ** Functor laws *)
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

(** ** Mapping is a Monoid Homomorphism *)
(******************************************************************************)
#[export] Instance Monoid_Morphism_subset_map:
  forall (A B: Type) (f: A -> B), Monoid_Morphism (subset A) (subset B) (map f).
Proof.
  intros.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - ext b. apply propositional_extensionality.
    firstorder.
  - intros. ext b. apply propositional_extensionality.
    firstorder.
Qed.

(** * Monad Instance (Categorical) *)
(******************************************************************************)
#[export] Instance Return_subset: Return subset := fun A a b => a = b.

#[local] Notation "{{ x }}" := (@ret subset _ _ x).

(** ** Monad Laws *)
(******************************************************************************)
#[export] Instance Natural_Return_subset: Natural (@ret subset _).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros. ext a. ext b.
    unfold_ops @Map_I @Map_subset @Return_subset.
    unfold compose.
    propext.
    firstorder (now subst).
    firstorder (now subst).
Qed.

(* TODO *)

(** * Monad Instances (Kleisli) *)
(******************************************************************************)

#[export] Instance Bind_subset: Bind subset subset := fun A B f s_a =>
(fun b => exists (a: A), s_a a /\ f a b).

(** ** Rewriting laws *)
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

(** ** Monad Laws *)
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
    bind g ∘ bind f = bind (g ⋆ f).
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

(** * Applicative instances for subset *)
(******************************************************************************)
Section subset_applicative_instance.

  Import Applicative.Notations.

  #[export] Instance Pure_subset: Pure subset := @eq.

  #[export] Instance Mult_subset: Mult subset :=
    fun A B '(sa, sb) '(a, b) => sa a /\ sb b.

  #[export] Instance Applicative_subset: Applicative subset.
  Proof.
    constructor.
    - apply Functor_subset.
    - intros. change (pure ?x) with (ret x).
      now simpl_subset.
    - intros. unfold_ops @Mult_subset.
      ext [c d]. cbv. propext.
      + intros [[a [Ha1 Ha2]] [b [Hb1 Hb2]]].
        exists (a, b). subst. intuition.
      + intros [[a b] [Hab1 Hab2]].
        inversion Hab2. subst. intuition eauto.
    - intros. ext [a [b c]]. cbv.
      propext.
      + intros [[[a' b'] c'] [Ht1 Ht2]].
        inversion Ht2; subst. tauto.
      + intros. exists (a, b, c). tauto.
    - intros. ext a. cbv.
      propext.
      + intros [[tt' a'] [H1 H2]]. now subst.
      + intros Xa. exists (tt, a). tauto.
    - intros. ext a. cbv.
      propext.
      + intros [[a' tt'] [H1 H2]]. now subst.
      + intros Xa. exists (a, tt). tauto.
    - intros. ext [a' b']. cbv. propext.
      + intuition. now subst.
      + intros X; inversion X; now subst.
  Qed.

  Lemma subset_ap_spec:
    forall (A B: Type) (sf: subset (A -> B)) (sa: subset A) (b: B),
      (sf <⋆> sa) b = exists (f: A -> B) (a: A), sa a /\ sf f /\ f a = b.
  Proof.
    intros.
    unfold ap.
    unfold_ops @Map_subset.
    unfold_ops @Mult_subset.
    propext.
    - intros [[f a] [[hyp1 hyp2] hyp3]].
      exists f a. auto.
    - intros [f [a [hyp1 [hyp2 hyp3]]]].
      subst. exists (f, a). tauto.
  Qed.

  Lemma fn_nequal_counterexample:
    forall (A B: Type) (f g: A -> B),
      (exists (a: A), (f a <> g a)) -> f <> g.
  Proof.
    intros.
    intro contra.
    destruct H as [a Hneq].
    rewrite contra in Hneq.
    contradiction.
  Qed.

  Corollary subset_nequal_counterexample:
    forall (A: Type) (a: A) (s1 s2: subset A),
      s1 a -> ~ s2 a ->
      s1 <> s2.
  Proof.
    intros.
    apply fn_nequal_counterexample.
    exists a. intro contra.
    rewrite contra in H.
    contradiction.
  Qed.

  Example not_subset_idem:
    ~ (forall (A: Type) (s: subset A),
          s ⊗ s = map (fun a: A => (a, a)) s).
  Proof.
    intro contra.
    specialize (contra nat ({{1}} ∪ {{2}})).
    generalize contra.
    pose (ctx := subset_nequal_counterexample (nat * nat) (1, 2)).
    unfold not in ctx.
    unfold map, Map_subset, mult,Mult_subset.
    apply ctx.
    - simpl_subset. tauto.
    - intros [a [_ false]].
      now inversion false.
  Qed.

  Lemma subset_commutative:
    forall (A: Type) (sA: subset A), Center subset%tea A sA.
  Proof.
    intros. constructor; intros;
     unfold_ops @Mult_subset;
       unfold_ops @Map_subset.
     - rename x into sB.
       ext [b a].
       propext.
       + intros [Ha Hb].
         exists (a, b). tauto.
       + intros [[a' b'] [H1 H2]].
         inversion H2. subst. tauto.
     - rename x into sB.
       ext [a b].
       propext.
       + intros [Ha Hb].
         exists (b, a). tauto.
       + intros [[b' a'] [H1 H2]].
         inversion H2. subst. tauto.
  Qed.

End subset_applicative_instance.
