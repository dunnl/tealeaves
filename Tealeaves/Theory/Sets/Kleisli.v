From Tealeaves Require Export
  Functors.Sets
  Classes.Monoid
  Classes.Algebraic.Monad
  Classes.Kleisli.Monad
  Theory.Algebraic.Monad.ToKleisli.

Import Sets.Notations.

#[local] Generalizable Variables A B.

(** ** [set]/[set] right module *)
(******************************************************************************)
#[export] Instance Bind_set: Bind set set := ToKleisli.Operation.Bind_Join set.
#[export] Instance KleisliMonad_list : Kleisli.Monad.Monad set := ToKleisli.KM_M.

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
  unfold_ops @Operation.Bind_Join.
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
  unfold_ops @Operation.Bind_Join.
  solve_basic_set.
Qed.

#[export] Hint Rewrite @bind_set_nil @bind_set_one @bind_set_add : tea_set.

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind {A B f} : Monoid_Morphism (bind set f) :=
  {| monmor_unit := @bind_set_nil A B f;
     monmor_op := @bind_set_add A B f;
  |}.
