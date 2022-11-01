From Tealeaves Require Export
  Functors.List
  Classes.Monoid
  Classes.Algebraic.Monad
  Classes.Kleisli.Monad
  Theory.Algebraic.Monad.ToKleisli.

Import List.ListNotations.
#[local] Open Scope list_scope.

(** ** [list]/[list] right module *)
(******************************************************************************)
#[export] Instance Bind_list : Bind list list := ToKleisli.Operation.Bind_alg list.
#[export] Instance KleisliMonad_list : Kleisli.Monad.Monad list := ToKleisli.Instance.toKleisli list.

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
    intros. unfold_ops @Bind_list. unfold_ops @Operation.Bind_Join.
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
    intros. unfold_ops @Bind_list. unfold_ops @Operation.Bind_Join.
    unfold compose. intros. now autorewrite with tea_list.
  Qed.

End bind_rewriting_lemmas.

#[export] Hint Rewrite bind_list_nil bind_list_one bind_list_cons bind_list_app :
  tea_list.

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind {A B f} : Monoid_Morphism (bind list f) :=
  {| monmor_unit := bind_list_nil A B f;
     monmor_op := bind_list_app A B f;
  |}.
