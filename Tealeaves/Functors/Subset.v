From Tealeaves Require Export
  Classes.Monoid
  Classes.Kleisli.Theory.Monad
  Classes.Categorical.Applicative
  Functors.Early.Subset.

Import Monad.Notations.
Import Product.Notations.
Import Applicative.Notations.
Import Misc.Subset.Notations.

#[local] Generalizable Variables A B.

(* Located in Misc.subset

(** * Functor instance *)
(******************************************************************************)
#[export] Instance Map_subset: Map subset :=
  fun A B f sa b => exists (a: A), sa a /\ f a = b.

Lemma map_id_subset:
  forall (A: Type), map (@id A) = @id (subset A).
Proof.
  intros. ext sa a. unfold id.
  unfold_ops @Map_subset. propext.
  firstorder (subst; auto).
  eauto.
Qed.

Lemma map_map_subset:
  forall (A B C: Type) (f: A -> B) (g: B -> C),
    map g ∘ map f = map (F := subset) (g ∘ f).
Proof.
  intros. ext sa c. unfold compose.
  unfold_ops @Map_subset. propext.
  firstorder subst. eauto.
  firstorder.
Qed.

#[export] Instance Functor_subset: Functor subset :=
  {| fun_map_id := map_id_subset;
    fun_map_map := map_map_subset;
  |}.

*)

#[export] Instance Compat_Map_Bind_subset :
  `{Compat_Map_Bind (Map_U := Map_subset) subset subset} := ltac:(reflexivity).

(** ** <<bind>> is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind {A B f} :
  Monoid_Morphism (subset A) (subset B) (bind f) :=
  {| monmor_unit := @bind_set_nil A B f;
    monmor_op := @bind_set_add A B f;
  |}.


(** * Misc properties *)
(******************************************************************************)
