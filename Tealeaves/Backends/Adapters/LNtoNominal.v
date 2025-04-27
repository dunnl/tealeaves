From Tealeaves Require Import
  Classes.Kleisli.DecoratedFunctorPoly
  Backends.Nominal.Common.Binding
  Backends.Nominal.Common.Freshening
  Backends.LN.LN.

Import List.ListNotations.
Import ContainerFunctor.Notations.

(** * Converting a depth to (list unit) binding context *)
(**********************************************************************)
Fixpoint length_to_list_unit (length: nat): list unit :=
  match length with
  | 0 => nil
  | S n => tt :: length_to_list_unit n
  end.

Lemma length_length_to_list_unit: forall n,
    length (length_to_list_unit n) = n.
Proof.
  intros. induction n.
  - reflexivity.
  - cbn. fequal; auto.
Qed.

Lemma length_cons {A} {a:A} {l: list A}:
  length (a :: l) = S (length l).
Proof.
  reflexivity.
Qed.

Lemma length_one {A} {a:A}:
  length [a] = 1.
Proof.
  reflexivity.
Qed.

Lemma length_to_list_unit_plus {n m: nat}:
  length_to_list_unit (n + m) =
    length_to_list_unit n ++
      length_to_list_unit m.
Proof.
  induction n.
  - reflexivity.
  - cbn. rewrite IHn.
    reflexivity.
Qed.

Lemma length_to_list_unit_S (n: nat):
  length_to_list_unit (S n) = tt :: length_to_list_unit n.
Proof.
  reflexivity.
Qed.

Lemma length_list_unit_iso (ctx: list unit):
  ctx = length_to_list_unit (length ctx).
Proof.
  induction ctx.
  - reflexivity.
  - cbn. destruct a.
    rewrite IHctx.
    rewrite length_length_to_list_unit.
    reflexivity.
Qed.

#[export] Instance Monoid_Morphism_length:
  Monoid_Morphism (list unit) nat (length (A:=unit)).
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - reflexivity.
  - intros.
    apply List.app_length.
Qed.

(** * Locally Nameless to Nominal *)
(**********************************************************************)

Section with_DTM.

  Context
    {T: Type -> Type -> Type}.

  (* if you are going to crash, do so very loudly *)
  Definition PANIC_INDEX_EXCEEDS_CONTEXT: nat := 1337.

  (* Give a DB index (Bd N), define its new name *)
  Definition bdToName (Γ: list name) (ctx: list unit) (n: nat): atom :=
    if Nat.ltb n (length ctx)
    then assignNames_loc Γ (length_to_list_unit (length ctx - (n + 1)), tt)
    else PANIC_INDEX_EXCEEDS_CONTEXT.

  Lemma bdToName_fresh: forall Γ a ctx n,
      length ctx > n ->
      a ∈ Γ -> bdToName Γ ctx n <> a.
  Proof.
    introv Hlt Hin.
    unfold bdToName.
    apply PeanoNat.Nat.ltb_lt in Hlt.
    rewrite Hlt.
    intro contra.
    subst.
    apply assignNames_loc_fresh in Hin.
    assumption.
  Qed.

  Definition lnToNom_loc (Γ: list name):
    list unit * LN -> name :=
    fun '(depth, v) =>
      match v with
      | Fr x => x
      | Bd n => bdToName Γ depth n
      end.

  Definition lnToNom `{MapdPoly T} (Γ: list name):
    T unit LN -> T name name :=
    mapdp (T := T) (assignNames_loc Γ) (lnToNom_loc Γ).

End with_DTM.

