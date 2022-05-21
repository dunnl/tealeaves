From Tealeaves Require Import
     Classes.Monoid.

From Multisorted Require Import
     Classes.Functor.

Import Monoid.Notations.
Import Multisorted.Theory.Category.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

(** * Universals (Row) *)
(******************************************************************************)
Section row_functor.

  Context
    `{Index}.

  Definition Row A := K -> A.

  #[global] Instance MFmap_Row : MFmap Row :=
    fun `(f : A -k-> B) xs k => f k (xs k).

  Lemma mfmap_id_Row {A} : mfmap Row kid = @id (Row A).
  Proof.
    now ext x k.
  Qed.

  Lemma mfmap_mfmap_Row :
    forall `(f : A -k-> B) `(g : B -k-> C),
      mfmap Row g ∘ mfmap Row f = mfmap Row (g ⊙ f).
  Proof.
    introv; now ext x k.
  Qed.

  #[global] Instance MFunctor_Row : MultisortedFunctor Row :=
    {| mfun_mfmap_id := @mfmap_id_Row;
       mfun_mfmap_mfmap := @mfmap_mfmap_Row;
    |}.

End row_functor.

(** * Vectors of monoid values *)
(******************************************************************************)
Section kmonoid.

  Context
    `{Index}
    `{Monoid W}.

  #[global] Instance Monoid_op_Row : Monoid_op (Row W) :=
    fun x y k => x k ● y k.

  #[global] Instance Monoid_unit_Row : Monoid_unit (Row W) :=
    fun _ =>  Ƶ.

  #[global] Instance Monoid_Row : Monoid (Row W).
  Proof.
    constructor;
      unfold monoid_op, Monoid_op_Row,
      monoid_unit, Monoid_unit_Row;
      introv; ext k.
    all: now simpl_monoid.
  Qed.

End kmonoid.
