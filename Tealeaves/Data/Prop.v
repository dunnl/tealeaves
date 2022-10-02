From Tealeaves Require Import
  Util.Prelude
  Classes.Monoid.

(** * Propositional monoids *)
Section propositional_monoids.

  #[global] Instance: Monoid_op Prop := and.

  #[global] Instance: Monoid_op Prop := or.

  #[global] Instance: Monoid_unit Prop := False.

  #[global] Instance: Monoid_unit Prop := True.

  #[global] Program Instance Monoid_disjunction : @Monoid Prop or False.

  #[global] Program Instance Monoid_conjunction : @Monoid Prop and True.

  Solve All Obligations with intros; propext; firstorder.

  (* This won't hold in a non-classical setting *)
  (* #[global] Program Instance Monmor_neg_conj_disj : @Monoid_Morphism Prop Prop and True or False not.
   *)

  #[global] Program Instance Monmor_neg_disj_conj :
    @Monoid_Morphism Prop Prop or False and True not.

  Solve Obligations with intros; propext; firstorder.

End propositional_monoids.
