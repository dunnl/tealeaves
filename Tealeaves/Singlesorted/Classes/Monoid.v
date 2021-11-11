(** This files defines [Monoid] and [Comonoid] and proves basic instances for these. *)
From Tealeaves Require Import
     Util.Prelude Product.

#[local] Open Scope tealeaves_scope.

(** * Monoids *)

(** ** Operational typeclasses *)
Class Monoid_op (A : Type) := monoid_op : A -> A -> A.
Class Monoid_unit (A : Type) := monoid_unit : A.

Arguments monoid_op {A}%type_scope {Monoid_op}.
Arguments monoid_unit A%type_scope {Monoid_unit}.

(** ** Notations *)
Module Notations.
  Notation "'Ƶ'" := (monoid_unit _) : tealeaves_scope. (* \Zbar *)
  Infix "●" := monoid_op (at level 60) : tealeaves_scope. (* \CIRCLE *)
End Notations.

Import Notations.

(** ** Monoid typeclass *)
Class Monoid (M : Type) {op : Monoid_op M} {unit : Monoid_unit M} :=
  { monoid_assoc : `((x ● y) ● z = x ● (y ● z));
    monoid_id_l : `(x ● Ƶ = x);
    monoid_id_r : `(Ƶ ● x = x); }.

(** ** Moniod Homomorphisms *)
Section monoid_morphism.

  Context
    {A B : Type}
    `{Monoid_op A}
    `{Monoid_unit A}
    `{Monoid_op B}
    `{Monoid_unit B}
    (ϕ : A -> B).

  Class Monoid_Morphism :=
    { monmor_a : Monoid A;
      monmor_b : Monoid B;
      monmor_unit : ϕ Ƶ = Ƶ;
      monmor_op : `(ϕ (a1 ● a2) = ϕ a1 ● ϕ a2); }.

End monoid_morphism.

(** ** Some rudimentary automation *)
Ltac simpl_monoid :=
  try rewrites monoid_id_l;
  try rewrites monoid_id_r;
  try rewrites monoid_assoc.

Tactic Notation "simpl_monoid" "in" ident(H) :=
  try rewrite monoid_id_l in H;
  try rewrite monoid_id_r in H;
  try rewrite monoid_assoc in H.

Tactic Notation "simpl_monoid" "in" "*" :=
  try rewrite monoid_id_l in *;
  try rewrite monoid_id_r in *;
  try rewrite monoid_assoc in *.

(** * Common monoid instances *)

(** ** Cartesian product of monoids *)
Section product_monoid.

  Context `{Monoid A, Monoid B}.

  #[global] Instance Monoid_unit_product : Monoid_unit (A * B) :=
    (Ƶ, Ƶ).

  #[global] Instance Monoid_op_product : Monoid_op (A * B) :=
    fun '(a1, b1) '(a2, b2) => (a1 ● a2, b1 ● b2).

  #[global] Program Instance Monoid_product : Monoid (A * B).

  Solve Obligations with
      (intros; destruct_all_pairs; unfold transparent tcs;
      cbn beta iota; now simpl_monoid).

End product_monoid.

(** ** Propositional monoids *)
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

(** ** Natural numbers with addition *)
Instance Monoid_op_plus : Monoid_op nat := plus.

Instance Monoid_unit_zero : Monoid_unit nat := 0.

Program Instance Monoid_Nat : @Monoid nat Monoid_op_plus Monoid_unit_zero.

Solve Obligations with (intros; unfold transparent tcs; lia).

(** * Comonoids *)

(** ** Operational typeclasses *)
Class Comonoid_Counit A := comonoid_counit : A -> unit.
Class Comonoid_Comult A := comonoid_comult : A -> A * A.
Arguments comonoid_comult {A}%type_scope {Comonoid_Comult}.
Arguments comonoid_counit A%type_scope {Comonoid_Counit}.

(** ** Comonoid typeclass *)
Class Comonoid (A : Type) `{Comonoid_Comult A} `{Comonoid_Counit A} :=
  { comonoid_assoc :
      `(associator (map_fst comonoid_comult (comonoid_comult a)) =
        map_snd comonoid_comult (comonoid_comult a));
    comonoid_id_l :
      `(fst (comonoid_comult a) = a);
    comonoid_id_r :
      `(snd (comonoid_comult a) = a);
  }.

(** ** Duplication comonoid *)
(** Everything is a [Comonoid]. In fact, the duplication comonoid is
    the only one, and the comonoid laws are proved by reflexivity. *)
Definition diagonal {A : Type} := fun a : A => (a, a).

Instance Comonoid_Counit_diagonal A : Comonoid_Counit A := fun _ => tt.
Instance Comonoid_Comult_diagonal A : Comonoid_Comult A := @diagonal A.

#[program] Instance Comonoid_diagonal {A} :
  @Comonoid A (Comonoid_Comult_diagonal A)
            (Comonoid_Counit_diagonal A).
