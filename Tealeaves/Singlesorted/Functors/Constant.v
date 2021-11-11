From Tealeaves Require Export
     Singlesorted.Classes.Monoid
     Singlesorted.Classes.Applicative.

Import Monoid.Notations.
#[local] Open Scope tealeaves_scope.

(** * Constant functor *)
(******************************************************************************)
Inductive Const V (tag : Type) : Type :=
| mkConst : V -> Const V tag.

Arguments mkConst {V tag}%type_scope v : rename.

Definition unconst {V tag} : Const V tag -> V :=
  fun '(mkConst c) => c.

Lemma unconst_mkConst {V A} : forall (v : V), unconst (mkConst (tag := A) v) = v.
Proof.
  now intros.
Qed.

Lemma mkConst_unconst {V A} : forall (x : @Const V A), mkConst (unconst x) = x.
Proof.
  now intros [?].
Qed.

Definition retag {V A B} : Const V A -> Const V B :=
  mkConst ∘ unconst.

Instance Fmap_Const {V} : Fmap (Const V) :=
  fun A B f x => mkConst (unconst x).

Program Instance End_Const {V} : Functor (Const V).

Solve All Obligations with
    (intros; now ext [?]).

#[local] Hint Immediate unconst_mkConst mkConst_unconst : tea_applicative.

Hint Rewrite (@unconst_mkConst) (@mkConst_unconst) : tea_applicative.

Lemma fmap_Const_1 : forall V (A B : Type) (f : A -> B) (x : Const V A),
    unconst (fmap (Const V) f x) = unconst x.
Proof.
  introv. now destruct x.
Qed.

Definition mapConst {A B} (f : A -> B) {C} : Const A C -> Const B C :=
  fun '(mkConst a) => mkConst (f a).

Theorem mapConst_1 {A B} (f : A -> B) {C} (x : Const A C) :
  f (unconst x) = unconst (mapConst f x).
Proof.
  destruct x; cbn. reflexivity.
Qed.

Theorem mapConst_2 {A B} (f : A -> B) {C} :
  f ∘ unconst (tag := C) = unconst ∘ mapConst f.
Proof.
  ext [?]. cbn. apply mapConst_1.
Qed.

(** * Constant applicative functors *)
(******************************************************************************)
Section const_ops.

  Context
    `{Monoid M}.

  #[global] Instance Pure_Const : Pure (Const M) :=
    fun (A : Type) (a : A) => mkConst (tag := A) Ƶ.

  #[global] Instance Mult_Const : Mult (Const M) :=
    fun A B (p : Const M A * Const M B) =>
      mkConst (tag := A * B) (unconst (fst p) ● unconst (snd p)).

  #[global, program] Instance Applicative_Const `{Monoid M} : Applicative (Const M).

  Solve Obligations with
      (intros; unfold transparent tcs in *; cbn; simpl_monoid;
      now auto with tea_applicative).

End const_ops.

Instance ApplicativeMorphism_Monoid `(f : M1 -> M2) `{Monoid_Morphism M1 M2 f} :
  ApplicativeMorphism (Const M1) (Const M2) (@mapConst M1 M2 f).
Proof.
  match goal with H : Monoid_Morphism f |- _ => inversion H end.
  constructor; try typeclasses eauto.
  - introv. destruct x. reflexivity.
  - intros. cbn. rewrite (monmor_unit). reflexivity.
  - intros. destruct x, y. cbn. rewrite (monmor_op). reflexivity.
Qed.
