From Tealeaves Require Export
  Classes.Monoid
  Classes.Categorical.Applicative
  Tactics.Debug.

Import Monoid.Notations.

#[local] Generalizable Variables W M N ϕ.

#[local] Arguments map F%function_scope {Map}
  {A B}%type_scope f%function_scope _.

(** * Inductive Definition of the Constant Functor *)
(**********************************************************************)
Inductive Const V (tag: Type): Type :=
| mkConst: V -> Const V tag.

Arguments mkConst {V tag}%type_scope v: rename.

Definition unconst {V tag}: Const V tag -> V :=
  fun '(mkConst c) => c.

Lemma unconst_mkConst {V A}:
  forall (v: V), unconst (mkConst (tag := A) v) = v.
Proof.
  now intros.
Qed.

Lemma mkConst_unconst {V A}:
  forall (x: @Const V A), mkConst (unconst x) = x.
Proof.
  now intros [?].
Qed.

Definition retag {V A B}: Const V A -> Const V B :=
  mkConst ∘ unconst.

#[global] Instance Map_Const {V}: Map (Const V) :=
  fun A B f x => mkConst (unconst x).

#[global, program] Instance End_Const {V}: Functor (Const V).

Solve All Obligations with
  (intros; now ext [?]).

#[local] Hint Immediate unconst_mkConst mkConst_unconst: tea_applicative.

#[global] Hint Rewrite (@unconst_mkConst)
  (@mkConst_unconst): tea_applicative.

Lemma map_Const_1: forall V (A B: Type) (f: A -> B) (x: Const V A),
    unconst (map (Const V) f x) = unconst x.
Proof.
  introv. now destruct x.
Qed.

Definition mapConst {A B} (f: A -> B) {C}: Const A C -> Const B C :=
  fun '(mkConst a) => mkConst (f a).

Theorem mapConst_1 {A B} (f: A -> B) {C} (x: Const A C):
  f (unconst x) = unconst (mapConst f x).
Proof.
  destruct x; cbn. reflexivity.
Qed.

Theorem mapConst_2 {A B} (f: A -> B) {C}:
  f ∘ unconst (tag := C) = unconst ∘ mapConst f.
Proof.
  ext [?]. cbn. apply mapConst_1.
Qed.

(** ** Monoids as Constant Applicative Functors *)
(**********************************************************************)
Section const_ops.

  Context
    `{Monoid M}.

  #[global] Instance Pure_Const: Pure (Const M) :=
    fun (A: Type) (a: A) => mkConst (tag := A) Ƶ.

  #[global] Instance Mult_Const: Mult (Const M) :=
    fun A B (p: Const M A * Const M B) =>
      mkConst (tag := A * B) (unconst (fst p) ● unconst (snd p)).

  #[global, program] Instance Applicative_Const `{Monoid M}:
    Applicative (Const M).

  Solve Obligations with
    (intros; unfold transparent tcs in *; cbn; simpl_monoid;
     now auto with tea_applicative).

End const_ops.

#[global] Instance ApplicativeMorphism_Monoid_Morphism
  `(f: M1 -> M2) `{Monoid M1} `{Monoid M2} `{! Monoid_Morphism M1 M2 f}:
  ApplicativeMorphism (Const M1) (Const M2) (@mapConst M1 M2 f).
Proof.
  match goal with H: Monoid_Morphism _ _ f |- _ => inversion H end.
  constructor; try typeclasses eauto.
  - introv. destruct x. reflexivity.
  - intros. cbn. rewrite monmor_unit. reflexivity.
  - intros. destruct x, y. cbn. rewrite monmor_op. reflexivity.
Qed.

(** * Computational Definition of the Constant Functor *)
(**********************************************************************)
Section constant_functor.

  Definition retag_const {A X Y: Type}:
    const A X -> const A Y := @id A.

  (** First we establish that (const M) is an applicative functor. *)
  Section with_monoid.

    Context
      `{Monoid M}.

    #[global] Instance Map_const: Map (const M) :=
      fun X Y f t => t.

    Theorem map_const_spec: forall {X Y: Type} (f: X -> Y),
        map (const M) f = id.
    Proof.
      reflexivity.
    Qed.

    (** ** Monoids as Constant Applicative Functors *)
    (******************************************************************)
    #[global] Instance Pure_const: Pure (const M) :=
      fun X x => Ƶ.

    #[global] Instance Mult_const: Mult (const M) :=
      fun X Y '(x, y) => x ● y.

    #[global] Instance Applicative_const:
      Applicative (const M).
    Proof.
      constructor; intros; try reflexivity.
      - constructor; reflexivity.
      - cbn. now Monoid.simpl_monoid.
      - cbn. unfold_ops @Pure_const. now Monoid.simpl_monoid.
      - cbn. unfold_ops @Pure_const. now Monoid.simpl_monoid.
      - cbn. unfold_ops @Pure_const. now Monoid.simpl_monoid.
    Qed.

    #[global] Instance ApplicativeMorphism_unconst:
      ApplicativeMorphism (Const M) (const M)
        (fun X => unconst).
    Proof.
      constructor; try typeclasses eauto; reflexivity.
    Qed.

  End with_monoid.

  #[global] Instance ApplicativeMorphism_monoid_morphism
    `{Monoid M} `{Monoid N}
    `{hom: ! Monoid_Morphism M N ϕ }:
    ApplicativeMorphism (const M) (const N) (const ϕ).
  Proof.
    inversion hom.
    constructor; now try typeclasses eauto.
  Qed.


  Lemma map_compose_const {F} `{Functor F} `{M: Type}:
    @Map_compose F (const M) _ _ = @Map_const (F M).
  Proof.
    ext A' B' f' t.
    unfold_ops @Map_compose @Map_const.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  Lemma mult_compose_const {G} `{Applicative G} `{Monoid M}:
    @Mult_compose G (const M) _ _ _ =
      @Mult_const (G M) (Monoid_op_applicative G M).
  Proof.
    ext A' B' [m1 m2].
    reflexivity.
  Qed.

End constant_functor.


(** * Simplification Support *)
(**********************************************************************)

Lemma pure_const_rw: forall {A} {a:A} {M} {unit: Monoid_unit M},
    pure (F := const M) (Pure := @Pure_const _ unit) a = @monoid_unit M unit.
Proof.
  reflexivity.
Qed.

Lemma ap_const_rw:
  forall {M} `{op: Monoid_op M} {A B} (x: const M (A -> B)) (y: const M A),
    ap (const M) x y = (@monoid_op M op x y).
Proof.
  Set Printing All.
  intros.
  reflexivity.
Qed.

Lemma map_const_rw: forall A B (f: A -> B) X,
    map (const X) f = @id X.
Proof.
  reflexivity.
Qed.


(** ** Constant applicatives *)
(**********************************************************************)
Ltac simplify_applicative_const :=
  ltac_trace "simplify_applicative_const";
  match goal with
  | |- context [pure (F := const ?W) ?x] =>
      rewrite pure_const_rw
  | |- context[(ap (const ?W) ?x ?y)] =>
      rewrite ap_const_rw
  end.

Ltac simplify_applicative_const_in :=
  match goal with
  | H: context [pure (F := const ?W) ?x] |- _ =>
      rewrite pure_const_rw in H
  | H: context[(ap (const ?W) ?x ?y)] |- _ =>
      rewrite ap_const_rw in H
  end.

(** ** Constant maps *)
(**********************************************************************)
Ltac simplify_map_const :=
  ltac_trace "simplify_map_const";
  match goal with
  | |- context[map (const ?X) ?f] =>
      rewrite map_const_rw
  end.

Ltac simplify_map_const_in :=
  match goal with
  | H: context[map (const ?X) ?f] |- _ =>
      rewrite map_const_rw in H
  end.
