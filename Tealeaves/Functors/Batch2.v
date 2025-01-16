From Tealeaves Require Import
  Classes.Categorical.Applicative.

Import Applicative.Notations.

(** * The [Batch] idiom *)
(******************************************************************************)
Inductive Batch2 (A1 A2 B1 B2 C : Type) : Type :=
| Done2 : C -> Batch2 A1 A2 B1 B2 C
| StepA : Batch2 A1 A2 B1 B2 (A2 -> C) -> A1 -> Batch2 A1 A2 B1 B2 C
| StepB : Batch2 A1 A2 B1 B2 (B2 -> C) -> B1 -> Batch2 A1 A2 B1 B2 C.

#[global] Arguments Done2 {A1 A2 B1 B2 C}%type_scope _.
#[global] Arguments StepA {A1 A2 B1 B2 C}%type_scope _ _.
#[global] Arguments StepB {A1 A2 B1 B2 C}%type_scope _ _.

(** ** Functor instance *)
(******************************************************************************)

(** *** Map operations *)
(******************************************************************************)
Fixpoint map_Batch2 {A1 A2 B1 B2: Type} {C1 C2: Type} (f : C1 -> C2)
  (b : Batch2 A1 A2 B1 B2 C1): Batch2 A1 A2 B1 B2 C2 :=
  match b with
  | Done2 c => Done2 (f c)
  | StepA mk a => StepA (map_Batch2 (compose f) mk) a
  | StepB mk b => StepB (map_Batch2 (compose f) mk) b
  end.

#[export] Instance Map_Batch2 {A1 A2 B1 B2: Type}: Map (Batch2 A1 A2 B1 B2) :=
  @map_Batch2 A1 A2 B1 B2.

(** ** Applicative instance *)
(******************************************************************************)

(** *** Operations *)
(******************************************************************************)
#[export] Instance Pure_Batch2 {A1 A2 B1 B2}: Pure (@Batch2 A1 A2 B1 B2) :=
  @Done2 A1 A2 B1 B2.

#[program] Fixpoint mult_Batch {A1 A2 B1 B2} {C1 C2: Type}
  (b1 : Batch2 A1 A2 B1 B2 C1)
  (b2 : Batch2 A1 A2 B1 B2 C2):
  Batch2 A1 A2 B1 B2 (C1 * C2) :=
    match b2 with
    | Done2 c2 => map (F := Batch2 A1 A2 B1 B2) (fun (c1 : C1) => (c1, c2)) b1
    | StepA mk a =>
        StepA
          (map (F := Batch2 A1 A2 B1 B2) strength_arrow (mult_Batch b1 mk))
          a
    | StepB mk b =>
        StepB
          (map (F := Batch2 A1 A2 B1 B2) strength_arrow (mult_Batch b1 mk))
          b
    end.

#[export] Instance Mult_Batch2 {A1 A2 B1 B2: Type}:
  Mult (Batch2 A1 A2 B1 B2) :=
  fun C1 C2 => uncurry (@mult_Batch A1 A2 B1 B2 C1 C2).

(** ** The <<runBatch>> operation *)
(******************************************************************************)
Fixpoint runBatch2 {A1 A2 B1 B2: Type}
  (F : Type -> Type) `{Map F} `{Mult F} `{Pure F}
  (ϕB : B1 -> F B2)
  (ϕA : A1 -> F A2)
  {C : Type} (b : Batch2 A1 A2 B1 B2 C) : F C :=
  match b with
  | Done2 c => pure c
  | StepA mk a => runBatch2 F ϕB ϕA (C := A2 -> C) mk <⋆> ϕA a
  | StepB mk b => runBatch2 F ϕB ϕA (C := B2 -> C) mk <⋆> ϕB b
  end.
