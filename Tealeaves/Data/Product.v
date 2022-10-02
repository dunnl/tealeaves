From Tealeaves Require Export
  Util.Prelude.

(** This file defines the monoidal-category-theoretic structure on the
    category of types and functions given by the Cartesian product
    [prod]. It supplies generally useful definitions like [copy] and
    [map_snd] related to the product functor. *)

#[local] Generalizable All Variables.

(** * Monoidal category-theoretic structure on types *)
(******************************************************************************)

(** ** Reassociating products *)
(******************************************************************************)
Section associator.

  Context
    {X Y Z W : Type}.

  (* Recall Coq's notation "_ * _" associates to the left. *)
  Definition associator : (X * Y) * Z -> X * (Y * Z) :=
    fun p => match p with
             | ((x, y), z) => (x, (y, z))
             end.

  Definition associator_inv : (X * (Y * Z)) -> (X * Y) * Z :=
    fun p => match p with
             | (x, (y, z)) => ((x, y), z)
             end.

  Theorem associator_iso_1 :
      associator_inv ∘ associator = id.
  Proof.
    now ext [[? ?] ?].
  Qed.

  Theorem associator_iso_2 :
    associator ∘ associator_inv = id.
  Proof.
    now ext [? [? ?]].
  Qed.

End associator.

(** ** Notations *)
(******************************************************************************)
Module Notations.
  Notation "'α'" := (associator) : tealeaves_scope.
  Notation "'α^-1'" := (associator_inv) : tealeaves_scope.
  Notation "( X  × )" := (prod X) (only parsing): function_scope.
End Notations.

Import Notations.

(** ** Monoidal category theory laws *)
(******************************************************************************)
Definition map_tensor `(f : X -> Z) `(g : Y -> W) `(p : X * Y) : Z * W :=
  match p with
  | (x, y) => (f x, g y)
  end.

Definition map_fst {Y} `(f : X -> Z) : X * Y -> Z * Y :=
  map_tensor f id.

Definition map_snd {X} `(f : Y -> W) : X * Y -> X * W :=
  map_tensor id f.

Definition map_both `(f : X -> Z) : X * X -> Z * Z :=
  map_tensor f f.

Definition left_unitor {X} : unit * X -> X := snd.

Definition left_unitor_inv {X} : X -> unit * X := pair tt.

Definition right_unitor {X} : (X * unit) -> X := fst.

Definition right_unitor_inv {X} : X -> X * unit := fun x => (x, tt).

Theorem unitors_1 : forall A, left_unitor_inv ∘ left_unitor = @id (unit * A).
Proof.
  introv; now ext [[] ?].
Qed.

Theorem unitors_2 : forall A, left_unitor ∘ left_unitor_inv = @id A.
Proof.
  introv. now ext a.
Qed.

Theorem unitors_3 : forall A, right_unitor_inv ∘ right_unitor = @id (A * unit).
Proof.
  introv; now ext [? []].
Qed.

Theorem unitors_4 : forall A, right_unitor ∘ right_unitor_inv = @id A.
Proof.
  introv; now ext a.
Qed.

Theorem triangle {X Y} :
    map_fst (X := X * unit) (Y := Y) right_unitor = map_snd left_unitor ∘ α.
Proof.
  now ext [[? ?] ?].
Qed.

Theorem pentagon {X Y Z W} :
  map_snd α ∘ α ∘ map_fst (Y := W) (@associator X Y Z) = α ∘ α.
Proof.
  now ext [[[? ?] ?] ?].
Qed.

Definition braiding {X Y : Type} : X * Y -> Y * X :=
  fun p => match p with
           | (x, y) => (y, x)
           end.

Theorem braiding_symmetry {X Y} :
    braiding ∘ braiding = @id (X * Y).
Proof.
  now ext [? ?].
Qed.

(** ** Currying and uncurrying *)
(******************************************************************************)
Definition uncurry {X Y Z} : (X -> Y -> Z) -> (X * Y -> Z) :=
  fun f p => let '(x, y) := p in f x y.

Definition curry {X Y Z} : (X * Y -> Z) -> (X -> Y -> Z) :=
  fun f x y => f (x, y).

Lemma curry_iso {X Y Z} : forall (f : X -> Y -> Z),
    f = curry (uncurry f).
Proof.
  now intros.
Qed.

Lemma curry_iso_inv {X Y Z} : forall (f : X * Y -> Z),
    f = uncurry (curry f).
Proof.
  intros. now ext [? ?].
Qed.

(** ** Deletions (projections) *)
(******************************************************************************)
Lemma product_delete_l {X Y Z} : forall (f : X -> Z) (p : X * Y),
    snd (map_fst f p) = snd p.
Proof.
  now intros ? [? ?].
Qed.

Lemma product_delete_r {X Y W} : forall (f : Y -> W) (p : X * Y),
    fst (map_snd f p) = fst p.
Proof.
  now intros ? [? ?].
Qed.

Lemma snd_map_snd {X Y Z} : forall (f : Y -> Z) (p : X * Y),
    snd (map_snd f p) = f (snd p).
Proof.
  now intros ? [? ?].
Qed.

Lemma fst_map_fst {X Y W} : forall (f : X -> W) (p : X * Y),
    fst (map_fst f p) = f (fst p).
Proof.
  now intros ? [? ?].
Qed.

(** ** Miscellaneous *)
(******************************************************************************)
Definition swap_middle {X Y Z W} : (X * Y) * (Z * W) -> (X * Z) * (Y * W) :=
  fun p =>
    associator_inv
      (map_snd associator
               (map_snd (map_fst braiding)
                        (map_snd associator_inv
                                 (associator p)))).

Lemma product_map_slide {X Y Z W} : forall (f : X -> Z) (g : Y -> W) (p : X * Y),
    map_fst f (map_snd g p) = map_snd g (map_fst f p).
Proof.
  now intros ? ? [? ?].
Qed.

Definition dup_left {A B} : A * B -> A * (A * B) :=
  fun '(a, b) => (a, (a, b)).
