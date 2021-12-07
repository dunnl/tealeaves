(** This file implements the ordinary endofunctors of functional programming. *)

From Tealeaves Require Export
     Util.Prelude
     Util.Product.

Import Product.Notations.
#[local] Open Scope tealeaves_scope.

#[local] Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.

(** * Endofunctors *)
(******************************************************************************)
Section Functor_operations.

  Context
    (F : Type -> Type).

  Class Fmap : Type :=
    fmap : forall {A B : Type} (f : A -> B), F A -> F B.

End Functor_operations.

Section Functor_class.

  Context
    (F : Type -> Type)
    `{Fmap F}.

  Class Functor : Prop :=
    { fun_fmap_id :
        `(fmap F (@id A) = @id (F A));
      fun_fmap_fmap : forall {A B C : Type} {f : A -> B} {g : B -> C},
          fmap F g ∘ fmap F f = fmap F (g ∘ f);
    }.

End Functor_class.

(** ** Natural transformations *)
(******************************************************************************)
Section natural_transformation_class.

  Context
    `{Functor F}
    `{Functor G}.

  Class Natural (ϕ : F ⇒ G) :=
    { natural_src : Functor F;
      natural_tgt : Functor G;
      natural : forall `(f : A -> B),
          fmap G f ∘ ϕ A = ϕ B ∘ fmap F f
    }.

End natural_transformation_class.

(** ** Monoid structure on endofunctors *)
(** Before defining [Monad] it is necessary to define the monoidal
    structure on endofunctors, i.e. to prove the identity operation is
    an endofunctor and that these are closed under composition. It is
    not necessary here to prove the full monoid laws. *)
(******************************************************************************)
Instance Fmap_I : Fmap (fun A => A) :=
  fun (A B : Type) (f : A -> B) => f.

#[program] Instance Functor_I : Functor (fun A => A).

(** It is sometimes necessary to explicitly unfold
<<compose>> in the type arguments of a <<compose>> in order to rewrite
with naturality laws without using <<Set Keyed Unification>>. *)
Ltac unfold_compose_in_compose :=
  repeat match goal with
         | |- context [@compose ?A ?B ?C] =>
           let A' := eval unfold compose in A in
               let B' := eval unfold compose in B in
                   let C' := eval unfold compose in C in
                       progress (change (@compose A B C) with (@compose A' B' C'))
         end.

Section Functor_composition.

  Context
    `{Functor F}
    `{Functor G}.

  #[global] Instance Fmap_compose : Fmap (G ∘ F) :=
    fun A B f => fmap G (fmap F f).

  #[global] Program Instance Functor_compose : Functor (G ∘ F).

  Solve Obligations with
      (intros; unfold transparent tcs;
      unfold_compose_in_compose;
      (rewrite (fun_fmap_id F), (fun_fmap_id G)) +
      (rewrite (fun_fmap_fmap G), (fun_fmap_fmap F));
      reflexivity).

End Functor_composition.

(** * Tensorial strength *)
(** All endofunctors in the CoC have a tensorial strength with respect
    to the Cartesian product of types. This is just the operation
    that distributes a pairing over an endofunctor. See *)
(** # <a href="https://ncatlab.org/nlab/show/tensorial+strength">https://ncatlab.org/nlab/show/tensorial+strength</a># *)
(******************************************************************************)
Section tensor_strength.

  Definition strength (F : Type -> Type) `{Fmap F} {A B} : forall (p : A * F B), F (A * B) :=
    fun '(a, t) => fmap F (pair a) t.

  Lemma strength_I : forall (A B : Type), strength (fun A : Type => A) = @id (A * B).
  Proof.
    intros. now ext [a b].
  Qed.

  Context
    (F : Type -> Type)
    `{Functor F}.

  Lemma strength_1 {A B} : forall (a : A) (x : F B),
      strength F (a, x) = fmap F (pair a) x.
  Proof.
    reflexivity.
  Qed.

  Lemma strength_2 {A B} : forall (a : A),
      (strength F ∘ pair a : F B -> F (A * B)) = fmap F (pair a).
  Proof.
    reflexivity.
  Qed.

  Lemma strength_nat `{f : A1 -> B1} `{g : A2 -> B2} : forall (p : A1 * F A2),
      strength F (map_tensor f (fmap F g) p) = fmap F (map_tensor f g) (strength F p).
  Proof.
    intros [a t]. cbn.
    compose near t on left.
    compose near t on right.
    now rewrite 2(fun_fmap_fmap F).
  Qed.

  Corollary strength_nat_l {A B C} {f : A -> B} : forall (p : A * F C),
      fmap F (map_fst f) (strength F p) = strength F (map_fst f p).
  Proof.
    intros. unfold map_fst.
    rewrite <- strength_nat.
    now rewrite (fun_fmap_id F).
  Qed.

  Corollary strength_nat_r {A B C} {f : A -> B} : forall (p : C * F A),
      fmap F (map_snd f) (strength F p) = strength F (map_snd (fmap F f) p).
  Proof.
    intros. unfold map_snd.
    now rewrite <- strength_nat.
  Qed.

  Lemma strength_triangle {A} : forall (p : unit * F A),
      fmap F (left_unitor) (strength F p) = left_unitor p.
  Proof.
    intros [u t]. destruct u. cbn.
    compose_near t. rewrite (fun_fmap_fmap F).
    now rewrite (fun_fmap_id F).
  Qed.

  Lemma strength_assoc {A B C} :
    fmap F α ∘ (@strength F _ (A * B) C) = strength F ∘ map_snd (strength F) ∘ α.
  Proof.
    ext [[? ?] t]. unfold strength, compose. cbn.
    compose_near t. do 2 rewrite (fun_fmap_fmap F).
    reflexivity.
  Qed.

End tensor_strength.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Notation "F ⇒ G" := (forall A : Type, F A -> G A) (at level 50) : tealeaves_scope.
  Notation "'σ'":= (strength) : tealeaves_scope.
End Notations.
