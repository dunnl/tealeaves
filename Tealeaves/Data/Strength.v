From Tealeaves Require Export
  Data.Product
  Classes.Functor
  Functors.Identity
  Functors.Compose.

Import Product.Notations.

#[local] Generalizable Variables F G A B.

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

  Lemma strength_compose `{Functor F} `{Functor G} : forall (A B : Type),
      strength (A := A) (B := B) (F ∘ G) = fmap F (strength G) ∘ strength F.
  Proof.
    intros. ext [x y]. unfold strength, compose; cbn.
    compose near y.
    now rewrite (fun_fmap_fmap F).
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
  Notation "'σ'":= (strength) : tealeaves_scope.
End Notations.
