From Tealeaves Require Export
  Misc.Product
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

  Definition strength {F : Type -> Type}
    `{Map F} {A B} : forall (p : A * F B), F (A * B) :=
    fun '(a, t) => map (pair a) t.

  Lemma strength_I : forall (A B : Type), @strength (fun A : Type => A) _ A B = @id (A * B).
  Proof.
    intros. now ext [a b].
  Qed.

  Lemma strength_compose `{Functor F} `{Functor G} : forall (A B : Type),
      strength (F := F ∘ G) (A := A) (B := B) =
        map (F := F) (strength (F := G)) ∘ strength (F := F).
  Proof.
    intros. ext [x y]. unfold strength, compose; cbn.
    compose near y.
    now rewrite (fun_map_map).
  Qed.

  Context
    (F : Type -> Type)
    `{Functor F}.

  Lemma strength_1 {A B} : forall (a : A) (x : F B),
      strength (a, x) = map (pair a) x.
  Proof.
    reflexivity.
  Qed.

  Lemma strength_2 {A B} : forall (a : A),
      (strength ∘ pair a : F B -> F (A * B)) = map (pair a).
  Proof.
    reflexivity.
  Qed.

  Lemma strength_nat `{f : A1 -> B1} `{g : A2 -> B2} : forall (p : A1 * F A2),
      strength (map_tensor f (map g) p) = map (map_tensor f g) (strength p).
  Proof.
    intros [a t]. cbn.
    compose near t on left.
    compose near t on right.
    now rewrite 2(fun_map_map).
  Qed.

  Corollary strength_nat_l {A B C} {f : A -> B} : forall (p : A * F C),
      map (map_fst f) (strength p) = strength (map_fst f p).
  Proof.
    intros. unfold map_fst.
    rewrite <- strength_nat.
    now rewrite (fun_map_id).
  Qed.

  Corollary strength_nat_r {A B C} {f : A -> B} : forall (p : C * F A),
      map (map_snd f) (strength p) = strength (map_snd (map f) p).
  Proof.
    intros. unfold map_snd.
    now rewrite <- strength_nat.
  Qed.

  Lemma strength_triangle {A} : forall (p : unit * F A),
      map left_unitor (strength p) = left_unitor p.
  Proof.
    intros [u t]. destruct u. cbn.
    compose_near t. rewrite (fun_map_map).
    now rewrite (fun_map_id).
  Qed.

  Lemma strength_assoc {A B C} :
    map α ∘ (@strength F _ (A * B) C) = strength ∘ map_snd strength ∘ α.
  Proof.
    ext [[? ?] t]. unfold strength, compose. cbn.
    compose_near t. do 2 rewrite (fun_map_map).
    reflexivity.

  Qed.

End tensor_strength.

(** * Notations *)
(******************************************************************************)
Module Notations.
  (* This line has the effect that we can pass implicit arguments explicitly (e.g. <<σ (F := T)>> *)
  #[local] Arguments strength F%function_scope {H} (A B)%type_scope _.
  Notation "'σ'":= (strength) : tealeaves_scope.
End Notations.
