From Tealeaves Require Import
  Classes.Kleisli.Monad (Return, ret)
  Classes.Kleisli.DecTravMonad
  Classes.Categorical.Applicative
  Functors.Writer
  Functors.Batch.

Import Monoid.Notations.
Import DecTravMonad.Notations.
Import Product.Notations.
Import Applicative.Notations.

#[local] Arguments Done : clear implicits.
#[local] Arguments Step : clear implicits.

(** * Traversable monads as coalgebras *)
(******************************************************************************)
Class ToBatchDM (W : Type) (T : Type -> Type) :=
  toBatchDM : forall A B, T A -> Batch (W * A) (T B) (T B).

#[global] Arguments toBatchDM (W)%type_scope (T)%function_scope
  {ToBatchDM} (A B)%type_scope _.

Fixpoint cojoin_BatchDM (W : Type) (T : Type -> Type) `{Monoid_op W} `{ToBatchDM W T} (A B B' C : Type)
  (b : Batch (W * A) (T B) C) : Batch (W * A) (T B') (Batch (W * B') (T B) C) :=
  match b with
  | Done _ _ _ c => Done (W * A) (T B') (Batch (W * B') (T B) C) (Done (W * B') (T B) C c)
  | Step _ _ _ rest (*:Batch (W * A) (T B) (T B -> C)*) (w, a)(*:W*A*) =>
      Step (W * A) (T B') (Batch (W * B') (T B) C)
        (map (Batch (W * A) (T B'))
           (fun (x : Batch (W * B') (T B) (T B -> C)) (t : T B') =>
              x <⋆> (mapfst_Batch (W * B') (W * B') (incr w)
                       (toBatchDM W T B' B t : Batch (W * B') (T B) (T B)))
           )
           (cojoin_BatchDM W T A B B' (T B -> C) rest))
        ((w, a) : W * A)
  end.

Section section.

  Context
    W T
      `{Monoid W}
      `{ToBatchDM W T}.

  Definition new_double_batch (A B C : Type) :
    W * A -> (Batch (W * A) (T B) ∘ Batch (W * B) (T C)) (T C) :=
    fun '(w, a) => (map (Batch (W * A) (T B))
                   (mapfst_Batch (W * B) (W * B) (incr w) ∘ toBatchDM W T B C)
                   ∘ batch (T B) (W * A)) (w, a).

  Lemma cojoin_Batch_rw0 : forall (A B B' C : Type),
      @cojoin_BatchDM W T _ _ A B B' C =
        runBatch (Batch (W * A) (T B') ∘ Batch (W * B') (T B)) (new_double_batch A B' B) C.
  Proof.
    intros. ext b.
    induction b as [C c | C rest IHrest [w a]].
    - cbn. reflexivity.
    - cbn.
      compose near ((runBatch (Batch (W * A) (T B') ∘ Batch (W * B') (T B)) (new_double_batch A B' B) (T B -> C) rest)).
      rewrite (fun_map_map (F := Batch (W*A)(T B'))).
      compose near ((runBatch (Batch (W * A) (T B') ∘ Batch (W * B') (T B)) (new_double_batch A B' B) (T B -> C) rest)).
      rewrite (fun_map_map (F := Batch (W*A)(T B'))).
      compose near ((runBatch (Batch (W * A) (T B') ∘ Batch (W * B') (T B)) (new_double_batch A B' B) (T B -> C) rest)).
      rewrite (fun_map_map (F := Batch (W*A)(T B'))).
      fequal. fequal.
      apply IHrest.
  Qed.
End section.

Class DecoratedTraversableMonad (W : Type) `{Monoid W}
  (T : Type -> Type) `{Return T} `{ToBatchDM W T} :=
  { dtm_ret : forall (A B : Type),
      toBatchDM W T A B ∘ ret T A = Step (W * A) (T B) (T B) (Done _ _ _ (@id (T B))) ∘ ret (W ×) A;
    dtm_extract : forall (A : Type),
      extract_Batch ∘ mapfst_Batch (W * A) (T A) (ret T A ∘ extract (W ×) A) ∘ toBatchDM W T A A = @id (T A);
    dtm_duplicate : forall (A B C : Type),
      cojoin_BatchDM W T A C B (T C) ∘ toBatchDM W T A C =
        map (Batch (W * A) (T B)) (toBatchDM W T B C) ∘ toBatchDM W T A B;
  }.
