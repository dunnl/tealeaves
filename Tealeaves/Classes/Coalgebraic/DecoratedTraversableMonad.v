From Tealeaves Require Import
  Classes.Kleisli.Monad (Return, ret)
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Categorical.Applicative
  Functors.Writer
  Functors.Batch.

Import Monoid.Notations.
Import DecoratedTraversableMonad.Notations.
Import Product.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables W T A B.

#[local] Arguments mapfst_Batch {B C}%type_scope {A1 A2}%type_scope f%function_scope b.
#[local] Arguments mapsnd_Batch {A}%type_scope {B1 B2}%type_scope {C}%type_scope f%function_scope b.
#[local] Arguments runBatch {A B}%type_scope {F}%function_scope {H H0 H1} ϕ%function_scope {C}%type_scope b.

(** * Traversable monads as coalgebras *)
(******************************************************************************)
Class ToBatchDM (W : Type) (T : Type -> Type) :=
  toBatchDM : forall A B, T A -> Batch (W * A) (T B) (T B).

#[global] Arguments toBatchDM {W}%type_scope {T}%function_scope {ToBatchDM} {A B}%type_scope _.

Fixpoint cojoin_BatchDM `{Monoid_op W} `{ToBatchDM W T} {A B B' C : Type}
  (b : Batch (W * A) (T B) C) : Batch (W * A) (T B') (Batch (W * B') (T B) C) :=
  match b with
  | Done c => Done (Done c)
  | Step rest (*:Batch (W * A) (T B) (T B -> C)*) (w, a)(*:W*A*) =>
      Step (map (F := Batch (W * A) (T B'))
              (fun (continue : Batch (W * B') (T B) (T B -> C))
                 (t : T B') => continue <⋆> mapfst_Batch (incr w) (toBatchDM t)
              ) (cojoin_BatchDM rest : Batch (W * A) (T B') (Batch (W * B') (T B) (T B -> C))))
        ((w, a) : W * A)
  end.

(** ** Characterizing <<cojoin_BatchDM>> via <<runBatch>> *)
(******************************************************************************)
Section section.

  Context
    `{Monoid W}
    `{ToBatchDM W T}.

  Definition double_batchDM {A B : Type} (C : Type) :
    W * A -> (Batch (W * A) (T B) ∘ Batch (W * B) (T C)) (T C) :=
    fun '(w, a) => (map (F := Batch (W * A) (T B))
                   (mapfst_Batch (incr w) ∘ toBatchDM) ∘ batch (W * A) (T B)) (w, a).

  Lemma cojoin_BatchDM_spec : forall (A B B' : Type),
      (@cojoin_BatchDM W _ T _ A B B') =
        (fun C => runBatch (F := Batch (W * A) (T B') ∘ Batch (W * B') (T B))
          (double_batchDM B)).
  Proof.
    intros. ext C b.
    induction b as [C c | C rest IHrest [w a]].
    - cbn. reflexivity.
    - cbn.
      do 3 compose near ((runBatch (double_batchDM (B := B') B) rest)).
      do 3 rewrite (fun_map_map (F := Batch (W * A) (T B'))).
      rewrite IHrest.
      reflexivity.
  Qed.

  Lemma cojoin_BatchDM_batch : forall (A B C : Type),
      cojoin_BatchDM (B' := B) ∘ batch (W * A) (T C) =
        double_batchDM C.
  Proof.
    intros.
    rewrite (cojoin_BatchDM_spec).
    rewrite (runBatch_batch
               ((Batch (W * A) (T B) ∘
                   Batch (W * B) (T C))) (W * A) (T C)).
    reflexivity.
  Qed.

  #[export] Instance AppMor_cojoin_BatchDM : forall (A B C : Type),
      ApplicativeMorphism (Batch (W * A) (T C)) (Batch (W * A) (T B) ∘ Batch (W * B) (T C))
        (@cojoin_BatchDM W _ T _ A C B).
  Proof.
    intros.
    rewrite (@cojoin_BatchDM_spec A C B).
    apply ApplicativeMorphism_runBatch.
  Qed.

End section.

Class DecoratedTraversableMonad (W : Type) (T : Type -> Type)
  `{Monoid_op W} `{Monoid_unit W} `{Return T} `{ToBatchDM W T} :=
  { dtm_ret : forall (A B : Type),
      toBatchDM ∘ ret (T := T) (A := A) = Step (Done (@id (T B))) ∘ ret (T := (W ×));
    dtm_extract : forall (A : Type),
      extract_Batch ∘ mapfst_Batch (ret ∘ extract (W := (W ×))) ∘ toBatchDM = @id (T A);
    dtm_duplicate : forall (A B C : Type),
      cojoin_BatchDM ∘ toBatchDM (A := A) (B := C) =
        map (F := Batch (W * A) (T B)) (toBatchDM) ∘ toBatchDM;
  }.
