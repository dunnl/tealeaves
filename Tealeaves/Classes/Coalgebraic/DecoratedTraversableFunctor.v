From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Categorical.Monad (Return, ret)
  Classes.Categorical.Comonad (Extract, extract)
  Functors.Early.Batch
  Functors.Early.Reader.

Import Batch.Notations.
Import Product.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables E T A B.

(** * Coalgebraic Decorated Traversable Functors *)
(**********************************************************************)

(** ** The <<toBatch3>> Operation *)
(**********************************************************************)
Class ToBatch3 (E: Type) (T: Type -> Type) :=
  toBatch3: forall A B, T A -> Batch (E * A) B (T B).

#[global] Arguments toBatch3 {E}%type_scope {T}%function_scope
  {ToBatch3} {A B}%type_scope _.

(** ** Operation <<cojoin_Batch3>> *)
(**********************************************************************)
Fixpoint cojoin_Batch3 `{ToBatch3 E T} {A B B' C: Type}
  (b: Batch (E * A) B C): Batch (E * A) B' (Batch (E * B') B C) :=
  match b with
  | Done c => Done (Done c)
  | Step rest (*:Batch (E * A) B (B -> C)*) (e, a)(*:E*A*) =>
      Step (map (F := Batch (E * A) B')
              (fun (continue: Batch (E * B') B (B -> C))
                 (b': B') =>
                 Step continue (e, b')
              ) (cojoin_Batch3 rest:
                Batch (E * A) B' (Batch (E * B') B (B -> C))))
        ((e, a): E * A)
  end.

(** ** <<cojoin_Batch3>> as <<runBatch double_batch3>> *)
(**********************************************************************)
Section section.

  Context
    `{ToBatch3 E T}.

  Definition double_batch3 {A B: Type} (C: Type):
    E * A -> (Batch (E * A) B ∘ Batch (E * B) C) C :=
    fun '(e, a) => (map (F := Batch (E * A) B)
                   (batch (E * B) C ∘ pair e) ∘ batch (E * A) B) (e, a).

  Lemma double_batch3_rw {A B C: Type}:
    forall '(e, a),
      @double_batch3 A B C (e, a) =
        Done (batch (E * B) C ∘ pair e) ⧆ (e, a).
  Proof.
    intros [e a].
    reflexivity.
  Qed.

  Lemma cojoin_Batch3_to_runBatch: forall (A B B': Type),
      (@cojoin_Batch3 E T _ A B B') =
        (fun C => runBatch (G := Batch (E * A) B' ∘ Batch (E * B') _)
                 (double_batch3 B)).
  Proof.
    intros. ext C b.
    induction b as [C c | C rest IHrest [e a]].
    - cbn. reflexivity.
    - cbn.
      do 3 compose near ((runBatch (double_batch3 (B := B') B) rest)).
      do 3 rewrite (fun_map_map (F := Batch (E * A) B')).
      fequal.
      rewrite IHrest.
      fequal.
      ext b x. unfold compose.
      cbn.
      compose near b.
      rewrite (fun_map_map).
      compose near b.
      rewrite (fun_map_map).
      fequal.
      unfold compose, strength_arrow.
      rewrite (fun_map_id).
      reflexivity.
  Qed.

  Lemma cojoin_Batch3_batch: forall (A B C: Type),
      cojoin_Batch3 (B' := B) ∘ batch (E * A) C =
        double_batch3 C.
  Proof.
    intros.
    rewrite (cojoin_Batch3_to_runBatch).
    pose (runBatch_batch).
    specialize (e ((Batch (E * A) B ∘ Batch (E * B) C))
                  _ _ _ _).
    specialize (e (E * A) C).
    specialize (e (double_batch3 C)).
    apply e.
  Qed.

  #[export] Instance ApplicativeMorphism_cojoin_Batch3:
    forall (A B C: Type),
      ApplicativeMorphism (Batch (E * A) C)
        (Batch (E * A) B ∘ Batch (E * B) C)
        (@cojoin_Batch3 E _ _ A C B).
  Proof.
    intros.
    rewrite (@cojoin_Batch3_to_runBatch A C B).
    apply ApplicativeMorphism_runBatch.
  Qed.

End section.

(** ** Typeclass *)
(**********************************************************************)
Class DecoratedTraversableFunctor
  (E: Type)
  (T: Type -> Type)
  `{ToBatch3 E T} :=
  { dtf_extract: forall (A: Type),
      extract_Batch ∘ mapfst_Batch (extract (W := (E ×))) ∘
        toBatch3 = @id (T A);
    dtf_duplicate: forall (A B C: Type),
      cojoin_Batch3 ∘ toBatch3 (A := A) (B := C) =
        map (F := Batch (E * A) B) (toBatch3) ∘ toBatch3;
  }.
