From Tealeaves Require Export
  Classes.Kleisli.TraversableMonad
  Classes.Coalgebraic.TraversableMonad
  Functors.Batch.

Import Kleisli.TraversableMonad.Notations.
Import Batch.Notations.

#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments bindt {U} (T)%function_scope {Bindt} G%function_scope
  {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments traverse (T)%function_scope {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

Import Kleisli.TraversableMonad.DerivedInstances.

(** * Traversals as <<BatchM>> coalgebras *)
(******************************************************************************)
#[export] Instance ToBatchM_Bindt
 (T : Type -> Type) `{Bindt T T}
    : Coalgebraic.TraversableMonad.ToBatchM T :=
  (fun A B => bindt T (Batch A (T B))
             A B (batch (T B) A) : T A -> Batch A (T B) (T B)).

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    (T : Type -> Type)
    `{Kleisli.TraversableMonad.TraversableMonad T}.

  Lemma bindt_to_runBatch (G : Type -> Type)
    `{Applicative G} {A B : Type} (f : A -> G (T B)) :
    bindt T G A B f = runBatch G f (T B) ∘ toBatchM T A B.
  Proof.
    unfold_ops @ToBatchM_Bindt.
    rewrite (ktm_morph (ϕ := runBatch G f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Lemma traverse_to_runBatch (G : Type -> Type)
    `{Applicative G} {A B : Type} (f : A -> G B) :
    traverse T G A B f = runBatch G (map G _ _ (ret T B) ∘ f) (T B) ∘ toBatchM T A B.
  Proof.
    rewrite traverse_to_bindt.
    rewrite (bindt_to_runBatch G).
    reflexivity.
  Qed.

  Corollary map_to_runBatch {A B : Type} (f : A -> B) :
    map T A B f = runBatch (fun A => A) (ret T B ∘ f) (T B) ∘ toBatchM T A B.
  Proof.
    rewrite (map_to_traverse).
    rewrite (traverse_to_runBatch (fun A => A)).
    reflexivity.
  Qed.

  Corollary id_to_runBatch : forall (A : Type),
      id (A := T A) = runBatch (fun A => A) (ret T A) (T A) ∘ toBatchM T A A.
  Proof.
    intros. rewrite <- (trf_traverse_id (T := T)).
    rewrite (traverse_to_runBatch (fun A => A)).
    reflexivity.
  Qed.

End runBatch.

(** ** Naturality of <<toBatch>> *)
(******************************************************************************)
Lemma toBatchM_mapfst (T : Type -> Type)
  `{Kleisli.TraversableMonad.TraversableMonad T}
  {A B : Type} (f : A -> B) {C : Type} :
  toBatchM T B C ∘ map T A B f = mapfst_Batch A B f ∘ toBatchM T A C.
Proof.
  unfold_ops @ToBatchM_Bindt.
  rewrite (bindt_map T (Batch B (T C))).
  rewrite (bindt_to_runBatch T (Batch B (T C))).
  rewrite (bindt_to_runBatch T (Batch A (T C))).
  ext t.
  unfold compose.
  induction (toBatchM T A C t).
  - cbv. reflexivity.
  - do 2 rewrite runBatch_rw2. rewrite IHb.
    now rewrite mapfst_Batch2.
Qed.

(** ** Coalgebra laws *)
(******************************************************************************)
Section to_coalgebraic.

  Context
    (T : Type -> Type)
    `{Kleisli.TraversableMonad.TraversableMonad T}.

  #[local] Arguments extract_Batch {A} (B)%type_scope b.

  Lemma double_BatchM_spec : forall A B C,
      double_BatchM T A B C =
        batch (T C) B ⋆3 batch (T B) A.
  Proof.
    reflexivity.
  Qed.

  Lemma toBatchM_ret_Kleisli : forall A B : Type,
      toBatchM T A B ∘ ret T A = batch (T B) A.
  Proof.
    intros.
    unfold_ops @ToBatchM_Bindt.
    now rewrite (ktm_bindt0 _).
  Qed.

  Lemma toBatchM_extract_Kleisli : forall (A : Type),
      extract_Batch (T A) ∘ mapfst_Batch A (T A) (ret T A) ∘ toBatchM T A A = @id (T A).
  Proof.
    intros.
    reassociate -> on left.
    rewrite <- (toBatchM_mapfst T).
    unfold_ops @ToBatchM_Bindt.
    rewrite (bindt_map T (Batch (T A) (T A))).
    rewrite (ktm_morph (ϕ := extract_Batch)).
    reassociate <- on left.
    rewrite (extract_batch).
    change (id ∘ ?f) with f.
    now rewrite (ktm_bindt1).
  Qed.

  Lemma toBatchM_duplicate_Kleisli : forall (A B C : Type),
      cojoin_BatchM T A C B (T C) ∘ toBatchM T A C =
        map (Batch A (T B)) _ _ (toBatchM T B C) ∘ toBatchM T A B.
  Proof.
    intros.
    unfold_ops @ToBatchM_Bindt.
    change (Batch A (T B) (Batch B (T C) ?x))
      with ((Batch A (T B) ∘ Batch B (T C)) x).
    erewrite (ktm_morph (T := T)
               (G1 := Batch A (T C))
               (G2 := Batch A (T B) ∘ Batch B (T C))
               (ϕ := @cojoin_BatchM T _ A C B)).
    unfold_compose_in_compose.
    rewrite (cojoin_BatchM_batch).
    rewrite (ktm_bindt2 _ _).
    rewrite double_BatchM_spec.
    reflexivity.
    Unshelve.
    eauto with typeclass_instances.
  Qed.

  #[export] Instance Coalgebraic_TraversableMonad_of_Kleisli :
    Coalgebraic.TraversableMonad.TraversableMonad T :=
    {| trfm_ret := toBatchM_ret_Kleisli;
      trfm_extract := toBatchM_extract_Kleisli;
      trfm_duplicate := toBatchM_duplicate_Kleisli;
    |}.

End to_coalgebraic.
