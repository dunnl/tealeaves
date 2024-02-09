From Tealeaves Require Import
  Classes.Kleisli.Monad (Return, ret)
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Categorical.Applicative
  Functors.Writer
  Functors.Batch.

Import Batch.Notations.
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
Class ToBatch7 (W : Type) (T : Type -> Type) :=
  toBatch7 : forall A B, T A -> Batch (W * A) (T B) (T B).

#[global] Arguments toBatch7 {W}%type_scope {T}%function_scope {ToBatch7} {A B}%type_scope _.

Section cojoin.

  Context
    {W : Type}
    {T : Type -> Type}
    `{Monoid_op W}
    `{ToBatch7 W T}.

  Context
    {A : Type} (* original leaves *)
    {A' : Type} (* new leaves *)
    {A'' : Type}. (* new type of new leaves *)

  Section auxiliary.

    Context {R : Type}.

    Definition cojoin_Type :=
      Batch (W * A) (T A') R ->
      Batch (W * A) (T A'') (Batch (W * A'') (T A') R).

    (* Batch (W * A) (T A') (T A' -> R) -> (* continuation *) *)
    (* Batch (W * A) (T A'') (Batch (W * A'') (T A'') (T A' -> Batch (W * A'') (T A') R)) (* return of cojoin *)
     *)

    Definition key_function (w : W) :
      Batch (W * A'') (T A') (T A' -> R) ->
      T A'' ->
      Batch (W * A'') (T A') R :=
      fun next_batch t =>
        next_batch <⋆> mapfst_Batch (incr w) (toBatch7 (B := A') t).

    Definition cojoin_Batch7_leaf_case :
      Batch (W * A) (T A'') (Batch (W * A'') (T A') (T A' -> R)) -> (* recursive call on cojoin of continuation *)
      W * A -> (* leaf in context *)
      Batch (W * A) (T A'') (T A'' -> Batch (W * A'') (T A') R) := (* new continuation *)
      fun rec_continue '(w, a) =>
        map (F := Batch (W * A) (T A'')) (key_function w) rec_continue.

  End auxiliary.

  Fixpoint cojoin_Batch7 {R : Type}
    (b : Batch (W * A) (T A') R) : Batch (W * A) (T A'') (Batch (W * A'') (T A') R) :=
    match b with
    | Done c => Done (Done c)
    | Step continuation (w, a) =>
        let new_continuation := cojoin_Batch7_leaf_case (cojoin_Batch7 (R := T A' -> R) continuation) (w, a)
        in Step new_continuation (w, a)
    end.

End cojoin.

(** ** Characterizing <<cojoin_BatchDM>> via <<runBatch>> *)
(******************************************************************************)
Section section.

  Context
    `{Monoid W}
    `{ToBatch7 W T}.

  Definition double_batch7 {A A' : Type} {R : Type} :
    W * A -> Batch (W * A) (T A') (Batch (W * A') (T R) (T R)) :=
    fun '(w, a) =>
      (map (F := Batch (W * A) (T A'))
         (mapfst_Batch (incr w) ∘ toBatch7) ∘ batch (W * A) (T A')) (w, a).

  Lemma double_batch7_rw {A A' : Type} {R : Type} :
    forall '(w, a),
      double_batch7 (A := A) (A' := A') (R := R) (w, a) =
        Done (mapfst_Batch (incr w) ∘ toBatch7) ⧆ (w, a).
  Proof.
    intros [w a].
    reflexivity.
  Qed.

  Lemma cojoin_Batch7_to_runBatch : forall (A A' A'' : Type) (R : Type),
      cojoin_Batch7 (A := A) (A' := A') (A'' := A'') (R := R) =
        runBatch (F := Batch (W * A) (T A'') ∘ Batch (W * A'') (T A'))
          double_batch7.
  Proof.
    intros. ext b.
    induction b as [R r | R continuation IHcontinuation [w a]].
    - cbn. reflexivity.
    - cbn.
      do 3 compose near
        (runBatch
           (F := Batch (W * A) (T A'') ∘ Batch (W * A'') (T A'))
           double_batch7
           continuation).
      do 3 rewrite (fun_map_map (F := Batch (W * A) (T A''))).
      rewrite IHcontinuation.
      reflexivity.
  Qed.

  Lemma cojoin_Batch7_batch : forall (A A' R : Type),
      cojoin_Batch7 (A'' := A') ∘ batch (W * A) (T R) = double_batch7.
  Proof.
    intros.
    rewrite cojoin_Batch7_to_runBatch.
    rewrite (runBatch_batch (Batch (prod W A) (T A') ∘ Batch (prod W A') (T R))).
    reflexivity.
  Qed.

  #[export] Instance AppMor_cojoin_Batch7 : forall (A A' A'' : Type),
      ApplicativeMorphism
        (Batch (W * A) (T A'))
        (Batch (W * A) (T A'') ∘ Batch (W * A'') (T A'))
        (@cojoin_Batch7 W T _ _ A A' A'').
  Proof.
    intros.
    assert (lemma :
             @cojoin_Batch7 W T op H0 A A' A'' =
               fun R => runBatch (F := Batch (W * A) (T A'') ∘ Batch (W * A'') (T A')) double_batch7).
    { ext R. now rewrite cojoin_Batch7_to_runBatch. }
    rewrite lemma.
    apply ApplicativeMorphism_runBatch.
  Qed.

End section.

Class DecoratedTraversableMonad (W : Type) (T : Type -> Type)
  `{Monoid_op W} `{Monoid_unit W} `{Return T} `{ToBatch7 W T} :=
  { dtm_monoid :> Monoid W;
    dtm_ret : forall (A B : Type),
      toBatch7 ∘ ret (T := T) (A := A) = Step (Done (@id (T B))) ∘ ret (T := (W ×));
    dtm_extract : forall (A : Type),
      extract_Batch ∘ mapfst_Batch (ret ∘ extract (W := (W ×))) ∘ toBatch7 = @id (T A);
    dtm_duplicate : forall (A B C : Type),
      cojoin_Batch7 ∘ toBatch7 (A := A) (B := C) =
        map (F := Batch (W * A) (T B)) (toBatch7) ∘ toBatch7;
  }.
