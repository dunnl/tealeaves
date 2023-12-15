From Tealeaves Require Export
  Classes.Functor.

#[local] Set Implicit Arguments.
#[local] Generalizable Variables X Y A B F i o.

(** * The [Store] functor *)
(******************************************************************************)
Section fix_parameters.

  Context
    {A B : Type}.

  Inductive Store C : Type :=
  | MkStore : (B -> C) -> A -> Store C.

  Definition map_Store `{f : X -> Y} (c : Store X) : Store Y :=
    match c with
    | MkStore mk a => MkStore (f ∘ mk) a
    end.

  #[export] Instance Map_Batch : Map Store := @map_Store.

  #[export, program] Instance Functor_Batch : Functor Store.

  Solve All Obligations with (intros; now ext [?]).

End fix_parameters.

(** * <<Store>> as a parameterized comonad *)
(******************************************************************************)
Section parameterized.

  #[local] Unset Implicit Arguments.

  Definition extract_Store {A B : Type} (s : @Store A A B) : B :=
    match s with
    | MkStore mk b => mk b
    end.

  Definition cojoin_Store {A C X : Type} (B : Type) (s : @Store A C X) : @Store A B (@Store B C X) :=
    match s with
    | MkStore mk a => MkStore (fun b => MkStore mk b) a
    end.

  Context
    (A B C X : Type).

  Lemma extr_cojoin : `(extract_Store ∘ cojoin_Store A = @id (@Store A B C)).
  Proof.
    intros. now ext [i1 mk].
  Qed.

  Lemma map_extr_cojoin :
    `(map extract_Store ∘ cojoin_Store B = @id (@Store A B C)).
  Proof.
    intros. now ext [i1 mk].
  Qed.

  Lemma cojoin_cojoin : `(cojoin_Store B2 ∘ @cojoin_Store A C X B1 =
                          map (cojoin_Store B1) ∘ cojoin_Store B2).
  Proof.
    intros. now ext [i1 mk].
  Qed.

End parameterized.

(** * A representation lemma *)
(******************************************************************************)
Definition runStore `{Map F} `(f : A -> F B) : forall X, Store X -> F X :=
  fun A '(MkStore mk a) => map mk (f a).

Definition runStore_inv `{Map F} `(run : forall X, @Store A B X -> F X) : A -> F B :=
  fun (a : A) => run B (MkStore id a).

Section representation.

  Context
    `{Functor F}.

  Lemma store_repr1 : forall `(f : i -> F o),
      runStore_inv (runStore f) = f.
  Proof.
    intros. ext i1. cbn. now rewrite (fun_map_id).
  Qed.

  Lemma runStore2 : forall `(ϕ : forall X, @Store A B X -> F X),
      Natural ϕ ->
      runStore (runStore_inv ϕ) = ϕ.
  Proof.
    intros. unfold runStore, runStore_inv.
    ext X [mk a]. compose near (MkStore (@id B) a) on left.
    now rewrite (natural (ϕ := ϕ)).
  Qed.

End representation.
