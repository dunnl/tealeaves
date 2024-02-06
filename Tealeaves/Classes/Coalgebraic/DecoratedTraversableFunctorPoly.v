From Tealeaves.Classes Require Export
  Monoid
  Categorical.Applicative
  Categorical.Monad
  Kleisli.TraversableFunctor.

From Tealeaves.Functors Require Export
  Constant
  Writer
  List.

Import Monoid.Notations.
Import Applicative.Notations.
Import TraversableFunctor.Notations.
Import Product.Notations.

#[local] Generalizable Variables ψ ϕ W WA WB F G M A B C D X Y O.

#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.

(** * The [DFS] idiom *)
(******************************************************************************)
Section DFS.

  Variables (B B' A A' : Type).

  Inductive DFS (R : Type) : Type :=
  | Done : R -> DFS R
  | Bin  : DFS (B' -> R) -> B -> DFS R
  | Leaf : DFS (A' -> R) -> A -> DFS R.

  Context
    (F : Type -> Type) `{Map F} `{Mult F} `{Pure F}.

  Program Fixpoint runDFS
    (ϕB : B  -> F B')
    (ϕA : A  -> F A')
    (R : Type)
    (d : DFS R) :
    F R :=
  match d with
  | Done _ r => pure r
  | Bin _ k b =>
      runDFS ϕB ϕA (B' -> R) k <⋆> ϕB b
  | Leaf _ k a =>
      runDFS ϕB ϕA (A' -> R) k <⋆> ϕA a
  end.

End DFS.

#[global] Arguments Done {B B' A A' R}%type_scope _.
#[global] Arguments Bin  {B B' A A' R}%type_scope _.
#[global] Arguments Leaf {B B' A A' R}%type_scope _ _.

(** ** Functor instances *)
(******************************************************************************)

(** *** Map operations *)
(******************************************************************************)
Fixpoint map_DFS {WA WB A B C1 C2 : Type} (f : C1 -> C2)
  (d : DFS WA WB A B C1) : DFS WA WB A B C2 :=
  match d with
  | Done c => Done (f c)
  | Bin rest wa => Bin (map_DFS (compose f) rest) wa
  | Leaf rest a => Leaf (map_DFS (compose f) rest) a
  end.

#[export] Instance Map_Batch {WA WB A B : Type} :
  Map (DFS WA WB A B) := @map_DFS WA WB A B.

Fixpoint mapfst_DFS {WA1 WA2 WB A1 A2 B C : Type} (r : WA1 -> WA2) (f : A1 -> A2)
  (d : DFS WA1 WB A1 B C) : DFS WA2 WB A2 B C :=
  match d with
  | Done c => Done c
  | Bin rest wa => Bin (mapfst_DFS r f rest) (r wa)
  | Leaf rest a => Leaf (mapfst_DFS r f rest) (f a)
  end.

Fixpoint mapsnd_DFS {WA WB1 WB2 A B1 B2 C : Type} (r : WB1 -> WB2) (f : B1 -> B2)
  (d : DFS WA WB2 A B2 C) : DFS WA WB1 A B1 C :=
  match d with
  | Done c => Done c
  | Bin rest wa => Bin (map_DFS (precompose r) (mapsnd_DFS r f rest)) wa
  | Leaf rest a => Leaf (map_DFS (precompose f) (mapsnd_DFS r f rest)) a
  end.


(*
(** *** Rewriting principles *)
(******************************************************************************)
Lemma map_Batch_rw1 {A B C1 C2 : Type} `(f : C1 -> C2) (c : C1) :
  map (Batch A B) f (Done A B C1 c) = Done A B C2 (f c).
Proof.
  reflexivity.
Qed.

Lemma map_Batch_rw2 {A B C1 C2 : Type} `(f : C1 -> C2) (a : A) (rest : Batch A B (B -> C1)) :
  map (Batch A B) f (rest ⧆ a) = map (Batch A B) (compose f) rest ⧆ a.
Proof.
  reflexivity.
Qed.

Lemma mapfst_Batch_rw1 {A1 A2 B C : Type} `(f : A1 -> A2) (c : C) :
  mapfst_Batch A1 A2 f (Done A1 B C c) = Done A2 B C c.
Proof.
  reflexivity.
Qed.

Lemma mapfst_Batch_rw2 {A1 A2 B C : Type} (f : A1 -> A2) (a : A1) (b : Batch A1 B (B -> C)) :
  mapfst_Batch A1 A2 f (b ⧆ a) = mapfst_Batch A1 A2 f b ⧆ f a.
Proof.
  reflexivity.
Qed.
 *)

(*

  Definition double_batch {A B C : Type} :
    A -> Batch A B (Batch B C C) :=
    map (Batch A B) (batch B C) ∘ (batch A B).
*)

(** * Traversable monads as coalgebras *)
(******************************************************************************)
Class ToBatchDMP
  (F : Type -> Type -> Type)
  (T : Type -> Type -> Type) :=
  toBatchDMP : forall
      B  (* type of old binders *)
      B' (* type of new binders *)
      A  (* type of old leaves *)
      A' (* type of new leaves *)
    , F B A -> (* input: the abstract syntax tree *)
      DFS (* output: a DFS of the tree *)
        (list B * B) (* binders in context *)
        B' (* newly inserted binders *)
        (list B * A) (* leaves in context *)
        (T B' A') (* newly inserted subtrees *)
        (F B' A'). (* return type of the DFS, the new syntax tree *)

#[local] Arguments toBatchDMP {F T}%function_scope {ToBatchDMP} {B B' A A'}%type_scope _.

Section cojoin.

  Context
    (T : Type -> Type -> Type)
      `{ToBatchDMP T T}
      (A A' A'' B B' B'' RB RA : Type).

  Definition double_batchDMP :
    list B * A ->
    DFS
      (list B * B)
      B''
      (list B * A)
      (T B'' A'')
      (DFS
         (list B'' * B'')
         B'
         (list B'' * A'')
         (T B' A')
         T).
  Proof.
    intros.
    apply Leaf.
    apply Done.
    intros.

    eapply toBatchDMP.

    Batch (W * A) (T A') (Batch (W * A') (T R) (T R))


    fun '(w, a) =>
      (map (F := Batch (W * A) (T A'))
         (mapfst_Batch (incr w) ∘ toBatch7) ∘ batch (W * A) (T A')) (w, a).

  Lemma cojoin_Batch7_spec : forall (A A' A'' : Type) (R : Type),
      cojoin_Batch7 (A := A) (A' := A') (A'' := A'') (R := R) =
        runBatch (F := Batch (W * A) (T A'') ∘ Batch (W * A'') (T A'))
          double_batch7.
  Proof.

  #[program] Definition cojoin_BatchDMP :
    DFS (* input: a DFS of a tree *)
      (list B * B) (* binders in context *)
      B' (* newly inserted binders *)
      (list B * A) (* leaves in context *)
      (T B' A') (* newly inserted subtrees *)
      R (* return type of the DFS, the new syntax tree *)
    ->
      DFS
        (list B * B)
        B''
        (list B * A)
        (T B'' A'')
        (DFS
           (list B'' * B'')
           B'
           (list B'' * A'')
           (T B' A')
           R).
  Proof.
    intros d.
    induction d as [R r | R cont cont_rec [w b] | ].
    - apply (Done (Done r)).
    - apply Bin.
      2: {exact (w, b).}.
      Check map (F := DFS (list B * B) B'' (list B * A) (T B'' A'')).
      assert (DFS (list B'' * B'') B' (list B'' * A'') (T B' A') (B' -> R) ->
              B'' ->
              DFS (list B'' * B'') B' (list B'' * A'') (T B' A') R).
      { intros next b''.
        apply Bin.
        apply next.
    False.

  #[program] Fixpoint cojoin_BatchDMP {T : Type -> Type -> Type}
  `{Monoid_op W}
  {WA WB WB' A B B' C : Type}
  (d : DFS (list WA  * WA ) WB  (list WA  * A) (T WB  B ) C):
  DFS (list WA  * WA ) WB' (list WA  * A) (T WB' B')
    (DFS (list WB' * WB') WB  (list WB' * B) (T WB  B ) C) := _.

Next Obligation.
Admitted.

Context (T : Type -> Type -> Type) `(d : DFS (list WA  * WA ) WB  (list WA  * A) (T WB  B ) C) (WB' B' : Type).

Goal False.
  destruct d.
  - admit.
  - admit.
  - rename d0 into rest.
    Set Printing Implicit.
    Check
      map_DFS (fun continue => fun (t : T WB' B') => _ )
        (cojoin_BatchDMP rest).
Abort.


#[program] Fixpoint cojoin_BatchDMP1 {T : Type -> Type -> Type}
  `{Monoid_op W} `{ToBatchDMP T T}
  {WA WB WB' A B B' C : Type}
  (d : DFS (list WA  * WA ) WB  (list WA  * A) (T WB  B ) C):
       DFS (list WA  * WA ) WB' (list WA  * A) (T WB' B')
      (DFS (list WB' * WB') WB  (list WB' * B) (T WB  B ) C) :=
  match d with
  | Done c => Done (Done c)
  | Leaf rest (w, a) =>
      Leaf
        (map_DFS (fun continue => fun (t : T WB' B') => _ )
           (cojoin_BatchDMP1 rest))
        (w, a)
  | Bin rest _ => _
  end.

Next Obligation.

  admit.
Admitted.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  Check cojoin_BatchDMP rest
  admit.
Admitted.
  Next Obligation.
  apply Leaf. shelve.
  constructor; auto.
  Unshelve.
  Check (cojoin_BatchDMP (C := _) rest).

        (*
      Step (map (F := Batch (W * A) (T B'))
              (fun (continue : Batch (W * B') (T B) (T B -> C))
                 (t : T B') =>
                 continue <⋆> (mapfst_Batch _ _ (incr w) (toBatchDM t : Batch (W * B') (T B) (T B)))
              ) (cojoin_BatchDM (T := T) (B' := B') (B := B) rest))
        ((w, a) : W * A)
         *)
  end.



About Leaf.
Class DecoratedTraversableMonadPoly (T : Type -> Type -> Type)
  `{forall B, Return (T B)} `{ToBatchDMP T T} :=
  { dtm_ret : forall (WA WB A B : Type),
      toBatchDMP WA WB A B ∘ ret (T WA) A = Leaf (Done (@id (T WB B))) ∘ ret (list WA ×) A;
  }.
    dtm_extract : forall (A : Type),
      extract_Batch ∘ mapfst_Batch (W * A) (T A) (ret T A ∘ extract (W ×) A) ∘ toBatchDM W T A A = @id (T A);
    dtm_duplicate : forall (A B C : Type),
      cojoin_BatchDM W T A C B (T C) ∘ toBatchDM W T A C =
        map (Batch (W * A) (T B)) (toBatchDM W T B C) ∘ toBatchDM W T A B;
  }.

Class Substitute
  (T : Type -> Type -> Type)
  (F : Type -> Type -> Type) :=
  substitute :
    forall (WA WB : Type) (G : Type -> Type)
      `{Map G} `{Pure G} `{Mult G}
      (A B : Type),
      (list WA * WA -> WB) ->
      (list WA * A -> G (T WB B))
      -> F WA A -> G (F WB B).
