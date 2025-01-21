From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.DecoratedTraversableCommIdemFunctor
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Functors.Early.List
  Functors.Diagonal
  Functors.Early.Writer.

Import Applicative.Notations.
Import Monoid.Notations.
Import TraversableFunctor.Notations.
Import DecoratedTraversableFunctor.Notations.
Import DecoratedTraversableCommIdemFunctor.Notations.
Import List.ListNotations.

(** * Prefix Decoration operation for the [List] functor *)
(******************************************************************************)

(** ** Accumulator-based specification *)
(******************************************************************************)
Section rec_version.

  Fixpoint decorate_prefix_list_rec {A: Type} (ctx: list A) (l: list A):
    list (list A * A) :=
    match l with
    | nil => nil
    | x :: xs =>
        (* (ctx, x) :: decorate_prefix_list_rec (x :: ctx) xs *)
        (ctx, x) :: decorate_prefix_list_rec (ctx ++ [x]) xs
    end.

  Definition decorate_prefix_list_ {A: Type} (l: list A):
    list (list A * A) := decorate_prefix_list_rec nil l.

End rec_version.

(** ** Map-based specification *)
(******************************************************************************)
Fixpoint decorate_prefix_list {A: Type} (l: list A):
  list (list A * A) :=
  match l with
  | nil => nil
  | x :: xs =>
      (nil, x) :: map (F := list) (incr [x]) (decorate_prefix_list xs)
  end.

(** ** Equivalence *)
(******************************************************************************)
Lemma decorate_prefix_list_equiv_rec : forall (A: Type) (ctx: list A) (l: list A),
    decorate_prefix_list_rec ctx l =
      map (F := list) (incr ctx) (decorate_prefix_list l).
Proof.
  intros.
  generalize dependent ctx. induction l; intro ctx.
  - reflexivity.
  - cbn.
    unfold Monoid_op_list at 1, monoid_op at 1.
    rewrite List.app_nil_r.
    fequal.
    compose near (decorate_prefix_list l) on right.
    rewrite (fun_map_map).
    rewrite incr_incr.
    unfold_ops @Monoid_op_list.
    rewrite IHl.
    reflexivity.
Qed.

Lemma decorate_prefix_list_equiv: forall (A: Type) (l: list A),
    decorate_prefix_list_ l = decorate_prefix_list l.
Proof.
  intros.
  assert (incr [] = id (A := list A * A)).
  { now ext [l' a]. }
  specialize (decorate_prefix_list_equiv_rec A nil l).
  rewrite H.
  rewrite fun_map_id.
  trivial.
Qed.

(** ** Examples *)
(******************************************************************************)
Module Examples.

  Example list1 := [ 3 ].
  Example list2 := [ 3 ; 5 ].
  Example list3 := [ 3 ; 5 ; 7 ; 8 ].

  Compute decorate_prefix_list list3.

End Examples.

(** ** Rewriting principles *)
(******************************************************************************)
Section decorate_prefix_list_rw.

  Context
    {A : Type}.

  Lemma decorate_prefix_list_rw_nil:
    decorate_prefix_list (@nil A) = (@nil (list A * A)).
  Proof.
    reflexivity.
  Qed.

  Lemma decorate_prefix_list_rw_one: forall (a: A),
    decorate_prefix_list [a] = [([], a)].
  Proof.
    reflexivity.
  Qed.

  Lemma decorate_prefix_list_rw_cons: forall (a: A) (l: list A),
      decorate_prefix_list (a :: l) =
        ([], a) :: map (incr [a]) (decorate_prefix_list l).
        (*
        ([], a) :: map (A := Z A) (B := Z A)
          (incr [a]) (decorate_prefix_list l).
          *)
  Proof.
    intros. cbn.
    reflexivity.
  Qed.

  Lemma decorate_prefix_list_rw_app: forall (l1 l2: list A),
      decorate_prefix_list (l1 ++ l2) =
        decorate_prefix_list l1 ++ map (incr l1) (decorate_prefix_list l2).
  Proof.
    intros. induction l1.
    - cbn.
      change (incr []) with (incr (A := A) (Ƶ: list A)).
      rewrite incr_zero.
      rewrite (fun_map_id (F := list)).
      reflexivity.
    - (* left *)
      rewrite <- List.app_comm_cons.
      rewrite decorate_prefix_list_rw_cons.
      rewrite IHl1.
      rewrite map_list_app.
      compose near (decorate_prefix_list l2) on left.
      rewrite (fun_map_map).
      rewrite incr_incr.
      (* right *)
      rewrite decorate_prefix_list_rw_cons.
      reflexivity.
  Qed.

End decorate_prefix_list_rw.


(** * Cartesian product bifunctor *)
(******************************************************************************)
Definition map_both {A B C D: Type} (f : A -> B) (g: C -> D) : A * C -> B * D :=
  map_snd g ∘ map_fst f.

Definition traverse_both
  {A B C D: Type}
  {G} `{Map G} `{Mult G} `{Pure G}
  (f : A -> G B) (g: C -> G D) : A * C -> G (B * D) :=
  fun '(a, c) => pure pair <⋆> f a <⋆> g c.

(** * The <<Z>> Comonad *)
(******************************************************************************)
Definition Z: Type -> Type := fun A => list A * A.

Ltac unfold_Z:=
  repeat change (Z ?A) with (list A * A).

Ltac unfold_Z_in H:=
  repeat change (Z ?A) with (list A * A) in H.

Ltac unfold_Z_all:=
  repeat change (Z ?A) with (list A * A) in *.

Ltac fold_Z :=
  repeat change (list ?A * ?A) with (Z A).

Ltac fold_Z_in H :=
  repeat change (list ?A * ?A) with (Z A) in H.

Ltac fold_Z_all :=
  repeat change (list ?A * ?A) with (Z A) in *.

(** ** Functor instance *)
(******************************************************************************)
#[export] Instance Map_Z: Map Z := fun A B f => map_both (map (F := list) f) f.

#[export] Instance Functor_Z: Functor Z.
Proof.
  constructor.
  - intros. ext [l a]. cbn. now rewrite fun_map_id.
  - intros. ext [l a]. cbn. unfold id.
    compose near l on left. rewrite fun_map_map. reflexivity.
Qed.

From Tealeaves Require Import Categorical.Comonad.

(** ** Categorical comonad instance *)
(******************************************************************************)
#[export] Instance Cojoin_Z: Cojoin Z := fun A '(l, a) => (decorate_prefix_list l, (l, a)).

(** *** Rewriting principles *)
(******************************************************************************)
Section Cojoin_Z_rw.

  Context {A: Type}.

  Lemma cojoin_Z_rw_nil: forall (a: A),
      cojoin (W := Z) (@nil A, a) = (nil, (nil, a)).
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Z_rw_cons: forall (a1 a2: A) (l: list A),
      cojoin (W := Z) (a1 :: l, a2) = (([], a1) :: map (incr [a1]) (decorate_prefix_list l), (a1 :: l, a2)).
  Proof.
    unfold_ops @Cojoin_Z.
    intros.
    rewrite decorate_prefix_list_rw_cons.
    reflexivity.
  Qed.

  Lemma cojoin_Z_rw_app: forall (a: A) (l1 l2: list A),
      cojoin (W := Z) (l1 ++ l2, a) = (decorate_prefix_list l1 ++ map (incr l1) (decorate_prefix_list l2), (l1 ++ l2, a)).
  Proof.
    unfold_ops @Cojoin_Z.
    intros.
    rewrite decorate_prefix_list_rw_app.
    reflexivity.
  Qed.

  Lemma cojoin_Z_rw_preincr_one: forall (ctx: A) (l: list A) (a: A),
      (cojoin (W := Z) ⦿ [ctx]) (l, a) =
        map_both (cons ([], ctx) ∘ map (incr [ctx])) (incr [ctx])
          (cojoin (W := Z) (l, a)).
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Z_rw_preincr: forall (ctx: list A) (l: list A) (a: A),
      (cojoin (W := Z) ⦿ ctx) (l, a) =
        map_both (app (decorate_prefix_list ctx) ∘ map (incr ctx)) (incr ctx)
          (cojoin (W := Z) (l, a)).
  Proof.
    intros.
    cbn. unfold id.
    change (?x ● ?y) with (x ++ y).
    rewrite decorate_prefix_list_rw_app.
    reflexivity.
  Qed.

  Lemma cojoin_Z_rw_preincr_pf: forall (ctx: list A),
      cojoin (W := Z) ⦿ ctx =
        map_both (app (decorate_prefix_list ctx) ∘ map (incr ctx)) (incr ctx) ∘ cojoin.
  Proof.
    intros. ext [l a].
    now rewrite cojoin_Z_rw_preincr.
  Qed.

End Cojoin_Z_rw.

#[export] Instance Extract_Z: Extract Z :=
  fun (A: Type) => @snd (list A) A.

Lemma extract_incr: forall (A: Type) (ctx: list A),
    extract (W := Z) ∘ incr ctx = extract (W := Z).
Proof.
  intros. ext [l a]. reflexivity.
Qed.

#[export] Instance Natural_decorate_prefix_list: Natural (@decorate_prefix_list).
Proof.
  constructor; try typeclasses eauto.
  intros. unfold compose. ext l.
  generalize dependent f.
  induction l; intro f.
  - reflexivity.
  - (* left *)
    rewrite decorate_prefix_list_rw_cons at 1.
    unfold_ops @Map_compose.
    rewrite map_list_cons at 1.
    compose near (decorate_prefix_list l).
    rewrite (fun_map_map).
    (* right *)
    rewrite map_list_cons at 1.
    rewrite decorate_prefix_list_rw_cons.
    rewrite <- IHl.
    compose near (decorate_prefix_list l) on right.
    unfold_ops @Map_compose.
    change (prod (list ?B) ?B) with (Z B).
    rewrite (fun_map_map).
    fequal.
    fequal.
    ext [z z'].
    reflexivity.
Qed.

#[export] Instance Natural_Extract_Z: Natural (@extract Z Extract_Z).
Proof.
  constructor; try typeclasses eauto.
  intros. ext [ctx a].
  reflexivity.
Qed.

#[export] Instance Natural_Cojoin_Z: Natural (@cojoin Z Cojoin_Z).
Proof.
  constructor; try typeclasses eauto.
  intros. ext [ctx a].
  cbn; unfold id.
  fequal.
  compose near ctx.
  rewrite <- (natural (Natural := Natural_decorate_prefix_list)).
  reflexivity.
Qed.

Section map_args.

  #[local] Notation "'dec'" := decorate_prefix_list.

  Arguments map (F)%function_scope {Map} {A B}%type_scope f%function_scope _.

  Lemma cojoin_assoc_lemma: forall (A : Type) (l: list A),
      dec (dec l) = map list cojoin (dec l).
  Proof.
    intros.
    induction l.
    - reflexivity.
    - (* left *)
      rewrite decorate_prefix_list_rw_cons at 1.
      rewrite decorate_prefix_list_rw_cons at 1.
      compose near (dec l) on left.
      rewrite <- (natural (Natural := Natural_decorate_prefix_list)).
      change (map (A := ?A) (B := ?B)
                (fun A0 : Type => list (list A0 * A0))) with
        (map (list ∘ Z) (A := A) (B := B)).
      unfold_ops @Map_compose.
      unfold compose at 1.
      compose near (dec (dec l)).
      rewrite (fun_map_map (F := list)).
      (* right *)
      rewrite decorate_prefix_list_rw_cons at 1.
      rewrite map_list_cons.
      unfold cojoin at 1, Cojoin_Z at 1.
      rewrite decorate_prefix_list_rw_nil.
      (* fequal *)
      fequal.
      compose near (dec l) on right.
      rewrite (fun_map_map (F := list)).
      (* panic *)
      rewrite IHl.
      compose near (dec l) on left.
      rewrite (fun_map_map).
      fequal.
      ext [zl za].
      cbn; unfold id.
      reflexivity.
  Qed.

End map_args.

Lemma cojoin_assoc:
  forall A : Type,
    cojoin (W := Z) ∘ cojoin (W := Z) =
      map (F := Z) (cojoin (W := Z)) ∘ cojoin (W := Z) (A := A).
Proof.
  intros A. ext [l a].
  unfold compose at 2 4.
  cbn.
  unfold id.
  induction l.
  + cbn. reflexivity.
  + fequal.
    apply cojoin_assoc_lemma.
Qed.

#[export] Instance Comonad_Z: Comonad Z.
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros A. ext [l a]. reflexivity.
  - intros A. ext [l a]. cbn.
    compose near l. unfold id. fequal.
    unfold compose.
    induction l.
    + reflexivity.
    + cbn. fequal.
      compose near (decorate_prefix_list l).
      rewrite (fun_map_map).
      assert (extract (W := Z) ∘ incr [a0] = extract (A := A) (W := Z)).
      { ext [l' a']. reflexivity. }
      unfold Z in H at 1; cbn in H.
      rewrite H.
      assumption.
  - apply cojoin_assoc.
Qed.

(** ** [decorate_prefix_list] is a coaction *)
(******************************************************************************)
Lemma decorate_prefix_list_extract: forall (A: Type),
    map extract ∘ decorate_prefix_list = @id (list A).
Proof.
  intros. ext l. unfold compose.
  induction l.
  - reflexivity.
  - rewrite decorate_prefix_list_rw_cons.
    rewrite map_list_cons.
    change (extract ([], a)) with a.
    compose near (decorate_prefix_list l).
    rewrite (fun_map_map).
    rewrite extract_incr.
    fold_Z_all.
    rewrite IHl.
    reflexivity.
Qed.

Lemma decorate_prefix_list_cojoin: forall (A: Type),
    map cojoin ∘ decorate_prefix_list =
      decorate_prefix_list ∘ decorate_prefix_list (A := A).
Proof.
  intros. ext l. unfold compose.
  now rewrite cojoin_assoc_lemma.
Qed.

(** ** Traversable functor instance *)
(******************************************************************************)
#[export] Instance Traverse_Z: Traverse Z.
Proof.
  intros G MapG PureG MultG A B f.
  unfold Z.
  intros [l a].
  (* exact (mult (map_both (traverse (T := list) f) f (l, a))).*)
  exact (pure pair <⋆> (traverse (T:=list) f l) <⋆> f a).
Defined.

#[export] Instance Compat_Map_Traverse: Compat_Map_Traverse Z.
Proof.
  unfold Compat_Map_Traverse.
  ext A B f [l a].
  cbn. unfold id. fequal.
  rewrite (map_to_traverse (T := list)).
  reflexivity.
Qed.

(** *** Specification *)
(******************************************************************************)
Section traverse_Z_spec.

  Context
    {G: Type -> Type}
      `{Applicative G}.

  Context
    {A B C D: Type}
    (f: A -> G B)
      (g: C -> G D).

  Lemma traverse_Z_spec:
      traverse (T := Z) f =
        traverse_both (traverse (T := list) f) f.
  Proof.
    reflexivity.
  Qed.


  Context {X Y: Type}
    (h:  X -> list A) (j: Y -> A).

  Lemma traverse_Z_map:
      traverse (T := Z) f ∘ map_both h j =
        traverse_both (traverse f ∘ h) (f ∘ j).
  Proof.
    ext [x y].
    reflexivity.
  Qed.


  Context {E: Type}.

  Lemma map_traverse_both: forall (i: B * D -> E),
      map i ∘ traverse_both f g =
        map i ∘ traverse_both f g.
  Proof.
    reflexivity.
  Qed.

End traverse_Z_spec.

(** *** Rewriting rules and specs *)
(******************************************************************************)
Section traverse_Z_rw.

  Context {A B: Type} {G: Type -> Type}
    `{Applicative G} (f: A -> G B).

  Lemma traverse_Z_rw: forall (l: list A) (a: A),
      traverse (T := Z) f (l, a) =
        (pure pair <⋆> (traverse (T:=list) f l) <⋆> f a).
  Proof.
    reflexivity.
  Qed.


  Lemma traverse_Z_incr_lemma:
    forall (ctx: list A)
      (g: list A * A -> G B)
      (j: list (list A * A))
      (l: list A) (a: A),
      (traverse (T := Z) g ∘
         map_both (app (decorate_prefix_list ctx) ∘ map (incr ctx)) (incr ctx))
        (j, (l, a)) =
        pure (compose pair ∘ app (A:=B))
          <⋆> traverse g (decorate_prefix_list ctx)
          <⋆> traverse (g ⦿ ctx) j
          <⋆> (g ⦿ ctx) (l, a).
  Proof.
    intros.
    unfold compose. cbn.
    unfold id.
    rewrite (traverse_list_app G).
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    compose near j on left.
    rewrite traverse_map.
    reflexivity.
  Qed.

  Lemma traverse_Z_incr_lemma2:
    forall (ctx: list A)
      (g: list A * A -> G B)
      j l a,
      (traverse (T := Z) g
         ∘ map_both (app (decorate_prefix_list ctx) ∘ map (incr ctx)) (incr ctx))
        (j, (l, a)) =
        map incr (traverse g (decorate_prefix_list ctx))
          <⋆> (pure pair <⋆> traverse (g ⦿ ctx) j <⋆> (g ⦿ ctx) (l, a)).
  Proof.
    intros.
    rewrite traverse_Z_incr_lemma.
    rewrite map_to_ap.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    reflexivity.
  Qed.

  Lemma traverse_Z_incr_lemma3:
    forall (ctx: list A)
      (g: list A * A -> G B)
      j l a,
      (traverse (T := Z) g ∘
         map_both (app (decorate_prefix_list ctx) ∘ map (incr ctx)) (incr ctx))
        (j, (l, a)) =
        map incr (traverse g (decorate_prefix_list ctx)) <⋆>
          (traverse (T := Z) (g ⦿ ctx) (j, (l, a))).
  Proof.
    intros.
    rewrite traverse_Z_incr_lemma2.
    reflexivity.
  Qed.

End traverse_Z_rw.

(** *** Traversable Z *)
(******************************************************************************)
#[export] Instance: TraversableFunctor Z.
Proof.
  constructor.
  - intros. ext [l a].
    cbn.
    now rewrite trf_traverse_id.
  - intros. ext [l a].
    unfold compose.
    cbn.
    do 2 rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- (trf_traverse_traverse _ _ _ g f).
    unfold kc2.
    unfold compose at 4.
    repeat rewrite (ap_compose2 G2 G1).
    unfold_ops @Pure_compose.
    rewrite <- ap_map.
    repeat rewrite map_ap.
    unfold compose at 5.
    rewrite <- ap_map.
    fequal. fequal.
    repeat rewrite app_pure_natural.
    reflexivity.
  - intros. ext [l a].
    unfold compose at 1. cbn.
    repeat rewrite ap_morphism_1.
    rewrite appmor_pure.
    compose near l on left.
    rewrite trf_traverse_morphism.
    reflexivity.
Qed.

(** * Decoration commutes with traversals *)
(******************************************************************************)
Generalizable All Variables.

Section commute_law.

  Context
    `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G}
      `{! ApplicativeCommutativeIdempotent G}.

  Import Categorical.Monad (Return, ret).

  Lemma decorate_commute_cons {A B: Type}
    (f: A -> G B) (a: A) (l: list (list A * A)):
    l <> nil ->
    (traverse (T := list) (traverse (T := Z) f)
       (map (F := list) (A := Z A) (B := Z A) (incr [a]) l)) =
      map (F := G) (map (F := list) (A := Z B) (B := Z B)
                      ∘ incr ∘ ret (T := list)) (f a) <⋆>
        traverse (T := list) (traverse (T := Z) f) l.
  Proof.
    introv Hneqnil.
    induction l as [| x xs IHxs ].
    - contradiction.
    - clear Hneqnil.
      destruct xs as [| y ys ].
      + clear IHxs.
        destruct x as [l b].
        (* LHS *)
        rewrite map_list_one.
        change ([?x]) with (ret (T := list) x) at 1.
        rewrite (traverse_list_one G).
        unfold incr at 1.
        change ([?a] ● ?l) with (a :: l).
        rewrite traverse_Z_rw.
        rewrite map_ap.
        rewrite map_ap.
        rewrite app_pure_natural.

        rewrite traverse_list_cons.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        (* RHS *)
        change ([?x]) with (ret (T := list) x) at 1.
        rewrite (traverse_list_one G).
        rewrite traverse_Z_rw.
        rewrite map_ap.
        rewrite map_ap.
        rewrite app_pure_natural.
        rewrite <- ap4.
        rewrite <- ap_map.
        rewrite app_pure_natural.

        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        reflexivity.
      + specialize (IHxs ltac:(discriminate)).
        remember (y :: ys) as rest.
        (* LHS *)
        rewrite map_list_cons.
        rewrite traverse_list_cons.

        assert (Htrav_incr_spec: traverse (T := Z) f (incr [a] x) =
                  (map (incr ∘ ret) (f a) <⋆> traverse (T := Z) f x)).
        { clear y ys rest Heqrest IHxs.
          destruct x as [xL xA].

          (* LHS *)
          unfold incr at 1.
          change ([?a] ● ?l) with (a :: l).
          rewrite traverse_Z_rw.
          rewrite traverse_list_cons.
          rewrite <- ap4.
          rewrite ap2.
          rewrite <- ap4.
          rewrite ap2.
          rewrite ap2.

          (* RHS *)
          rewrite traverse_Z_rw.
          rewrite <- ap4.
          rewrite <- ap_map.
          rewrite app_pure_natural.
          rewrite <- ap4.
          rewrite <- ap4.
          rewrite ap2.
          rewrite ap2.

          rewrite ap3.
          rewrite <- ap4.
          rewrite ap2.
          rewrite ap2.
          reflexivity. }
        rewrite Htrav_incr_spec.
        clear Htrav_incr_spec.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap_map.
        rewrite app_pure_natural.

        Set Keyed Unification.
        rewrite IHxs.
        clear IHxs.
        Unset Keyed Unification.
        rewrite (traverse_list_cons G (Z A) (Z B) (traverse f) x rest).

        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap2.

        (* RHS *)
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        (* panik *)
        fequal.

        (* LHS *)
        rewrite map_to_ap at 1.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        rewrite (ap_ci2 _ (f a)).
        rewrite app_pure_natural.
        rewrite ap_cidup.
        rewrite map_ap.
        rewrite app_pure_natural.
        rewrite (ap_ci2 _ (traverse (T := Z) f x) (f a)).
        rewrite app_pure_natural.

        (* RHS *)
        rewrite <- ap_map.
        rewrite app_pure_natural.
        reflexivity.
  Qed.

  Theorem decorate_commute {A B: Type}
    (f: A  -> G B):
    map (F := G) (decorate_prefix_list) ∘ traverse (T := list) f =
      traverse (T := list) (traverse (T := Z) f) ∘ decorate_prefix_list.
  Proof.
    intros.
    unfold compose.
    ext l.
    induction l as [| x xs IHxs ].
    - (* LHS *)
      rewrite traverse_list_nil.
      rewrite app_pure_natural.
      (* RHS *)
      rewrite decorate_prefix_list_rw_nil.
      rewrite traverse_list_nil.
      (* Done *)
      reflexivity.
    - destruct xs as [| y ys ].
      { (* LHS *)
        change [x] with (ret (T := list) x) at 1.
        rewrite (traverse_list_one G).
        compose near (f x) on left.
        rewrite (fun_map_map).
        (* RHS *)
        rewrite decorate_prefix_list_rw_one.
        change [?pair] with (ret (T := list) pair) at 1.
        rewrite (traverse_list_one G).
        rewrite traverse_Z_rw.
        rewrite map_ap.
        rewrite map_ap.
        rewrite app_pure_natural.
        rewrite traverse_list_nil.
        rewrite ap2.
        rewrite map_to_ap.
        reflexivity.
      }
      {
        (* LHS *)
        remember (y :: ys) as rest.
        rewrite traverse_list_cons.
        rewrite map_ap.
        rewrite map_ap.
        rewrite app_pure_natural.

        (* RHS *)
        rewrite decorate_prefix_list_rw_cons; fold_Z.
        rewrite traverse_list_cons.
        rewrite traverse_Z_rw.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite traverse_list_nil.
        rewrite ap2.
        rewrite (decorate_commute_cons f x (decorate_prefix_list rest)).
        (* where prior lemma gets used! *)
        2: { subst. cbn. discriminate. }
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite map_to_ap.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap_cidup.
        rewrite app_pure_natural.

        rewrite <- IHxs.
        rewrite map_to_ap.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        (* Cross our fingers! *)
        reflexivity.
      }
  Qed.

  Theorem cojoin_commute {A B: Type}
    (f: A  -> G B):
    map (cojoin (W := Z)) ∘ traverse (T := Z) f =
      traverse (T := Z) (traverse (T := Z) f) ∘ cojoin.
  Proof.
    intros. ext [l a].
    unfold compose. cbn.
    rewrite map_to_ap.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    repeat rewrite ap2.
    (* RHS *)
    change ((traverse (traverse f)) (decorate_prefix_list l))
      with ((traverse (traverse f) ∘ decorate_prefix_list) l).
    rewrite <- decorate_commute.
    unfold compose at 4.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    repeat rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    do 2 rewrite ap2.
    rewrite ap_cidup.
    rewrite app_pure_natural.
    reflexivity.
  Qed.

End commute_law.

(** * Mapdt *)
(******************************************************************************)

(** ** Recursive inlined version *)
(******************************************************************************)
Fixpoint mapdt_list_prefix_
  {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
  {A B : Type} (f : list A * A -> G B) (l : list A)
  : G (list B) :=
  match l with
  | nil => pure (@nil B)
  | x :: xs =>
      pure (@List.cons B) <⋆> f (nil, x) <⋆>
        mapdt_list_prefix_ (f ⦿ [x]) xs
  end.

(*
(** *** Rewriting principles *)
(******************************************************************************)
Section mapdt_list_prefix_rw.
  Context
    {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
      `{! Applicative G}
      {A B : Type}.

  Lemma mapdt_list_prefix_rw_nil: forall (f : list A * A -> G B),
    mapdt_list_prefix_ f nil = pure nil.
  Proof. reflexivity. Qed.

  Lemma mapdt_list_prefix_rw_cons: forall (f : list A * A -> G B) a l,
      mapdt_list_prefix_ f (a :: l) =
        pure (@List.cons B) <⋆> f (nil, a) <⋆> mapdt_list_prefix_ (f ⦿ [a]) l.
  Proof. reflexivity. Qed.

  Lemma mapdt_list_prefix_rw_app: forall (g: list A * A -> G B) l l',
      mapdt_list_prefix_ g (l ++ l') =
        pure (@app B) <⋆> mapdt_list_prefix_ g l <⋆> mapdt_list_prefix_ (g ⦿ l) l'.
  Proof.
    intros g l. generalize dependent g.
    induction l. intros g l'.
    - cbn. change (g ⦿ []) with (g ⦿ Ƶ). rewrite preincr_zero.
      rewrite ap2.
      change (app []) with (@id (list B)).
      rewrite ap1. reflexivity.
    - intros g l'.
      rewrite <- List.app_comm_cons.
      rewrite mapdt_list_prefix_rw_cons.
      rewrite IHl.
      rewrite mapdt_list_prefix_rw_cons.
      rewrite preincr_preincr.
      repeat rewrite <- ap4.
      fequal.
      fequal.
      repeat rewrite ap4.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      repeat rewrite <- ap2.
      rewrite ap3.
      repeat rewrite ap2.
      rewrite <- ap4.
      repeat rewrite ap2.
      reflexivity.
  Qed.

End mapdt_list_prefix_rw.
*)

(** ** Decomposed version *)
(******************************************************************************)
Definition mapdt_list_prefix
  `{G: Type -> Type} `{Map G} `{Pure G} `{Mult G}
  {A B: Type} (f: list A * A -> G B): list A -> G (list B) :=
  traverse (T := list) (G := G) f ∘ decorate_prefix_list.

#[export] Instance Mapdt_CommIdem_list_prefix:
  Mapdt_CommIdem Z list := @mapdt_list_prefix.

Lemma mapdt_list_prefix_decorate:
  forall `{G: Type -> Type} `{Map G} `{Pure G} `{Mult G} `{! Applicative G}
    {A B: Type} (f: Z (Z A) -> G B),
    mapdt_list_prefix f ∘ decorate_prefix_list =
      mapdt_list_prefix (f ∘ cojoin (W := Z)).
Proof.
  intros.
  unfold mapdt_list_prefix.
  reassociate -> on left.
  rewrite <- decorate_prefix_list_cojoin.
  reassociate <- on left.
  rewrite (traverse_map).
  reflexivity.
Qed.

(** *** Rewriting principles *)
(******************************************************************************)
Section mapdt_list_prefix_rw.
  Context
    {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
      `{! Applicative G}
      {A B : Type}.

  Lemma mapdt_list_prefix_rw_nil: forall (f : list A * A -> G B),
    mapdt_list_prefix f nil = pure nil.
  Proof.
    reflexivity.
  Qed.

  Lemma mapdt_list_prefix_rw_cons: forall (f : list A * A -> G B) a l,
      mapdt_list_prefix f (a :: l) =
        pure (@List.cons B) <⋆> f (nil, a) <⋆> mapdt_list_prefix (f ⦿ [a]) l.
  Proof.
    intros. cbn.
    compose near (decorate_prefix_list l) on left.
    rewrite traverse_map.
    reflexivity.
  Qed.

  Lemma mapdt_list_prefix_rw_app: forall (g: list A * A -> G B) l l',
      mapdt_list_prefix g (l ++ l') =
        pure (@app B) <⋆> mapdt_list_prefix g l <⋆> mapdt_list_prefix (g ⦿ l) l'.
  Proof.
    intros g l.
    generalize dependent g.
    induction l; intros g l'.
    - cbn.
      rewrite ap2.
      change (app []) with (@id (list B)).
      rewrite ap1.
      change (g ⦿ []) with (g ⦿ Ƶ).
      rewrite preincr_zero.
      reflexivity.
    - rewrite <- List.app_comm_cons.
      rewrite mapdt_list_prefix_rw_cons.
      rewrite IHl.
      rewrite mapdt_list_prefix_rw_cons.
      rewrite preincr_preincr.
      repeat rewrite <- ap4.
      fequal.
      fequal.
      repeat rewrite ap4.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      repeat rewrite <- ap2.
      rewrite ap3.
      repeat rewrite ap2.
      rewrite <- ap4.
      repeat rewrite ap2.
      reflexivity.
  Qed.

End mapdt_list_prefix_rw.

(** ** Specifications *)
(******************************************************************************)
Lemma mapdt_list_prefix_spec
  {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! Applicative G}
  (f: list A * A -> G B) (l: list A):
  mapdt_list_prefix f l = mapdt_list_prefix_ f l.
Proof.
  generalize dependent f.
  unfold mapdt. induction l; intro f.
  - reflexivity.
  - cbn. specialize (IHl (f ⦿ [a])).
    compose near (decorate_prefix_list l) on left.
    rewrite traverse_map.
    rewrite <- IHl.
    unfold preincr. unfold incr.
    reflexivity.
Qed.

(** ** Preincrement *)
(******************************************************************************)
Lemma traverse_incr_one: forall (A B: Type) {G} `{Applicative G} (f: A -> G B) (a: A),
    traverse (T := Z) f ∘ incr [a] =
      ap G (pure (map_fst ∘ cons) <⋆> f a) ∘ traverse (T := Z) f.
Proof.
  intros. ext [l a'].
  unfold compose.
  cbn.
  (* lhs *)
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  rewrite ap2.
  rewrite ap2.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  rewrite ap2.
  rewrite ap2.
  rewrite ap2.
  rewrite ap2.
  rewrite ap2.
  rewrite ap3.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  reflexivity.
Qed.

Lemma traverse_preincr_one: forall (A B: Type) {G} `{Applicative G} (f: A -> G B) (a: A),
    (traverse (T := Z) f) ⦿ [a] =
      ap G (pure (map_fst ∘ cons) <⋆> f a) ∘ traverse (T := Z) f.
Proof.
  apply traverse_incr_one.
Qed.

Lemma traverse_preincr: forall (A B: Type) {G} `{Applicative G} (f: A -> G B) (ctx: list A),
    (traverse (T := Z) f) ⦿ ctx =
      ap G (map incr (traverse (T := list) f ctx)) ∘ traverse (T := Z) f.
Proof.
  intros.
  ext [l a].
  unfold compose.
  unfold_ops @Traverse_Z.
  cbn.
  change (ctx ● l) with (ctx ++ l).
  rewrite (traverse_list_app G).
  rewrite <- ap4.
  rewrite ap2.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.

  rewrite map_to_ap.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  rewrite ap3.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  reflexivity.
Qed.

(*
Lemma mapdt_list_prefix_preincr
  {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! ApplicativeCommutativeIdempotent G}
  (f: list A * A -> G B) (ctx: list A) (l: list A):
  l <> nil ->
  mapdt_list_prefix (f ⦿ ctx) l = mapdt_list_prefix f l.
Proof.
  introv Hneq.
  induction l.
  - contradiction.
  - rewrite mapdt_list_prefix_spec.
    rewrite mapdt_list_prefix_rw_cons.
  unfold mapdt_list_prefix.
  Search traverse preincr.
  destruct (dec l).
  generalize dependent f.
*)

(*
#[local] Generalizable Variable  G.

Lemma mapdt_list_prefix_rw_preincr {A B} `{Applicative G}:
  forall (g: list A * A -> G B) ctx l,
    l <> nil ->
      mapdt_list_prefix (g ⦿ ctx) l =
        pure (@app B) <⋆> mapdt_list_prefix g ctx <⋆> mapdt_list_prefix g l.
  Proof.
    intros.
    rewrite mapdt_list_prefix_spec.
    rewrite mapdt_list_prefix_spec2.
    destruct l as [| a l].
    - contradiction.
    - rewrite decorate_prefix_list_rw_cons.
      rewrite traverse_list_cons.
      (* LHS *)
      unfold preincr at 1.
      unfold compose at 1.
      unfold incr at 1.
      change (@nil A) with (Ƶ: list A) at 1.
      rewrite monoid_id_l.
      compose near (dec l) on left.
      rewrite traverse_map.
      replace (g ⦿ ctx ∘ incr [a]) with (g ⦿ (ctx ++ [a])).
      2:{ unfold preincr, incr, compose.
          ext [pl pa].
          unfold_ops @Monoid_op_list.
          now rewrite List.app_assoc. }
      (* RHS *)
      cbn.
  Abort.
  *)
#[export] Instance Mapdt_Z: Mapdt_CommIdem Z Z.
Proof.
  intros G Gmap Gpure Gmult A B f.
  exact (traverse (T := Z) f ∘ cojoin (W := Z)).
Defined.

(** ** Kleisli composition *)
(******************************************************************************)
Definition compose_arrows_manual
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B)
  : list A * A -> G1 (G2 C) :=
  map g ∘ traverse (T := Z) f ∘ cojoin (W := Z).

(** *** Inlined version *)
(******************************************************************************)
Definition compose_arrows2
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B)
  : list A * A -> G1 (G2 C) :=
  fun '(l, a) =>
  map (F := G1) g
    (pure (@pair (list B) B) <⋆> mapdt_list_prefix f l <⋆> (f (l, a): G1 B)).

(** *** Another version *)
(******************************************************************************)
Definition compose_arrows3
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B)
  : list A * A -> G1 (G2 C) :=
  map (F := G1) g ∘ mapdt_ci (T := Z) (W := Z) f.

(** *** Equivalence *)
(******************************************************************************)
Lemma compose_arrows_equiv
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1} `{! Applicative G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B):
  g ⋆3_ci f = compose_arrows2 g f.
Proof.
  ext [l a].
  unfold kc3_ci.
  unfold compose.
  cbn.
  reflexivity.
Qed.

Lemma compose_arrows_equiv2
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1} `{! Applicative G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B):
  g ⋆3_ci f = compose_arrows3 g f.
Proof.
  reflexivity.
Qed.

(** *** Preincrement (2025 VERSION!) *)
(******************************************************************************)
Section preincrement_kc.

  Context
    {A B C: Type}
      `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1} `{! Applicative G1}
      `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}.

  Lemma kc_preincr
      (g: list B * B -> G2 C)
      (f: list A * A -> G1 B)
      (ctx: list A):
    (kc3_ci (G1 := G1) (G2 := G2) g f ⦿ ctx) =
      ap (A := Z B) G1 (map (preincr g) (traverse f (decorate_prefix_list ctx))) ∘
        mapdt_ci (T := Z) (W := Z) (f ⦿ ctx).
  Proof.
    unfold kc3_ci.
    unfold_ops @Mapdt_Z.
    reassociate <- on left.
    rewrite (preincr_assoc (map g ∘ traverse f) (cojoin (W := Z))).
    fold_Z; change (Z (Z ?A)) with ((Z ∘ Z) A);
      rewrite (cojoin_Z_rw_preincr_pf ctx).
    reassociate <- on left.
    change (map g ∘ traverse f ∘ ?x ∘ ?y)
      with (map g ∘ (traverse f ∘ x) ∘ y).
    rewrite traverse_Z_map.
    ext [l a]; unfold compose; cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite (traverse_list_app G1).
    compose near (decorate_prefix_list l) on left.
    rewrite traverse_map.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    rewrite <- ap4.
    rewrite ap3.
    rewrite <- ap4.
    repeat rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    reflexivity.
  Qed.

  Lemma ap_spec {G}: forall `{Applicative G} (g: G (A -> B)),
      ap G g = map (F := G) applyFn ∘ mult ∘ pair g.
  Proof.
    reflexivity.
  Qed.

  Lemma mult_pair_spec {G}: forall `{Applicative G} (g: G A),
      mult (F := G) ∘ pair g (B := G B) =
        mult (F := G) ∘ pair g (B := G B).
  Proof.
    reflexivity.
  Qed.

  Lemma kc_preincr2
      (g: list B * B -> G2 C)
      (f: list A * A -> G1 B)
      (ctx: list A):
      (g ⋆3_ci f) ⦿ ctx =
        map (F := G1) g ∘
          ap G1 (map incr (traverse f (decorate_prefix_list ctx))) ∘
          traverse (f ⦿ ctx) ∘ cojoin (W := Z) (A := A).
  Proof.
    rewrite kc_preincr.
    unfold preincr.
    change (?x ○ ?y) with (x ∘ y).
    rewrite <- fun_map_map.
    unfold compose at 3.
    change (ap G1 (map (compose g)
                     (map incr (traverse f (decorate_prefix_list ctx))))) with
      ((ap G1 ∘ map (compose g))
         (map incr (traverse f (decorate_prefix_list ctx)))).
    rewrite <- map_ap2.
    unfold compose at 3.
    reflexivity.
  Qed.

End preincrement_kc.



(** *** Kleisli composition with preincrement *)
(******************************************************************************)
Lemma kc_preincr1
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1} `{! Applicative G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B)
  (ctx: list A): forall l a,
  ((kc3_ci (G1 := G1) (G2 := G2) g f) ⦿ ctx) (l, a) =
    map g (map incr (traverse f (decorate_prefix_list ctx))
             <⋆> traverse (f ⦿ ctx) (decorate_prefix_list l, (l, a))).
Proof.
  intros.
  unfold kc3_ci.
  rewrite (preincr_assoc
              (map (F := G1) (A := Z B) g)
              (mapdt_ci f (W := Z))
              ctx).
  unfold mapdt_ci.
  unfold Mapdt_Z.
  unfold_Z.
  rewrite preincr_assoc.
  fold_Z; change (Z (Z ?A)) with ((Z ∘ Z) A);
    rewrite (cojoin_Z_rw_preincr_pf (A := A) ctx).
  unfold compose at 2 3 5.
  unfold_ops @Cojoin_Z.
  compose near (decorate_prefix_list l, (l, a)) on left.
  rewrite (traverse_Z_incr_lemma3 ctx f (decorate_prefix_list l) l a).
  reflexivity.
Qed.


(*
Context
  {E A B C : Type}
  {G1 G2 : Type -> Type}
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2}.

Section Traverse_Reader.

  Context {E: Type}.

  (*
  #[export] Instance Dist_Reader: Mult (prod E) :=
    strength.
   *)

  #[export] Instance Traverse_Reader: Traverse (prod E).
  Proof.
    intros G Gmap Gpure Gmult A B f.
    exact (strength ∘ map (F := prod E) f).
  Defined.

  #[export] Instance Mapdt_Reader: Mapdt E (prod E).
  Proof.
    intros G Gmap Gpure Gmult A B f.
    exact (strength ∘ cobind f).
  Defined.

End Traverse_Reader.

Definition test
  (g : E * B -> G2 C)
  (f : E * A -> G1 B) :
  (E * A -> G1 (G2 C)) :=
  map g ∘ mapdt f.

Goal test = kc3.
  ext g f.
  unfold kc3.
  unfold test.
  unfold mapdt.
  unfold Mapdt_Reader.
  unfold test.
  reflexivity.
Qed.
*)

(** *** Examples *)
(******************************************************************************)
Section test.

  Import Examples.

  Context (A B: Type) {G} `{Applicative G} (f: list nat * nat -> G nat) (g: list nat * nat -> G nat).
  Eval cbn in mapdt_list_prefix_ f list2.

  Eval cbn in map (mapdt_list_prefix_ g) (mapdt_list_prefix_ f list2).

  Goal map (mapdt_list_prefix_ g) (mapdt_list_prefix_ f list3) <>
         map (mapdt_list_prefix_ g) (mapdt_list_prefix_ f list3).
  Proof.
    cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    unfold compose.
    cbn.
  Abort.

  Goal map (mapdt_list_prefix_ g) (mapdt_list_prefix_ f list3) =
         mapdt_list_prefix_ (G := G ∘ G) (kc3_ci (W := Z) g f) list3.
  Proof.
    cbn.
    unfold kc3_ci.
    unfold compose at 1 2.
  Abort.

End test.

(** * Decorate traversable functor instance *)
(******************************************************************************)

(** ** Unit law *)
(******************************************************************************)
Lemma kdtfci_mapdt1_list_prefix: forall (A : Type),
    mapdt_list_prefix (G := fun A => A) extract = @id (list A).
Proof.
  intros. ext l. induction l.
  - cbn. reflexivity.
  - rewrite mapdt_list_prefix_rw_cons.
    rewrite extract_preincr.
    rewrite IHl.
    reflexivity.
Qed.

(** ** Composition law (Indirect proof) *)
(******************************************************************************)
Lemma kdtfci_mapdt2_list_prefix:
  forall `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    {A B C : Type} (g : Z B -> G2 C) (f : Z A -> G1 B),
    map (mapdt_list_prefix g) ∘ mapdt_list_prefix f =
      mapdt_list_prefix (G := G1 ∘ G2) (g ⋆3_ci f).
Proof.
  intros.
  unfold mapdt_list_prefix at 1 2.
  rewrite <- fun_map_map.
  reassociate -> on left.
  reassociate <- near (map decorate_prefix_list).
  rewrite decorate_commute.
  do 2 reassociate <- on left.
  rewrite (trf_traverse_traverse).
  change (traverse (T := list) ?f ∘ decorate_prefix_list)
    with  (mapdt_list_prefix f).
  rewrite (mapdt_list_prefix_decorate
             (A := A) (B := C) (G := G1 ∘ G2)).
  reflexivity.
Qed.

(** ** Composition law (Direct Proof!) *)
(******************************************************************************)
Lemma kdtfci_mapdt2_list_prefix2_lemma1:
  forall `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    {A B C : Type} (g : Z B -> G2 C) (f : Z A -> G1 B) (ctx: list A),
    mapdt_list_prefix (G := G1 ∘ G2) ((g ⋆3_ci f) ⦿ ctx) =
      mapdt_list_prefix (G := G1 ∘ G2) (g ⋆3_ci (f ⦿ ctx)).
Proof.
  intros.
  rewrite kc_preincr2.
  change (map _ g ∘ ?x ∘ ?y ∘ ?z) with (g ⋆2 (x ∘ y ∘ z)).
  unfold mapdt_list_prefix at 1.
Abort.

Lemma kdtfci_mapdt2_list_prefix_direct_lemma2:
  forall `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    {A B : Type} (f : Z A -> G1 B),
    forall (ctx: list A),
      ap G1 (map (F := G1) incr
               (traverse (T := list) f (decorate_prefix_list ctx)))
        ∘ traverse (T := Z) (f ⦿ ctx) =
        traverse_both (ap G1 (pure (app (A:=B))
                                <⋆> traverse (T := list) f (decorate_prefix_list ctx))
                         ∘ traverse (T := list) (f ⦿ ctx))
          (f ⦿ ctx).
Proof.
  intros.
  ext [binders leaf].
  unfold compose at 1.
  rewrite traverse_Z_spec.
  unfold traverse_both.
  rewrite map_to_ap.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  rewrite ap3.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  (* RHS *)
  unfold compose at 6.
  try rewrite <- ap4.
  rewrite ap2.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  reflexivity.
Qed.


Lemma kdtfci_mapdt2_list_prefix_direct_lemma3:
  forall `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    {A B : Type} (f : Z A -> G1 B),
  forall (ctx: list A),
    traverse (T := Z) f ∘ cojoin (W := Z) ∘ incr ctx =
    ap G1 (map (F := G1) incr (traverse (T := list) f (decorate_prefix_list ctx)))
      ∘ traverse (T := Z) (f ⦿ ctx) ∘ cojoin.

Proof.
  intros.
  symmetry.
  ext [binders leaf].
  unfold compose at 1 2.
  rewrite map_to_ap.
  cbn.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite <- ap4.
  repeat rewrite ap2.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  rewrite ap3.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  change (?l ● ?r) with (l ++ r).
  rewrite decorate_prefix_list_rw_app.
  rewrite (traverse_list_app G1).
  rewrite <- ap4.
  rewrite ap2.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  compose near (decorate_prefix_list binders) on right.
  rewrite traverse_map.
  reflexivity.
Qed.

(*
Lemma kdtfci_mapdt2_list_prefix_direct_lemma4:
  forall `{ApplicativeCommutativeIdempotent G1}
    {A B : Type} (f : Z A -> G1 B) (ctx: list A),
    ap G1 (pure (app (A:=B))
             <⋆> traverse list f (decorate_prefix_list ctx))
      ∘ traverse list (f ⦿ ctx)
    = traverse list f ∘ app (decorate_prefix_list ctx).
Proof.
  intros.
  ext lz.
  unfold compose.
  generalize dependent f.
  induction lz; intros f.
  - cbn.
    rewrite (traverse_list_app G1).
    cbn.
    reflexivity.
  - rewrite traverse_list_cons.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite ap3.
    rewrite <- ap4; repeat rewrite ap2.

    rewrite (traverse_list_app G1).
    rewrite (traverse_list_cons).
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite ap3.
    rewrite <- ap4; repeat rewrite ap2.
Abort.



Lemma kdtfci_mapdt2_list_prefix_direct_lemma5:
  forall `{ApplicativeCommutativeIdempotent G1}
    {A B : Type} (f : Z A -> G1 B) (ctx: A) (l: list A),
    traverse list
      (traverse_both (traverse list f ∘ (app (decorate_prefix_list [ctx]) ∘ map list (incr [ctx])))
         (f ⦿ [ctx]) ∘ cojoin) (decorate_prefix_list l)
    =
      map G1 (map list ∘ incr (A := B)) (traverse list f (decorate_prefix_list [ctx]))
          <⋆>
        (traverse list
           (traverse_both (traverse list f ∘ map list (incr [ctx]))
              (f ⦿ [ctx]) ∘ cojoin) (decorate_prefix_list l)).
Proof.
  intros.
  induction l as [| a as' IHas].
  - unfold compose. cbn.
Abort.

Lemma kdtfci_mapdt2_list_prefix_direct_lemma6:
  forall `{ApplicativeCommutativeIdempotent G1}
    {A B : Type} (f : Z A -> G1 B),
    traverse list (traverse Z f ∘ cojoin) ∘ decorate_prefix_list =
      map G1 decorate_prefix_list ∘ traverse list f ∘ decorate_prefix_list.
Proof.
  intros.
  ext l.
  unfold compose at 1 3 4.
  generalize dependent f.
  induction l as [| a as' IHas]; intro f.
  - cbn.
    rewrite app_pure_natural.
    reflexivity.
  - remember (map G1 decorate_prefix_list (traverse list f (decorate_prefix_list (a :: as')))) as rhs.
    (* LHS *)
    rewrite decorate_prefix_list_rw_cons.
    rewrite traverse_list_cons.
    unfold compose at 1.
    cbn.
    rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    compose near (decorate_prefix_list as') on left.
    rewrite traverse_map.
    reassociate -> on left.
    change (?x ∘ incr ?y) with (x ⦿ y).
    rewrite cojoin_Z_rw_preincr_pf.
    reassociate <- on left.
    rewrite traverse_Z_map.

    (* RHS *)
    rewrite Heqrhs.
    rewrite (decorate_prefix_list_rw_cons a as').
    rewrite traverse_list_cons.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    destruct as'.
    + cbn. admit.
    + cbn.
Abort.

Lemma kdtfci_mapdt2_list_prefix_direct_lemma:
  forall `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    {A B C : Type} (g : Z B -> G2 C) (f : Z A -> G1 B) (ctx: list A),
    map G1 (mapdt_list_prefix g) ∘ (fun l => pure (@app B) <⋆> mapdt_list_prefix f ctx <⋆> mapdt_list_prefix (f ⦿ ctx) l) =
      mapdt_list_prefix (G := G1 ∘ G2) (g ⋆3_ci f) ∘ app ctx.
Proof.
  intros.
  ext l.
  (* LHS *)
  unfold compose at 1.
  rewrite map_ap.
  rewrite map_ap.
  rewrite app_pure_natural.

  (* RHS *)
  unfold compose at 3.
  rewrite mapdt_list_prefix_rw_app.
  unfold pure at 2; unfold Pure_compose.
  rewrite (ap_compose2 G2 G1).
  rewrite (ap_compose2 G2 G1).
  rewrite map_ap.
  rewrite app_pure_natural.
  rewrite app_pure_natural.
  generalize dependent f.
  induction l as [| a as' IHas ]; intro f.
  - cbn.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    unfold pure at 6.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
Abort.

Lemma kdtfci_mapdt2_list_prefix_direct:
  forall `{ApplicativeCommutativeIdempotent G1}
    `{ApplicativeCommutativeIdempotent G2}
    {A B C : Type} (g : Z B -> G2 C) (f : Z A -> G1 B),
    map G1 (mapdt_list_prefix g) ∘ mapdt_list_prefix f =
      mapdt_list_prefix (G := G1 ∘ G2) (g ⋆3_ci f).
Proof.
  intros.
  ext l.
  unfold compose at 1.
  generalize dependent f.
  induction l as [| a as' IHas ]; intro f.
  -  cbn.
     rewrite app_pure_natural.
     reflexivity.
  -  (*
       remember (map G1 (mapdt_list_prefix g) (mapdt_list_prefix f (a :: as')))
       as lhs.
      *)
      (* LHS *)
    rewrite mapdt_list_prefix_rw_cons.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.

    (* RHS *)
    rewrite mapdt_list_prefix_rw_cons.

    (* Unroll applicative composition *)
    unfold_ops @Pure_compose.
    rewrite (ap_compose2 G2 G1).
    rewrite (ap_compose2 G2 G1).
    rewrite app_pure_natural.
    rewrite map_ap.
    rewrite app_pure_natural.

    (* inner *)
    unfold kc3_ci at 1.
    unfold compose at 4 5.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap2.

    (* outer *)
    rewrite kc_preincr2.
    unfold mapdt_list_prefix at 3.
    change (map _ g ∘ ?x ∘ ?y ∘ ?z) with (g ⋆2 (x ∘ y ∘ z)).
    rewrite <- trf_traverse_traverse.
    rewrite <- traverse_map.
Abort.
*)

(** ** Homomorphism law *)
(******************************************************************************)
Lemma kdtfci_morph_list_prefix:
  forall `{ApplicativeMorphism G1 G2 ϕ}
      {A B : Type} (f : Z A -> G1 B),
    mapdt_ci (ϕ B ∘ f) =
      ϕ (list B) ∘ mapdt_ci (W := Z) (T := list) (A := A) (B := B) f.
Proof.
  intros. ext l.
  generalize dependent f.
  induction l as [| b bs IHbs ]; intro f.
  - unfold compose. cbn.
    now rewrite appmor_pure.
  - cbn.
    unfold compose at 3.
    cbn.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    compose near (decorate_prefix_list bs).
    assert (Applicative G2) by now inversion H5.
    rewrite (traverse_map).
    reassociate -> near (incr [b]).
    rewrite <- trf_traverse_morphism.
    assert (Applicative G1) by now inversion H5.
    rewrite (traverse_map).
    reflexivity.
Qed.

(** ** Typeclass Instance *)
(******************************************************************************)
#[export] Instance DecoratedTraversableCommIdemFunctor_list_prefix:
  DecoratedTraversableCommIdemFunctor Z list :=
    { kdtfci_mapdt1 := kdtfci_mapdt1_list_prefix;
      kdtfci_mapdt2 := @kdtfci_mapdt2_list_prefix;
      kdtfci_morph  := @kdtfci_morph_list_prefix
    }.


(*
(** * Proof that decoration is SSR *)
From Tealeaves Require Import
  Classes.Categorical.ContainerFunctor
  Classes.Kleisli.Theory.TraversableFunctor.

Import ContainerFunctor.Notations.

#[export] Instance ToSubset_Z: ToSubset Z := ToSubset_Traverse.

#[export] Instance ToSubset_LZ: ToSubset (list ∘ Z) := ToSubset_Traverse.

Import Subset.Notations.

Lemma decoration_is_SSR1: forall (A: Type) (l: list A),
  forall (a: A), a ∈ l -> tosubset (F := list ∘ Z) (dec l) a.
Proof.
  introv Hin.
  induction l.
  - inversion Hin.
  - inversion Hin.
    + subst.
      rewrite decorate_prefix_list_rw_cons.
      unfold_ops @ToSubset_LZ.
      unfold_ops @ToSubset_Traverse.
      unfold foldMap.
      unfold_ops @Traverse_LZ.
      rewrite traverse_list_cons.
      unfold ap at 1 2.
      unfold_ops @Mult_const.
      unfold_ops @Monoid_op_subset.
      unfold_ops @Pure_const.
      left.
      right. cbn. right. easy.
    + clear Hin. specialize (IHl H).
      clear H.
      rewrite decorate_prefix_list_rw_cons.
      right.
Abort.
*)
