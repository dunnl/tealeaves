From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.TraversableFunctor
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Functors.List
  Functors.Diagonal.

Import Applicative.Notations.
Import Monoid.Notations.
Import DecoratedTraversableFunctor.Notations.
Import Kleisli.TraversableFunctor.Notations.
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
    decorate_prefix_list (a :: l) = ([], a) :: map (incr [a]) (decorate_prefix_list l).
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
      rewrite map_id.
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

(** * The <<Z>> Comonad *)
(******************************************************************************)
Definition Z: Type -> Type := fun A => list A * A.

Definition map_both {A B C D: Type} (f : A -> B) (g: C -> D) : A * C -> B * D :=
  map_snd g ∘ map_fst f.

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

  Lemma cojoin_Z_rw_preincr: forall (ctx: list A)(l: list A) (a: A),
      (cojoin (W := Z) ⦿ ctx) (l, a) =
        (cojoin (W := Z) ⦿ ctx) (l, a).
  Proof.
    intros.
    cbn.
    unfold_ops @Cojoin_Z.
    intros.
    reflexivity.
  Qed.

End Cojoin_Z_rw.

#[export] Instance Extract_Z: Extract Z := fun A => snd.

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

#[local] Notation "'dec'" := decorate_prefix_list.

Section map_args.

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

(** *** Traversable Z *)
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

End traverse_Z_rw.

(** *** Traversable Z *)
(******************************************************************************)
#[export] Instance: TraversableFunctor Z.
Proof.
  constructor.
  - intros. ext [l a].
    cbn. now rewrite trf_traverse_id.
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

(** ** Decomposed version *)
(******************************************************************************)
Definition mapdt_list_prefix
  {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G}
  (f: list A * A -> G B) (l: list A): G (list B) :=
  traverse (T := list) (G := G) f (decorate_prefix_list l).

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

Lemma mapdt_list_prefix_spec2: forall
  {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! Applicative G}
  (f: list A * A -> G B) (l: list A),
    mapdt_list_prefix_ f l = traverse (T := list) f (dec l).
Proof.
  intros.
  generalize dependent f.
  induction l; intro f.
  - reflexivity.
  - rewrite decorate_prefix_list_rw_cons.
    rewrite mapdt_list_prefix_rw_cons.
    rewrite traverse_list_cons.
    rewrite IHl.
    compose near (dec l) on right.
    rewrite traverse_map.
    reflexivity.
Qed.

(** ** Kleisli composition *)
(******************************************************************************)
Definition compose_arrows
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
    (pure (@pair (list B) B) <⋆> mapdt_list_prefix_ f l <⋆> (f (l, a): G1 B)).

(** *** Equivalence *)
(******************************************************************************)
Lemma compose_arrows_equiv
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1} `{! Applicative G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B):
  compose_arrows g f = compose_arrows2 g f.
Proof.
  ext [l a].
  unfold compose_arrows.
  unfold compose.
  cbn.
  do 3 fequal.
  rewrite mapdt_list_prefix_spec2.
  reflexivity.
Qed.

(** *** Preincrement *)
(******************************************************************************)
Lemma compose_arrows_preincr
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1} `{! Applicative G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B)
  (ctx: list A):
  (compose_arrows g f) ⦿ ctx =
    (compose_arrows2 g f) ⦿ ctx.
Proof.
  intros.
  unfold compose_arrows at 1.
  unfold_ops @Cojoin_Z.
  ext [zl za].
  unfold preincr at 1.
  unfold compose at 1 2 3.
  cbn.
  unfold_ops @Monoid_op_list; rewrite decorate_prefix_list_rw_app.
  rewrite (traverse_list_app G1).
  compose near (decorate_prefix_list zl) on left.
  rewrite traverse_map.
  rewrite <- ap4.
  rewrite <- ap4.
  rewrite ap2.
  rewrite ap2.
  rewrite ap2.
  rewrite map_ap.
  rewrite map_ap.
  rewrite map_ap.
  rewrite app_pure_natural.
  (* right hand size *)
  unfold compose_arrows2.
  rewrite map_ap.
  rewrite map_ap.
  rewrite app_pure_natural.
Abort.

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
         mapdt_list_prefix_ (compose_arrows g f) list3.
  Proof.
    cbn.
    unfold compose_arrows.
    unfold compose at 1 2.
    cbn.
    repeat rewrite map_ap.
    do 30 rewrite <- ap4.
    repeat rewrite app_pure_natural.
    repeat rewrite ap2.
    unfold compose.
    cbn.
  Abort.

End test.

(** * Traversal axioms *)
(******************************************************************************)

(** ** Unit law *)
(******************************************************************************)
Definition kdtfunp_axiom1: Prop := forall (A : Type),
    mapdt_list_prefix (G := fun A => A) extract = @id (list A).
Lemma proof1: kdtfunp_axiom1.
Proof.
  unfold kdtfunp_axiom1.
  intros. ext l. induction l.
  - cbn. reflexivity.
  - rewrite mapdt_list_prefix_spec.
    rewrite mapdt_list_prefix_rw_cons.
    rewrite <- mapdt_list_prefix_spec.
    rewrite extract_preincr.
    rewrite IHl.
    reflexivity.
Qed.

(** ** Composition law *)
(******************************************************************************)
Generalizable All Variables.

Section commute_law.

  Context
    `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G}
      `{! ApplicativeCommutativeIdempotent G}.

  Lemma decorate_commute_cons {A B: Type}
    (f: A -> G B) (a: A) (l: list (list A * A)):
    l <> nil ->
    (traverse (T := list) (traverse (T := Z) f) (map (F := list) (incr [a]) l)) =
      map (F := G) (map (F := list) ∘ incr ∘ ret (T := list)) (f a) <⋆>
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
        change ([?x]) with (ret x) at 1.
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
        change ([?x]) with (ret x) at 1.
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

        assert (Htrav_incr_spec: traverse f (incr [a] x) =
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
    (f: A  -> G B) (l: list A):
    map (decorate_prefix_list) (traverse f l) =
      traverse (T := list) (traverse (T := Z) f) (decorate_prefix_list l).
  Proof.
    intros.
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
        change [x] with (ret x) at 1.
        rewrite (traverse_list_one G).
        compose near (f x) on left.
        rewrite (fun_map_map).
        (* RHS *)
        rewrite decorate_prefix_list_rw_one.
        change [?pair] with (ret pair) at 1.
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
        rewrite decorate_prefix_list_rw_cons.
        rewrite traverse_list_cons.

        rewrite traverse_Z_rw.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        rewrite traverse_list_nil.
        rewrite ap2.

        Set Keyed Unification.
        rewrite (decorate_commute_cons f x (dec rest)). (* where prior lemma gets used! *)
        Unset Keyed Unification.
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

End commute_law.

Lemma trav_incr_rw: forall (A B: Type) `{Applicative G} (f: A -> G B) (a: A),
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

#[export] Instance Traverse_LZ: Traverse (list ∘ Z) :=
  fun A B _ _ A B f l => traverse (T := list) (traverse (T := Z) f) l.

Definition kdtfunp_axiom2: Prop :=
  forall `{ApplicativeCommutativeIdempotent G1} `{ApplicativeCommutativeIdempotent G2}
    {A B C : Type} (g : list B * B -> G2 C) (f : list A * A -> G1 B),
    map (mapdt_list_prefix g) ∘ mapdt_list_prefix f =
      mapdt_list_prefix (G := G1 ∘ G2) (compose_arrows g f).

(*
Lemma decorate_commute {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! ApplicativeCommutativeIdempotent G}
  (f: A  -> G B) (l: list A):
  map (F := G) (decorate_prefix_list) (traverse f l) =
    traverse (T := list) (traverse (T := Z) f) (decorate_prefix_list l).
Proof.
  induction l as [|x xs IHx].
  - cbn.
    rewrite app_pure_natural.e
    reflexivity.
  - rewrite traverse_list_cons.
    rewrite decorate_prefix_list_rw_cons.
    rewrite traverse_list_cons.
Abort.
 *)

Lemma proof2: kdtfunp_axiom2.
Proof.
  unfold kdtfunp_axiom2.
  intros.
  ext l.

  Search "mapdt" "spec".
  unfold mapdt_list_prefix.
  change (?f ○ ?g) with (f ∘ g).
  rewrite <- fun_map_map.
  reassociate -> on left.
  reassociate <- near (map dec).
  rewrite decorate_commute.

  rewrite mapdt_list_prefix


  generalize dependent f.
  generalize dependent g.
  unfold compose at 1.
  induction l; intros g f.
  - cbn.
    rewrite app_pure_natural.
    reflexivity.
  - (* left side *)
    rewrite mapdt_list_prefix_spec.
    rewrite mapdt_list_prefix_rw_cons.
    rewrite <- mapdt_list_prefix_spec.
    do 2 rewrite map_ap; rewrite app_pure_natural.
    (* right side *)
    rewrite (mapdt_list_prefix_spec (G := G1 ∘ G2) (compose_arrows g f)).
    rewrite mapdt_list_prefix_rw_cons.
    rewrite <- mapdt_list_prefix_spec.
    rewrite compose_arrows_equiv.
    unfold compose_arrows2.
    rewrite map_ap.
    rewrite map_ap.
    rewrite mapdt_list_prefix_rw_nil.
    rewrite app_pure_natural.
    rewrite ap2.
    rewrite <- map_to_ap.
    unfold compose at 6.
    unfold preincr, compose.
    cbn.
Abort.

Lemma proof2: kdtfunp_axiom2.
Proof.
  unfold kdtfunp_axiom2.
  intros.
  ext l.
  generalize dependent f.
  generalize dependent g.
  unfold compose at 1.
  induction l; intros g f.
  - cbn.
    rewrite app_pure_natural.
    reflexivity.
  - unfold mapdt_list_prefix at 2.
    unfold mapdt_list_prefix at 2.
    unfold compose_arrows.
    rewrite <- (traverse_map (T := list) (G2 := (G1 ∘ G2))
                 (H := Traverse_list)
                 (H2 := @Map_compose G1 G2 H3 H)
                 (H3 := (@Pure_compose G1 G2 H4 H0))
                 (H4 := @Mult_compose G1 G2 H5 H H1)
                 (A := (prod (list A) A)) (C := C)).
    Set Keyed Unification.
    rewrite <- (traverse_map (T := list)  (G2 := (G1 ∘ G2))
                 (H := Traverse_list)
                 (H2 := @Map_compose G1 G2 H3 H)
                 (H3 := (@Pure_compose G1 G2 H4 H0))
                 (H4 := @Mult_compose G1 G2 H5 H H1)).
    unfold traverse.
    try rewrite <- key_principle.
Abort.

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
