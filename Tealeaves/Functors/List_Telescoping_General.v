From Tealeaves Require Import
  Classes.Kleisli.DecoratedTraversableFunctor
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.TraversableFunctor
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Functors.List.

Import Applicative.Notations.
Import Monoid.Notations.
Import DecoratedTraversableFunctor.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import List.ListNotations.

Fixpoint decorate_telescoping_list_rec {A: Type} (ctx: list A) (l: list A):
  list (list A * A) :=
  match l with
  | nil => nil
  | x :: xs =>
      (* (ctx, x) :: decorate_telescoping_list_rec (x :: ctx) xs *)
      (ctx, x) :: decorate_telescoping_list_rec (ctx ++ [x]) xs
  end.

Definition decorate_telescoping_list {A: Type} (l: list A):
  list (list A * A) := decorate_telescoping_list_rec nil l.

Fixpoint decorate_telescoping_list_alt {A: Type} (l: list A):
  list (list A * A) :=
  match l with
  | nil => nil
  | x :: xs =>
      (nil, x) :: map (F := list) (incr [x]) (decorate_telescoping_list_alt xs)
  end.

Definition list1 := [ 3 ; 5 ; 7 ; 8 ].

Compute decorate_telescoping_list_alt list1.

Lemma decorate_telescoping_list_equiv_rec : forall (A: Type) (ctx: list A) (l: list A),
    decorate_telescoping_list_rec ctx l =
      map (F := list) (incr ctx) (decorate_telescoping_list_alt l).
Proof.
  intros.
  generalize dependent ctx. induction l; intro ctx.
  - reflexivity.
  - cbn.
    unfold Monoid_op_list at 1, monoid_op at 1.
    rewrite List.app_nil_r.
    fequal.
    compose near (decorate_telescoping_list_alt l) on right.
    rewrite (fun_map_map).
    rewrite incr_incr.
    unfold_ops @Monoid_op_list.
    rewrite IHl.
    reflexivity.
Qed.

Lemma decorate_telescoping_list_equiv: forall (A: Type) (l: list A),
    decorate_telescoping_list l = decorate_telescoping_list_alt l.
Proof.
  intros.
  assert (incr [] = id (A := list A * A)).
  { now ext [l' a]. }
  specialize (decorate_telescoping_list_equiv_rec A nil l).
  rewrite H.
  rewrite fun_map_id.
  trivial.
Qed.


Section decorate_telescoping_list_rw.

  Context
    {A : Type}.

  Lemma decorate_telescoping_list_rw_nil:
    decorate_telescoping_list_alt (@nil A) = (@nil (list A * A)).
  Proof.
    reflexivity.
  Qed.

  Lemma decorate_telescoping_list_rw_cons: forall (a: A) (l: list A),
    decorate_telescoping_list_alt (a :: l) = ([], a) :: map (incr [a]) (decorate_telescoping_list_alt l).
  Proof.
    intros. cbn.
    reflexivity.
  Qed.

  Lemma decorate_telescoping_list_rw_app: forall (l1 l2: list A),
      decorate_telescoping_list_alt (l1 ++ l2) =
        decorate_telescoping_list_alt l1 ++ map (incr l1) (decorate_telescoping_list_alt l2).
  Proof.
    intros. induction l1.
    - cbn.
      change (incr []) with (incr (A := A) (Ƶ: list A)).
      rewrite incr_zero.
      rewrite map_id.
      reflexivity.
    - (* left *)
      rewrite <- List.app_comm_cons.
      rewrite decorate_telescoping_list_rw_cons.
      rewrite IHl1.
      rewrite map_list_app.
      compose near (decorate_telescoping_list_alt l2) on left.
      rewrite (fun_map_map).
      rewrite incr_incr.
      (* right *)
      rewrite decorate_telescoping_list_rw_cons.
      reflexivity.
  Qed.

End decorate_telescoping_list_rw.

Fixpoint mapdt_list_telescope
  {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
  {A B : Type} (f : list A * A -> G B) (l : list A)
  : G (list B) :=
  match l with
  | nil => pure (@nil B)
  | x :: xs =>
      pure (@List.cons B) <⋆> f (nil, x) <⋆>
        mapdt_list_telescope (f ⦿ [x]) xs
  end.

Section mapdt_list_telescope_rw.
  Context
    {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
      `{! Applicative G}
      {A B : Type}.

  Lemma mapdt_list_telescope_rw_nil: forall (f : list A * A -> G B),
    mapdt_list_telescope f nil = pure nil.
  Proof. reflexivity. Qed.

  Lemma mapdt_list_telescope_rw_cons: forall (f : list A * A -> G B) a l,
      mapdt_list_telescope f (a :: l) =
        pure (@List.cons B) <⋆> f (nil, a) <⋆> mapdt_list_telescope (f ⦿ [a]) l.
  Proof. reflexivity. Qed.

  Lemma mapdt_list_telescope_rw_app: forall (g: list A * A -> G B) l l',
      mapdt_list_telescope g (l ++ l') =
        pure (@app B) <⋆> mapdt_list_telescope g l <⋆> mapdt_list_telescope (g ⦿ l) l'.
  Proof.
    intros g l. generalize dependent g.
    induction l. intros g l'.
    - cbn. change (g ⦿ []) with (g ⦿ Ƶ). rewrite preincr_zero.
      rewrite ap2.
      change (app []) with (@id (list B)).
      rewrite ap1. reflexivity.
    - intros g l'.
      rewrite <- List.app_comm_cons.
      rewrite mapdt_list_telescope_rw_cons.
      rewrite IHl.
      rewrite mapdt_list_telescope_rw_cons.
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

End mapdt_list_telescope_rw.

Definition Z: Type -> Type := fun A => list A * A.

Definition map_both {A B C D: Type} (f : A -> B) (g: C -> D) : A * C -> B * D :=
  map_snd g ∘ map_fst f.

#[export] Instance Map_Z: Map Z := fun A B f => map_both (map (F := list) f) f.
#[export] Instance Functor_Z: Functor Z.
Proof.
  constructor.
  - intros. ext [l a]. cbn. now rewrite fun_map_id.
  - intros. ext [l a]. cbn. unfold id.
    compose near l on left. rewrite fun_map_map. reflexivity.
Qed.

From Tealeaves Require Import Categorical.Comonad.

#[export] Instance Cojoin_Z: Cojoin Z := fun A '(l, a) => (decorate_telescoping_list_alt l, (l, a)).

Section Cojoin_Z_rw.

  Context {A: Type}.

  Lemma cojoin_Z_rw_nil: forall (a: A),
      cojoin (W := Z) (@nil A, a) = (nil, (nil, a)).
  Proof.
    reflexivity.
  Qed.

  Lemma cojoin_Z_rw_cons: forall (a1 a2: A) (l: list A),
      cojoin (W := Z) (a1 :: l, a2) = (([], a1) :: map (incr [a1]) (decorate_telescoping_list_alt l), (a1 :: l, a2)).
  Proof.
    unfold_ops @Cojoin_Z.
    intros.
    rewrite decorate_telescoping_list_rw_cons.
    reflexivity.
  Qed.

  Lemma cojoin_Z_rw_app: forall (a: A) (l1 l2: list A),
      cojoin (W := Z) (l1 ++ l2, a) = (decorate_telescoping_list_alt l1 ++ map (incr l1) (decorate_telescoping_list_alt l2), (l1 ++ l2, a)).
  Proof.
    unfold_ops @Cojoin_Z.
    intros.
    rewrite decorate_telescoping_list_rw_app.
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

#[export] Instance Natural_decorate_telescoping_list: Natural (@decorate_telescoping_list_alt).
Proof.
  constructor; try typeclasses eauto.
  intros. unfold compose. ext l.
  generalize dependent f.
  induction l; intro f.
  - reflexivity.
  - (* left *)
    rewrite decorate_telescoping_list_rw_cons at 1.
    unfold_ops @Map_compose.
    rewrite map_list_cons at 1.
    compose near (decorate_telescoping_list_alt l).
    rewrite (fun_map_map).
    (* right *)
    rewrite map_list_cons at 1.
    rewrite decorate_telescoping_list_rw_cons.
    rewrite <- IHl.
    compose near (decorate_telescoping_list_alt l) on right.
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
  rewrite <- (natural (Natural := Natural_decorate_telescoping_list)).
  reflexivity.
Qed.

#[local] Notation "'dec'" := decorate_telescoping_list_alt.

Section map_args.
  Arguments map (F)%function_scope {Map} {A B}%type_scope f%function_scope _.


  Lemma cojoin_assoc_lemma: forall (A : Type) (l: list A),
      dec (dec l) = map list cojoin (dec l).
  Proof.
    intros.
    induction l.
    - reflexivity.
    - (* left *)
      rewrite decorate_telescoping_list_rw_cons at 1.
      rewrite decorate_telescoping_list_rw_cons at 1.
      compose near (dec l) on left.
      rewrite <- (natural (Natural := Natural_decorate_telescoping_list)).
      change (map (A := ?A) (B := ?B)
                (fun A0 : Type => list (list A0 * A0))) with
        (map (list ∘ Z) (A := A) (B := B)).
      unfold_ops @Map_compose.
      unfold compose at 1.
      compose near (dec (dec l)).
      rewrite (fun_map_map (F := list)).
      (* right *)
      rewrite decorate_telescoping_list_rw_cons at 1.
      rewrite map_list_cons.
      unfold cojoin at 1, Cojoin_Z at 1.
      rewrite decorate_telescoping_list_rw_nil.
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
      compose near (decorate_telescoping_list_alt l).
      rewrite (fun_map_map).
      assert (extract (W := Z) ∘ incr [a0] = extract (A := A) (W := Z)).
      { ext [l' a']. reflexivity. }
      unfold Z in H at 1; cbn in H.
      rewrite H.
      assumption.
  - apply cojoin_assoc.
Qed.

Definition mapdt
  {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G}
  (f: list A * A -> G B) (l: list A): G (list B) :=
  traverse (T := list) (G := G) f (decorate_telescoping_list_alt l).

Lemma mapdt_spec
  {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! Applicative G}
  (f: list A * A -> G B) (l: list A):
  mapdt f l = mapdt_list_telescope f l.
Proof.
  generalize dependent f.
  unfold mapdt. induction l; intro f.
  - reflexivity.
  - cbn. specialize (IHl (f ⦿ [a])).
    compose near (decorate_telescoping_list_alt l) on left.
    rewrite traverse_map.
    rewrite <- IHl.
    unfold preincr. unfold incr.
    reflexivity.
Qed.

Lemma mapdt_spec2: forall
  {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! Applicative G}
  (f: list A * A -> G B) (l: list A),
    mapdt_list_telescope f l = traverse (T := list) f (dec l).
Proof.
  intros.
  generalize dependent f.
  induction l; intro f.
  - reflexivity.
  - rewrite decorate_telescoping_list_rw_cons.
    rewrite mapdt_list_telescope_rw_cons.
    rewrite traverse_list_cons.
    rewrite IHl.
    compose near (dec l) on right.
    rewrite traverse_map.
    reflexivity.
Qed.

#[export] Instance: Traverse Z.
Proof.
  intros G MapG PureG MultG A B f.
  unfold Z.
  intros [l a].
  (* exact (mult (map_both (traverse (T := list) f) f (l, a))).*)
  exact (pure pair <⋆> (traverse (T:=list) f l) <⋆> f a).
Defined.

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


Definition compose_arrows
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B)
  : list A * A -> G1 (G2 C) :=
  map g ∘ traverse (T := Z) f ∘ cojoin (W := Z).

Definition compose_arrows2
  {A B C: Type}
  `{G1: Type -> Type} `{Map G1} `{Mult G1} `{Pure G1}
  `{G2: Type -> Type} `{Map G2} `{Mult G2} `{Pure G2}
  (g: list B * B -> G2 C) (f: list A * A -> G1 B)
  : list A * A -> G1 (G2 C) :=
  fun '(l, a) =>
  map (F := G1) g
    (pure (@pair (list B) B) <⋆> mapdt_list_telescope f l <⋆> (f (l, a): G1 B)).


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
  rewrite mapdt_spec2.
  reflexivity.
Qed.

Section test.
  Context (A B: Type) {G} `{Applicative G} (f: list nat * nat -> G nat) (g: list nat * nat -> G nat).

  Definition list2 : list nat :=[ 2 ; 3 ].

  Eval cbn in mapdt_list_telescope f list2.

  Eval cbn in map (mapdt_list_telescope g) (mapdt_list_telescope f list2).

  Definition list3 := [ 2 ].

  Goal map (mapdt_list_telescope g) (mapdt_list_telescope f list3) <>
         map (mapdt_list_telescope g) (mapdt_list_telescope f list3).
  Proof.
    cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    unfold compose.
    cbn.
  Abort.

  Goal map (mapdt_list_telescope g) (mapdt_list_telescope f list3) =
         mapdt_list_telescope (compose_arrows g f) list3.
  Proof.
    cbn.
    unfold compose_arrows.
    unfold compose at 1 2.
    cbn.
    repeat rewrite map_ap.
    repeat rewrite <- ap4.
    repeat rewrite app_pure_natural.
    repeat rewrite ap2.
    unfold compose.
  Abort.

End test.


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
  unfold_ops @Monoid_op_list; rewrite decorate_telescoping_list_rw_app.
  rewrite (traverse_list_app G1).
  compose near (decorate_telescoping_list_alt zl) on left.
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

Definition kdtfunp_axiom1: Prop := forall (A : Type),
    mapdt (G := fun A => A) extract = @id (list A).
Lemma proof1: kdtfunp_axiom1.
Proof.
  unfold kdtfunp_axiom1.
  intros. ext l. induction l.
  - cbn. reflexivity.
  - rewrite mapdt_spec.
    rewrite mapdt_list_telescope_rw_cons.
    rewrite <- mapdt_spec.
    rewrite extract_preincr.
    rewrite IHl.
    reflexivity.
Qed.

Generalizable All Variables.


Lemma key_principle {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! Applicative G}
  (f: A  -> G B) (l: list A):
  map (F := G) (decorate_telescoping_list_alt) (traverse f l) =
    traverse (T := list) (traverse (T := Z) f) (decorate_telescoping_list_alt l).
Proof.
  intros.
  induction l.
  - rewrite traverse_list_nil.
    rewrite app_pure_natural.
    rewrite decorate_telescoping_list_rw_nil.
    rewrite traverse_list_nil.
    reflexivity.
  - rewrite traverse_list_cons.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    (* right *)
    rewrite decorate_telescoping_list_rw_cons.
    rewrite traverse_list_cons.
    cbn. (* todo traverse_Z_rw_nil *)
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    compose near (dec l).
    rewrite (traverse_map).
    unfold compose at 1 2.
    cbn.
Abort.

Fixpoint dupfst {A:Type} (l: list A): list A :=
  match l with
  | nil => nil
  | cons a l' =>  cons a (cons a l')
  end.

Definition dup {A:Type} := fun (a: A) => (a, a).
(*
Lemma dupfst_pointfree: forall (A: Type) (a: A) (l: list A),
    (* (compose dec ∘ cons) a l = dec (cons a l).*)
    (compose dupfst ∘ cons) a l = (precompose dup ∘ cons) a l.
Proof.
  reflexivity.
Qed.
 *)

Lemma ap_ci: forall `{ApplicativeCommutativeIdempotent G} {A B: Type} (f: G (A -> B)) (a: G A),
    f <⋆> a = (map evalAt a) <⋆> f.
Proof.
  intros.
  unfold ap.
  inversion H2.
  rewrite appci_commutative.
  compose near (a ⊗ f).
  rewrite (fun_map_map).
  rewrite (app_mult_natural_l G).
  compose near (a ⊗ f) on right.
  rewrite (fun_map_map).
  fequal.
  ext [x y].
  cbn. reflexivity.
Qed.

Definition double_input {A B: Type} (f: A -> A -> B): A -> B :=
  uncurry f ∘ dup.

Lemma ap_cidup: forall `{ApplicativeCommutativeIdempotent G} {A B: Type} (f: G (A -> A -> B)) (a: G A),
    f <⋆> a <⋆> a = (map double_input f) <⋆> a.
Proof.
  intros.
  unfold ap.
  inversion H2.
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a ⊗ a).
  rewrite (fun_map_map).
  rewrite <- (app_assoc_inv G).
  rewrite appci_idempotent.
  rewrite (app_mult_natural_r G).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  (* rhs *)
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  fequal.
  ext [x y].
  cbn. reflexivity.
Qed.

Lemma key_principle_simplified {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! ApplicativeCommutativeIdempotent G}
  (f: A  -> G B) (l: list A):
  map (F := G) dupfst (traverse f l) = traverse f (dupfst l).
Proof.
  intros.
  induction l.
  - cbn. rewrite app_pure_natural. reflexivity.
  - rewrite traverse_list_cons.
    cbn.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- ap4.
    rewrite (ap_ci (pure (@cons B)) (f a)) at 2.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    repeat rewrite ap2.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite ap_cidup.
    rewrite app_pure_natural.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    fequal.
Qed.

Lemma dec_pointfree: forall (A: Type) (a: A) (l: list A),
    (* (compose dec ∘ cons) a l = dec (cons a l).*)
    (compose dec ∘ cons) a l = ((precompose (map (incr [a]) ∘ dec)) ∘ precompose (pair nil) cons) a l.
Proof.
  intros.
  About mult.
  unfold compose, precompose. cbn.
Abort.

Lemma key_principle {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G} `{! Applicative G}
  (f: A  -> G B) (l: list A):
  map (F := G) (decorate_telescoping_list_alt) (traverse f l) =
    traverse (T := list) (traverse (T := Z) f) (decorate_telescoping_list_alt l).
Proof.
  intros.
  induction l.
  - rewrite traverse_list_nil.
    rewrite app_pure_natural.
    rewrite decorate_telescoping_list_rw_nil.
    rewrite traverse_list_nil.
    reflexivity.
  - rewrite traverse_list_cons.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    (* right *)
    rewrite decorate_telescoping_list_rw_cons.
    rewrite traverse_list_cons.
    cbn.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    compose near (dec l).
    rewrite (traverse_map).
Admitted.


Definition kdtfunp_axiom2: Prop :=
  forall `{ApplicativeCommutativeIdempotent G1} `{ApplicativeCommutativeIdempotent G2}
    {A B C : Type} (g : list B * B -> G2 C) (f : list A * A -> G1 B),
    map (mapdt g) ∘ mapdt f = mapdt (G := G1 ∘ G2) (compose_arrows g f).


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
  - (* left side *)
    rewrite mapdt_spec.
    rewrite mapdt_list_telescope_rw_cons.
    rewrite <- mapdt_spec.
    do 2 rewrite map_ap; rewrite app_pure_natural.
    (* right side *)
    rewrite (mapdt_spec (G := G1 ∘ G2) (compose_arrows g f)).
    rewrite mapdt_list_telescope_rw_cons.
    rewrite <- mapdt_spec.
    rewrite compose_arrows_equiv.
    unfold compose_arrows2.
    rewrite map_ap.
    rewrite map_ap.
    rewrite mapdt_list_telescope_rw_nil.
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
  - unfold mapdt at 2.
    unfold mapdt at 2.
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
    rewrite <- key_principle.


(** * Proof that decoration is SSR *)
From Tealeaves Require Import
  Classes.Categorical.ContainerFunctor
  Classes.Kleisli.Theory.TraversableFunctor.

Import ContainerFunctor.Notations.

#[export] Instance ToSubset_Z: ToSubset Z := ToSubset_Traverse.

#[export] Instance Traverse_LZ: Traverse (list ∘ Z) :=
  fun A B _ _ A B f l => traverse (T := list) (traverse (T := Z) f) l.
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
      rewrite decorate_telescoping_list_rw_cons.
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
      rewrite decorate_telescoping_list_rw_cons.
      right.
Abort.
