From Tealeaves Require Import
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Categorical.ApplicativeCommutativeIdempotent
  Functors.Diagonal.

Import List.ListNotations.
Import Applicative.Notations.

(** * Examples of CI-Traversable Homomorphisms *)
(******************************************************************************)
Section ci_traversable_hom_examples.

  Context
    `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G}
      `{! ApplicativeCommutativeIdempotent G}.

  (** ** List reversal *)
  (******************************************************************************)
  Lemma rev_traverse_ci_hom {A B: Type}
    (f: A  -> G B) (l: list A):
    map (F := G) (List.rev (A := B))
      (traverse f l) = traverse f (List.rev l).
  Proof.
    induction l.
    - cbn. rewrite app_pure_natural. reflexivity.
    - rewrite traverse_list_cons.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      (* rhs *)
      cbn.
      rewrite (traverse_list_app G).
      rewrite <- IHl.
      rewrite <- ap_map.
      rewrite app_pure_natural.
      change [a] with (ret a).
      rewrite (traverse_list_one G).
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite (ap_ci2 _ (traverse f l) (f a)).
      rewrite app_pure_natural.
      fequal.
  Qed.

  (** ** "Duplicate first element" *)
  (******************************************************************************)
  Definition dupfst {A:Type} (l: list A): list A :=
    match l with
    | nil => nil
    | cons a l' =>  cons a (cons a l')
    end.

  Lemma dupfst_pointfree: forall (A: Type) (a: A) (l: list A),
      (* (compose dec ∘ cons) a l = dec (cons a l).*)
      (*
    (compose dupfst ∘ cons) a l = (precompose dup ∘ cons) a l.
       *)
      1 = 1.
  Proof.
    reflexivity.
  Qed.

  Lemma key_principle_simplified {A B: Type}
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

  (** ** "Pair all with first element" *)
  (******************************************************************************)
  Definition pairall {A:Type} (l: list A): list (A * A) :=
    match l with
    | nil => nil
    | cons a l' =>  cons (a, a) (map (pair a) l')
    end.

  Lemma pairall_spec {A} (a: A) (l: list A):
    pairall (a :: l) = map (pair a) (a :: l).
  Proof.
    cbn. reflexivity.
  Qed.

  Definition apply {A B}: (A -> B) * A -> B :=
    fun '(f, a) => f a.

  Lemma pairall_cons_pf {A:Type}:
    (compose pairall ∘ (@cons A)) =
      (uncurry compose ∘ map_snd cons ∘ map_fst (fun a => map (F := list) (pair a)) ∘ (@dup A)).
  Proof.
    reflexivity.
  Qed.


  Lemma pairall_commute_cons_simpler {A B: Type}
    (f: A -> G B) (a: A) (x: A) (l: list A):
    map (map ∘ pair) (f a) <⋆> traverse f l = traverse (traverse f) (map (pair a) l) ->
    map (map ∘ pair) (f a) <⋆> traverse f (x :: l) = traverse (traverse f) (map (pair a) (x :: l)).
  Proof.
    introv IH.
    (* RHS *)
    rewrite map_list_cons.
    rewrite (traverse_list_cons _ _ _ _ (a, x)).
    rewrite traverse_Diagonal_rw.
    rewrite <- IH.
    clear IH.
    (* LHS *)
    rewrite traverse_list_cons.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    change (fun f0 => f0 cons) with
      (evalAt (A := B -> list B -> list B) (B := B -> list B -> list (B * B)) cons).
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- map_to_ap.
    compose near (f a) on left.
    rewrite (fun_map_map).
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    do 8 rewrite <- ap4.
    repeat rewrite ap2.
    rewrite <- map_to_ap.
    rewrite <- ap_map.
    rewrite map_ap.
    compose near (f a) on right.
    compose near (f a) on right.
    rewrite (fun_map_map).
    unfold compose at 7.
    rewrite (ap_ci2 _ _ (f a)).
    compose near (f a) on right.
    compose near (f a) on right.
    rewrite (fun_map_map).
    unfold compose at 7.
    rewrite map_to_ap.
    rewrite map_to_ap.
    rewrite ap_cidup.
    rewrite <- map_to_ap.
    rewrite app_pure_natural.
    rewrite <- map_to_ap.
    fequal.
  Qed.

  Lemma pairall_commute_cons {A B: Type}
    (f: A -> G B) (a: A) (l: list A):
    l <> nil ->
    map (F := G) (fun b => map (F := list) (pair b)) (f a) <⋆> (traverse (T := list) f l) =
      traverse (traverse (T := fun A => A * A) f) (map (pair a) l).
  Proof.
    introv Hnotnil.
    induction l.
    - contradiction.
    - destruct l.
      + cbn.
        rewrite map_to_ap.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.
        fequal.
      + specialize (IHl ltac:(easy)).
        remember (a1 :: l).
        apply pairall_commute_cons_simpler.
        assumption.
  Qed.

  Lemma pairall_commute {A B: Type}
    (f: A  -> G B) (l: list A):
    map (F := G) pairall (traverse f l) =
      traverse (T := list) (traverse (T := fun A => A * A) f) (pairall l).
  Proof.
    destruct l.
    - cbn.
      rewrite app_pure_natural.
      reflexivity.
    - rewrite pairall_spec.
      rewrite <- pairall_commute_cons.
      rewrite traverse_list_cons.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite map_to_ap.
      rewrite <- ap4.
      rewrite <- ap4.
      rewrite <- ap4.
      rewrite ap2.
      rewrite ap2.
      rewrite <- (ap4 _ _ (f a)).
      rewrite ap2.
      rewrite ap2.
      rewrite ap3.
      rewrite <- ap4.
      rewrite ap2.
      rewrite ap2.
      rewrite ap_cidup.
      rewrite app_pure_natural.
      reflexivity.
      easy.
  Qed.

End ci_traversable_hom_examples.
