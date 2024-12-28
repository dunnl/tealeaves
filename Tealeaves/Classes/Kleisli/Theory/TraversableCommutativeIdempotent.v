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

  (*

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
    map (F := G) (map (F := list) ∘ pair) (f a) <⋆> (traverse (T := list) f l) =
      traverse (traverse (T := fun A => A * A) f) (map (pair a) l).
  Proof.
    introv Hnotnil.
    induction l as [| x xs IHxs ].
    - contradiction.
    - destruct xs.
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
      + specialize (IHxs ltac:(easy)).
        remember (a0 :: xs).
        apply pairall_commute_cons_simpler.
        assumption.
  Qed.
  *)
Lemma compose_compose {A B C D: Type}:
    forall (g: B -> C) (h: C -> D),
      (compose h ∘ compose (A := A) g) = compose (h ∘ g).
  Proof.
    reflexivity.
  Qed.

  Lemma pairall_commute_cons_Inductive_Step {A B: Type}
    (f: A -> G B) (a: A) (x: A) (l: list A):
    traverse (traverse f) (map (pair a) l) = map (map ∘ pair) (f a) <⋆> traverse f l ->
    traverse (traverse f) (map (pair a) (x :: l)) = map (map ∘ pair) (f a) <⋆> traverse f (x :: l).
  Proof.
    introv IH.
    (* LHS *)
    rewrite map_list_cons.
    rewrite (traverse_list_cons _ _ _ _ (a, x)).
    rewrite IH.
    clear IH.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite traverse_Diagonal_rw.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.

    rewrite <- ap_map.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    reassociate <- near (compose (precompose (map ∘ pair))).
    rewrite compose_compose.
    reassociate <- near (precompose (map ∘ pair)).

    rewrite (ap_ci2 _ (f a) (f x)).
    rewrite app_pure_natural.

    rewrite ap_cidup.
    rewrite map_ap.
    rewrite app_pure_natural.

    rewrite (ap_ci2 _ (f x) (f a)).
    rewrite app_pure_natural.

    (* RHS *)
    rewrite (traverse_list_cons _ _ _ _ x).
    rewrite <- (ap4 (map (map ∘ pair) (f a)) _ (traverse f l)).
    rewrite pure_ap_map.
    rewrite <- (ap4 _ (pure cons) (f x)).
    rewrite pure_ap_map.
    rewrite ap3.
    rewrite pure_ap_map.

    (* Done ! *)
    rewrite map_to_ap.
    reflexivity.
  Qed.

  Lemma pairall_commute_cons {A B: Type}
    (f: A -> G B) (a: A) (l: list A):
    l <> nil ->
    traverse (traverse (T := fun A => A * A) f) (map (pair a) l) =
    map (F := G) (map (F := list) ∘ pair) (f a) <⋆> (traverse (T := list) f l).
  Proof.
    introv Hnotnil.
    induction l as [| x xs IHxs ].
    - contradiction.
    - clear Hnotnil.
      destruct xs as [| y ys ].
      + clear IHxs.

        (* LHS *)
        rewrite map_list_one.
        change ([(a, x)]) with (ret (a, x)).
        rewrite (traverse_list_one G).
        rewrite traverse_Diagonal_rw.
        rewrite map_ap.
        rewrite map_ap.
        rewrite app_pure_natural.

        (* RHS *)
        change ([x]) with (ret x) at 1.
        rewrite (traverse_list_one G).

        rewrite (map_to_ap (G := G)).
        rewrite (map_to_ap (G := G)).

        rewrite <- ap4.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        rewrite ap3.
        rewrite <- ap4.
        rewrite ap2.
        rewrite ap2.

        (* Done! *)
        reflexivity.

      + specialize (IHxs ltac:(discriminate)).
        remember (y :: ys) as rest.
        apply pairall_commute_cons_Inductive_Step.
        assumption.
  Qed.

  (*
  Lemma pairall_commute {A B: Type}
    (f: A  -> G B) (l: list A):
    map (F := G) pairall (traverse f l) =
      traverse (T := list) (traverse (T := fun A => A * A) f) (pairall l).
  Proof.
    destruct l.
    - cbn.
      rewrite app_pure_natural.
      reflexivity.
    - (* RHS *)
      rewrite pairall_spec.
      rewrite pairall_commute_cons; [| discriminate].
      (* ^^ rely on (a :: l <> []) *)
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
  Qed.
*)


  Lemma pairall_commute2 {A B: Type}
    (f: A  -> G B) (l: list A):
    map (F := G) pairall (traverse f l) =
      traverse (T := list) (traverse (T := fun A => A * A) f) (pairall l).
  Proof.
    destruct l as [| a as'].
    - cbn.
      rewrite app_pure_natural.
      reflexivity.
    - (* LHS *)
      rewrite traverse_list_cons.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.

      rewrite pairall_spec.
      rewrite pairall_commute_cons; [| discriminate].
      rewrite map_to_ap.

      rewrite traverse_list_cons.
      rewrite <- ap4.
      rewrite <- (ap4 (pure compose) _ (f a)).
      rewrite ap2.
      rewrite ap2.
      rewrite <- ap4.
      rewrite <- (ap4 (pure compose) _ (f a)).
      rewrite ap2.
      rewrite ap2.

      rewrite ap3.
      rewrite <- (ap4 (pure (evalAt cons)) _ (f a)).
      rewrite ap2.
      rewrite ap2.
      rewrite ap_cidup.
      rewrite app_pure_natural.
      reflexivity.
  Qed.

End ci_traversable_hom_examples.
