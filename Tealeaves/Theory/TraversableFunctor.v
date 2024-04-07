From Tealeaves Require Export
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.Theory.TraversableFunctor
  Classes.Coalgebraic.TraversableFunctor
  Classes.Categorical.ContainerFunctor
  Adapters.KleisliToCoalgebraic.TraversableFunctor.

From Tealeaves Require Export
  Classes.Categorical.ShapelyFunctor
  Theory.Batch
  Functors.List.

About foldMap.

Import Subset.Notations.
Import Applicative.Notations.
Import ContainerFunctor.Notations.
Import ProductFunctor.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import Batch.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables T G A B C M ϕ.

(** * Proof that traversable functors are shapely over lists *)
(******************************************************************************)
Section shapeliness.

  Context
    `{TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  Lemma shapeliness_tactical : forall (A : Type) (b1 b2 : Batch A A (T A)),
      runBatch (const (list A)) (ret (T := list)) _ b1 =
        runBatch (const (list A)) (ret (T := list) (A := A)) _ b2 ->
      mapfst_Batch A unit (const tt) b1 = mapfst_Batch A unit (const tt) b2 ->
      runBatch (fun A => A) id (T A) b1 = runBatch (fun A => A) id (T A) b2.
  Proof.
    introv Hlist Hshape.
    induction b1 as [C c1 | C rest1 IHrest1 a1];
      destruct b2 as [c2 | rest2 a2]; cbn in *.
    - inversion Hshape. reflexivity.
    - inversion Hshape.
    - inversion Hshape.
    - unfold monoid_op, Monoid_op_list in *.
      assert (Hleft := Hlist); apply list_app_inv_l2 in Hleft.
      rename Hlist into Hright;  apply list_app_inv_r2 in Hright.
      injection Hshape; clear Hshape; intro Hshape.
      subst. erewrite IHrest1; auto.
  Qed.

  Theorem shapeliness : forall A (t1 t2 : T A),
      shape t1 = shape t2 /\ tolist t1 = tolist t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    assert (hyp1' : (toBatch (A := unit) (A' := A) ∘ shape) t1 =
                      (toBatch (A := unit) (A' := A) ∘ shape) t2).
    { unfold compose, shape in *. now rewrite hyp1. }
    clear hyp1; rename hyp1' into hyp1.
    unfold shape in hyp1.
    rewrite toBatch_mapfst in hyp1.
    rewrite (tolist_through_runBatch A t1) in hyp2.
    rewrite (tolist_through_runBatch A t2) in hyp2.
    change (id t1 = id t2).
    rewrite id_through_runBatch.
    unfold compose. auto using shapeliness_tactical.
  Qed.

End shapeliness.

(** * Pointwise reasoning for operations *)
(******************************************************************************)
Section pointwise.

  Context
    `{Classes.Kleisli.TraversableFunctor.TraversableFunctor T}
    `{Map T}
    `{Elements T}
    `{! Compat_Map_Traverse T}
    `{! Compat_Elements_Traverse T}.

  Lemma traverse_respectful :
    forall `{Applicative G} `(f1 : A -> G B) `(f2 : A -> G B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> traverse f1 t = traverse f2 t.
  Proof.
    introv ? hyp.
    do 2 rewrite traverse_through_runBatch.
    rewrite (element_through_runBatch2 A B) in hyp.
    unfold compose in *.
    unfold ret in *.
    induction (toBatch t).
    - reflexivity.
    - cbn. fequal.
      + apply IHb. intros.
        apply hyp. now left.
      + apply hyp. now right.
  Qed.

  (** *** Corollaries *)
  (******************************************************************************)
  Corollary traverse_respectful_pure :
    forall `{Applicative G} `(f1 : A -> G A) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = pure a) -> traverse f1 t = pure t.
  Proof.
    intros.
    rewrite <- traverse_purity1.
    now apply traverse_respectful.
  Qed.

  Corollary traverse_respectful_map {A B} :
    forall `{Applicative G} (t : T A) (f : A -> G B) (g : A -> B),
      (forall a, a ∈ t -> f a = pure (g a)) -> traverse f t = pure (map g t).
  Proof.
    intros. rewrite <- (traverse_purity1 (G := G)).
    compose near t on right.
    rewrite traverse_map.
    apply traverse_respectful.
    assumption.
  Qed.

  Corollary traverse_respectful_id {A} :
    forall (t : T A) (f : A -> A),
      (forall a, a ∈ t -> f a = id a) -> traverse (G := fun A => A) f t = t.
  Proof.
    intros.
    change t with (pure (F := fun A => A) t) at 2.
    apply (traverse_respectful_pure (G := fun A => A)).
    assumption.
  Qed.

  Corollary map_respectful : forall `(f1 : A -> B) `(f2 : A -> B) (t : T A),
      (forall (a : A), a ∈ t -> f1 a = f2 a) -> map f1 t = map f2 t.
  Proof.
    introv hyp.
    rewrite map_to_traverse.
    rewrite map_to_traverse.
    apply (traverse_respectful (G := fun A => A)).
    assumption.
  Qed.

  #[export] Instance ContainerFunctor_Traverse:
    ContainerFunctor T.
  Proof.
    constructor.
    - rewrite compat_element_traverse.
      typeclasses eauto.
    - typeclasses eauto.
    - intros. now apply map_respectful.
  Qed.

End pointwise.

(** * New length *)
(******************************************************************************)

Section length.

  Context
    `{TraversableFunctor T} `{Map T}
     `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}.

  Lemma plength_eq_length :
    forall {A} {B} (t: T A),
     length_Batch (toBatch (A' := B) t) = plength t.
  Proof.
    intros.
    unfold plength.
    rewrite (foldMap_through_runBatch2 A B).
    unfold compose.
    induction (toBatch t).
    - reflexivity.
    - cbn.
      rewrite IHb.
      unfold_ops @NaturalNumbers.Monoid_op_plus.
      lia.
  Qed.

  Lemma plength_eq_length': forall {A} (t: T A),
      plength t = length_Batch (toBatch (A' := False) t).
  Proof.
    intros.
    symmetry.
    apply plength_eq_length.
  Qed.

  Lemma length_Batch_independent: forall `(t: T A) B C,
      length_Batch (toBatch (A' := B) t) =
        length_Batch (toBatch (A' := C) t).
  Proof.
    intros.
    rewrite length_Batch_spec.
    rewrite length_Batch_spec.
    compose near t on left.
    compose near t on right.
    rewrite <- traverse_through_runBatch.
    rewrite <- traverse_through_runBatch.
    rewrite (traverse_const2 _ B C).
    reflexivity.
  Qed.

End length.

(** * Deconstructing with refinement-type vectors *)
(******************************************************************************)
Section deconstruction.

  Context
    `{Traverse T}
    `{! Kleisli.TraversableFunctor.TraversableFunctor T}
    `{Map T}
    `{! Compat_Map_Traverse T}
    `{ToBatch T}
    `{! Compat_ToBatch_Traverse}
    `{! Elements T}
     `{! Compat_Elements_Traverse T}.

  Definition trav_contents {A} (t: T A):
    Vector (plength t) A :=
    let v : Vector (length_Batch (toBatch (A' := False) t)) A
      := Batch_contents (toBatch t)
    in coerce_Vector_length (plength_eq_length t) v.

  Definition trav_contents_list {A} (t: T A):
    Vector (plength t) A :=
    let v : Vector (length_Batch (toBatch (A' := False) t)) A
      := Batch_contents (toBatch t)
    in coerce_Vector_length (plength_eq_length t) v.

  Definition trav_make {A B} (t: T A):
    Vector (plength t) B -> T B :=
    (fun v =>
       let v' := coerce_Vector_length (eq_sym (plength_eq_length t)) v
       in Batch_make (toBatch t) v').

  Generalizable Variable v.

  (** ** Lemmas regarding <<trav_make>> *)
  (******************************************************************************)
  Section trav_make_lemmas.

    Context
      {A B : Type}.

    Lemma trav_make_sim1:
      forall (t : T A) `{v1 ~~ v2},
        trav_make (B := B) t v1 = trav_make t v2.
    Proof.
      intros.
      unfold trav_make.
      apply Batch_make_sim1.
      vector_sim.
    Qed.

    Lemma trav_make_sim2:
      forall `(t1 : T A) (t2: T A)
        `(v1: Vector (plength t1) B)
        `(v2: Vector (plength t2) B),
        t1 = t2 ->
        Vector_sim v1 v2 ->
        trav_make t1 v1 = trav_make t2 v2.
    Proof.
      intros.
      subst.
      now apply trav_make_sim1.
    Qed.

  End trav_make_lemmas.

  (** ** Miscellaneous *)
  (******************************************************************************)
  Section list.

    Lemma tolist_trav_contents `{t: T A}:
      Vector_to_list A (trav_contents t) = List.rev (tolist t).
    Proof.
      intros.
      unfold trav_contents.
      rewrite (tolist_through_runBatch False).
      generalize (plength_eq_length (B := False) t).
      intros Heq.
      generalize dependent (plength t).
      induction (toBatch (A' := False) t); intros n Heq.
      - reflexivity.
      - rewrite runBatch_rw2.
        rewrite Batch_contents_rw2.
        unfold Vector_to_list.
        rewrite <- coerce_Vector_contents.
        unfold length_Batch at 1. (* hidden *)
        rewrite proj_vcons.
        cbn.
        unfold_ops @Monoid_op_list.
        unfold_ops @Return_list.
        rewrite List.rev_unit.
        fequal.
        cbn in Heq.
        assert (Hlen: length_Batch b = (n -1)) by lia.
        specialize (IHb (n - 1) Hlen).
        change (fun a => a :: nil) with (@ret list _ A).
        cbn in IHb.
        change (@app A) with (@Monoid_op_list A).
        rewrite <- IHb.
        unfold Vector_to_list.
        rewrite <- coerce_Vector_contents.
        reflexivity.
    Qed.

    Lemma Batch_contents_tolist:
      forall {A B} (t: T A),
        Vector_to_list A (Batch_contents (toBatch (A' := B) t)) =
          List.rev (tolist t).
    Proof.
      intros.
      rewrite tolist_to_foldMap.
      rewrite (foldMap_through_runBatch2 A B).
      unfold compose.
      induction (toBatch t).
      - reflexivity.
      - cbn.
        rewrite Vector_to_list_vcons.
        rewrite IHb.
        unfold_ops @Monoid_op_list @Return_list.
        rewrite List.rev_unit.
        reflexivity.
    Qed.

    Lemma Batch_contents_toBatch_sim:
      forall {A B B'} (t: T A),
        Batch_contents
          (toBatch (A' := B) t) ~~
          Batch_contents (toBatch (A' := B') t).
    Proof.
      intros.
      unfold Vector_sim.
      change (proj1_sig ?v) with (Vector_to_list _ v).
      rewrite Batch_contents_tolist.
      rewrite Batch_contents_tolist.
      reflexivity.
    Qed.

    Lemma shape_toBatch_spec: forall (A B: Type) (t: T A),
        shape (toBatch (A' := B) t) =
          toBatch (A' := B) (shape t).
    Proof.
      intros.
      compose near t on right.
      unfold shape at 2.
      rewrite toBatch_mapfst.
      reflexivity.
    Qed.

    Lemma toBatch_shape:
      forall {A' B} `(t1: T A) (t2: T A'),
        shape t1 = shape t2 ->
        shape (F := BATCH1 B (T B))
              (toBatch (A' := B) t1) =
          shape (F := BATCH1 B (T B))
                (toBatch (A' := B) t2).
    Proof.
      introv Hshape.
      do 2 rewrite shape_toBatch_spec.
      rewrite Hshape.
      reflexivity.
    Qed.

    (** ** Batch_to_list *)
    (******************************************************************************)
    Section Batch.

      Definition Batch_to_list: forall `(b: Batch A B C), list A.
      Proof.
        intros. apply (tolist (F := BATCH1 B C) b).
      Defined.

      Lemma Batch_contents_list: forall `(b: Batch A B C),
          proj1_sig (Batch_contents b) = List.rev (Batch_to_list b).
      Proof.
        intros.
        induction b.
        - reflexivity.
        - cbn.
          rewrite proj_vcons.
          rewrite IHb.
          rewrite <- List.rev_unit.
          reflexivity.
      Qed.

      Lemma Batch_to_list_rw2 {A B C}: forall (b: Batch A B (B -> C)) (a: A),
          Batch_to_list (b ⧆ a) = Batch_to_list b ++ (a::nil).
      Proof.
        intros.
        cbn.
        reflexivity.
      Qed.

    End Batch.

  End list.

  (** ** Lens-like laws *)
  (******************************************************************************)
  Section lens_laws.

    (** *** get-put *)
    (******************************************************************************)
    Lemma trav_get_put `{t: T A}:
      trav_make t (trav_contents t) = t.
    Proof.
      unfold trav_make, trav_contents.
      enough (cut: Batch_make
                     (toBatch t)
                     (coerce eq_sym (plength_eq_length t)
                       in coerce (plength_eq_length (B := False) t)
                         in Batch_contents (toBatch t)) =
                     Batch_make (toBatch t) (Batch_contents (toBatch t))).
      rewrite cut.
      rewrite Batch_make_contents.
      compose near t.
      now rewrite trf_extract.
      { apply Batch_make_sim1.
        vector_sim.
        apply Batch_contents_toBatch_sim.
      }
    Qed.

    Lemma toBatch_trav_make {A A' B} {t: T A} {v: Vector (plength t) B}:
      toBatch (A' := A') (trav_make t v) =
        Batch_replace_contents
          (toBatch (A' := A') t)
          (coerce eq_sym (plength_eq_length t) in v).
    Proof.
      unfold trav_make.
      rewrite Batch_make_compose_rw1.
      rewrite Batch_replace_spec.
      apply Batch_make_sim2; vector_sim.
      compose near t.
      now rewrite <- trf_duplicate.
    Qed.

    (** *** put-get *)
    (******************************************************************************)
    Lemma trav_contents_make {A} {t: T A} {v: Vector (plength t) A}:
      trav_contents (trav_make t v) ~~ v.
    Proof.
      unfold trav_contents.
      vector_sim.
      rewrite toBatch_trav_make.
      rewrite Batch_put_get.
      vector_sim.
    Qed.

    (** *** put-put *)
    (******************************************************************************)
    Lemma trav_make_make
            `(t: T A) `(v: Vector (plength t) B)
            `(v1: Vector _ B')
            (v2: Vector _ B')
            (pf: v1 ~~ v2):
      trav_make (trav_make t v) v1 =
        trav_make t v2.
    Proof.
      unfold trav_make at 1.
      unfold trav_make at 7.
      apply Batch_make_sim3.
      - symmetry.
        rewrite toBatch_trav_make.
        apply Batch_shape_replace_contents.
      - vector_sim.
    Qed.

    Notation "'precoerce' Hlen 'in' F" :=
      (F ○ coerce_Vector_length Hlen)
        (at level 10, F at level 20).

    Lemma trav_same_shape
            `(t1: T A) `(t2: T A'):
      shape t1 = shape t2 ->
      forall B, trav_make (B := B) t1 ~!~ trav_make t2.
    Proof.
      intros.
      unfold trav_make.
      apply Vector_coerce_fun_sim_l'.
      apply Vector_coerce_fun_sim_r'.
      apply Batch_make_shape.
      apply toBatch_shape.
      assumption.
    Qed.

  End lens_laws.

  (** ** Representation theorems *)
  (******************************************************************************)
  Lemma traverse_repr:
    forall `{Applicative G} (A B: Type) (t: T A) (f: A -> G B),
      traverse f t =
        map (trav_make t) (forwards (traverse (mkBackwards ∘ f) (trav_contents t))).
  Proof.
    intros.
    rewrite traverse_through_runBatch.
    unfold compose.
    rewrite runBatch_repr2.
    unfold trav_make, trav_contents.
    rewrite (traverse_Vector_coerce _ _ _ (plength_eq_length t)).
    change_left (
        map (Batch_make (toBatch t))
            (map
               (fun v : Vector (plength t) B =>
                  coerce eq_sym (plength_eq_length (B := B) t) in v)
               (forwards
                  (traverse (mkBackwards ∘ f)
                            (coerce (plength_eq_length (B := B) t) in
                              Batch_contents (toBatch t)))))).
    compose near ((forwards
                     (traverse (mkBackwards ∘ f)
                               (coerce (plength_eq_length (B := B) t)
                                 in Batch_contents (toBatch t))))).
    rewrite (fun_map_map).
    fequal.
    fequal.
    fequal.
    apply Vector_eq.
    apply Vector_coerce_sim_l'.
    apply Vector_coerce_sim_r'.
    eapply Batch_contents_toBatch_sim.
  Qed.

  (** ** Lemmas regarding <<plength>> *)
  (******************************************************************************)
  Lemma plength_trav_make: forall `(t: T A) `(v: Vector _ B),
      plength t = plength (trav_make t v).
  Proof.
    intros.
    unfold plength at 1 2.
    do 2 change (fun (x:?X) => 1) with (const (A := X) 1).
    do 2 rewrite (foldMap_through_runBatch2 _ B).
    unfold compose.
    rewrite (@toBatch_trav_make A B B t v).
    rewrite <- (runBatch_const_contents (G := @const Type Type nat)).
    reflexivity.
  Qed.

End deconstruction.

#[export] Instance Elements_Vector {n}: Elements (Vector n).
unfold Vector.
intro X.
intros [l pf].
intro x.
exact (x ∈ l).
Defined.

(** * Elements of <<Batch>> *)
(******************************************************************************)
Require Import ContainerFunctor.

Import ContainerFunctor.Notations.
Import Applicative.Notations.

#[export] Instance Elements_Batch1 {B C}: Elements (BATCH1 B C) :=
  Elements_Traverse.

Section pw_Batch.

  Lemma foldMap_Batch_rw2: forall {A B C: Type} `{Monoid M}
      (f : A -> M) (a: A) (rest: Batch A B (B -> C)),
      foldMap (T := BATCH1 B C) f (rest ⧆ a) =
        foldMap f rest ● f a.
  Proof.
    intros.
    unfold foldMap.
    rewrite traverse_Batch_rw2.
    reflexivity.
  Qed.

  Definition element_of_Step1 {A B C:Type}:
    forall (a' : A) (rest: Batch A B (B -> C)),
      forall (a : A),
      element_of (F := BATCH1 B (B -> C)) rest a ->
      element_of (F := BATCH1 B C) (Step rest a') a.
  Proof.
    introv.
    unfold_ops @Elements_Batch1 @Elements_Traverse.
    introv Hin.
    change ((evalAt a ∘ foldMap (T := BATCH1 B (B -> C))
                    (ret (T := subset))) rest) in Hin.
    change ((evalAt a ∘ foldMap (T := BATCH1 B C)
                    (ret (T := subset))) (rest ⧆ a')).
    rewrite (foldMap_morphism
               (T := BATCH1 B (B -> C))
               _ _ (ϕ := evalAt a)) in Hin.
    rewrite (foldMap_morphism
               (T := BATCH1 B C)
               _ _ (ϕ := evalAt a)).
    rewrite foldMap_Batch_rw2.
    now left.
  Defined.

  Definition element_of_Step2 {A B C:Type}:
    forall (rest: Batch A B (B -> C)) (a: A),
      element_of (F := BATCH1 B C) (Step rest a) a.
  Proof.
    intros.
    unfold_ops @Elements_Batch1 @Elements_Traverse.
    change ((evalAt a ∘ foldMap (T := BATCH1 B C)
                    (ret (T := subset))) (rest ⧆ a)).
    rewrite (foldMap_morphism
               (T := BATCH1 B C)
               _ _ (ϕ := evalAt a)).
    rewrite foldMap_Batch_rw2.
    now right.
  Qed.

  Lemma element_of_Step_spec: forall `(b: Batch A B (B -> C)) a a',
      a' ∈ (b ⧆ a) = (a' ∈ b \/ a' = a).
  Proof.
    intros.
    rewrite in_to_foldMap.
    rewrite in_to_foldMap.
    rewrite foldMap_Batch_rw2.
    reflexivity.
  Qed.

  Definition sigMapP (A: Type) (P Q: A -> Prop) (Himpl: forall a, P a -> Q a):
    sig P -> sig Q :=
    fun σ => match σ with
          | exist _ a h => exist Q a (Himpl a h)
          end.

  Fixpoint elt_decorate
   {A B C: Type}
   (b : Batch A B C):
    Batch {a|element_of (F := BATCH1 B C) b a} B C :=
    match b with
    | Done c => Done c
    | Step rest a =>
        Step (map (F := BATCH1 B (B -> C))
                  (sigMapP A
                           (element_of (F := BATCH1 B (B -> C)) rest)
                           (element_of (F := BATCH1 B C) (Step rest a))
                           (element_of_Step1 a rest)
                  )
                  (elt_decorate rest))
             (exist _ a (element_of_Step2 rest a))
    end.


  Definition runBatch_pw
               {A B C} (G : Type -> Type)
               `{Applicative G}:
    forall (b: Batch A B C) `(f1 : {a | element_of (F := BATCH1 B C) b a} -> G B), G C.
  Proof.
    intros.
    induction b.
    - apply (pure c).
    - apply (ap G (A := B)).
      apply IHb.
      + intros [a' a'in].
        apply f1.
        exists a'.
        rewrite element_of_Step_spec.
        now left.
      + apply f1.
        exists a.
        rewrite element_of_Step_spec.
        now right.
  Defined.

End pw_Batch.
