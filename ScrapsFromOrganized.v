(** ** Some things to think about *)

(** ** <<Join>> in terms of Kleisli Composition *)
(******************************************************************************)
Check (@kc T Return_inst (@Bind_Binddt W T T Bindd_T_inst)
         (T (T A)) (T A) A (@id (T A)) (@id (T (T A)))).

Many interesting properties have the forms like
  join = id ⋆ id
           cojoin = (id ⋆1 id)
                       or some such






(** * Traversable Functors *)


  Context
    `{Map T}
    `{ToBatch T}
    `{Traverse T}
    `{! Kleisli.TraversableFunctor.TraversableFunctor T}
    `{! Compat_Map_Traverse T}
    `{! Compat_ToBatch_Traverse}.

  (** *** Factoring operations through <<toBatch>> *)
  (******************************************************************************)
  Lemma traverse_through_runBatch
    `{Applicative G} `(f: A -> G B) :
    traverse f = runBatch f ∘ toBatch.
  Proof.
    rewrite toBatch_to_traverse.
    rewrite trf_traverse_morphism.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary map_through_runBatch {A B: Type} (f: A -> B) :
    map f = runBatch (F := fun A => A) f ∘ toBatch.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch: forall (A: Type),
      id = runBatch (F := fun A => A) id ∘ toBatch (T := T) (A' := A).
  Proof.
    intros.
    rewrite <- trf_traverse_id.
    rewrite (traverse_through_runBatch (G := fun A => A)).
    reflexivity.
  Qed.

  (** *** Naturality of <<toBatch>> *)
  (******************************************************************************)
  Lemma toBatch_mapfst: forall (A B A': Type) (f: A -> B),
      toBatch (A := B) (A' := A') ∘ map f =
        mapfst_Batch f ∘ toBatch (A := A) (A' := A').
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite traverse_map.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism (morphism := mapfst_Batch1_Hom f)).
    rewrite ret_natural.
    reflexivity.
  Qed.

  Lemma toBatch_mapsnd: forall (X A A': Type) (f: A -> A'),
      mapsnd_Batch f ∘ toBatch =
        map (map f) ∘ toBatch (A := X) (A' := A).
  Proof.
    intros.
    rewrite toBatch_to_traverse.
    rewrite (trf_traverse_morphism (morphism := mapsnd_Batch2_Hom f)).
    rewrite ret_dinatural.
    rewrite toBatch_to_traverse.
    rewrite map_traverse.
    reflexivity.
  Qed.



  (** *** Factoring derived operations through <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMap_through_runBatch1 {A : Type} `{Monoid M} : forall `(f : A -> M),
      foldMap f = runBatch (F:= const M) f (B := False) ∘
                    toBatch (A := A) (A' := False).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Lemma foldMap_through_runBatch2 `{Monoid M} : forall (A fake : Type) `(f : A -> M),
      foldMap f = runBatch (F := const M) f (B := fake) ∘
                    toBatch (A' := fake).
  Proof.
    intros.
    rewrite foldMap_to_traverse1.
    change (fun _ : Type => M) with (const (A := Type) M).
    rewrite (traverse_const1 fake).
    rewrite (traverse_through_runBatch (G := const M)).
    reflexivity.
  Qed.


  Corollary tolist_through_runBatch {A : Type} (tag : Type) `(t : T A) :
    tolist t =
      runBatch (F := const (list A))
        (ret (T := list) : A -> const (list A) tag)
        (B := tag) (toBatch (A' := tag) t).
  Proof.
    rewrite (tolist_to_traverse2 A tag).
    rewrite (traverse_through_runBatch (G := const (list A))).
    reflexivity.
  Qed.

  Context
    `{ToSubset T}
      `{! Compat_ToSubset_Traverse T}.

  Lemma tosubset_through_runBatch1 : forall (A : Type),
      tosubset =
        runBatch (F := const (A -> Prop))
          (ret (T := subset) (A := A)) (B := False) ∘
          toBatch (A' := False).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_through_runBatch1.
    reflexivity.
  Qed.

  Lemma tosubset_through_runBatch2 : forall (A tag : Type),
      tosubset =
        runBatch (F := const (A -> Prop))
          (ret (T := subset)) (B := tag) ∘
          toBatch (A' := tag).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite (foldMap_through_runBatch2 A tag).
    reflexivity.
  Qed.





















  (** * Traversable Monads *)

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    `{ret_inst : Return T}
    `{Map_inst : Map U}
    `{Traverse_inst : Traverse U}
    `{Bind_inst : Bind T U}
    `{Bindt_inst : Bindt T U}
    `{Bindt_T_inst : Bindt T T}
    `{! Compat_Map_Bindt T U}
    `{! Compat_Traverse_Bindt T U}
    `{! Compat_Bind_Bindt T U}
    `{! Functor U}
    `{! TraversableRightPreModule T U}.

  Lemma bindt_through_runBatch `{Applicative G} `(f : A -> G (T B)):
    bindt (U := U) f = runBatch f ∘ toBatch6 B.
  Proof.
    unfold_ops @ToBatch6_Bindt.
    rewrite (ktm_morph (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary bind_through_runBatch `{Applicative G} `(f : A -> T B):
    bind (U := U) f = runBatch (F := fun A => A) f ∘ toBatch6 B.
  Proof.
    unfold_ops @ToBatch6_Bindt.
    rewrite bind_to_bindt.
    rewrite bindt_through_runBatch.
    reflexivity.
  Qed.

  Corollary traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse (T := U) f = runBatch (map ret ∘ f) ∘ toBatch6 B.
  Proof.
    rewrite traverse_to_bindt.
    rewrite bindt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
    map (F := U) f = runBatch (F := fun A => A) (ret (T := T) ∘ f) ∘ toBatch6 B.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch : forall (A : Type),
      id (A := U A) = runBatch (F := fun A => A) (ret (T := T)) ∘ toBatch6 A.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := U)).
    rewrite map_through_runBatch.
    reflexivity.
  Qed.

End runBatch.

(** * Other Properties *)
(******************************************************************************)

(** ** Relating <<toBatch6>> with <<toBatch>> *)
(******************************************************************************)
Lemma toBatch6_toBatch
  `{Kleisli.TraversableMonad.TraversableMonad T}
  `{Traverse_inst: Traverse U}
  `{Bindt_U_inst: Bindt T U}
  `{ToBatch_U_inst: ToBatch U}
  `{! Compat_Traverse_Bindt T U}
  `{! Compat_ToBatch_Traverse}
  `{! Kleisli.TraversableMonad.TraversableRightPreModule T U}
  {A B: Type} (t: U A) : True.
  toBatch B t = mapsnd_Batch (ret (T := T)) (toBatch6 B t).
Proof.
  intros.
  rewrite toBatch_to_traverse.
  rewrite traverse_to_bindt.
  unfold_ops @ToBatch6_Bindt.
  compose near t on right.
  rewrite (ktm_morph (G1 := Batch A (T B)) (G2 := Batch A B)
                     (ϕ := fun C => mapsnd_Batch (ret (T := T)))).
  rewrite ret_dinatural.
  reflexivity.
Qed.

  (** *** Naturality of <<toBatch>> *)
  (******************************************************************************)
  Lemma toBatch6_mapfst (U: Type -> Type)
    `{Return_T: Return T}
    `{Bindt_TT: Bindt T T}
    `{Bindt_TU: Bindt T U}
    `{Map_U: Map U}
    `{! Compat_Map_Bindt T U}
    `{! Kleisli.TraversableMonad.TraversableMonad T}
    `{! Kleisli.TraversableMonad.TraversableRightPreModule T U}
    {A B: Type} (f: A -> B) {C: Type}:
    toBatch6 C ∘ map (F := U) f =
      mapfst_Batch _ _ f ∘ toBatch6 C.
  Proof.
    intros.
    unfold_ops @ToBatch6_Bindt.
    rewrite (bindt_map (G2 := Batch B (T C))).
    rewrite (bindt_through_runBatch (G := Batch B (T C))).
    rewrite (bindt_through_runBatch (G := Batch A (T C))).
    ext t.
    unfold compose.
    induction (toBatch6 C t).
    - cbn. reflexivity.
    - do 2 rewrite runBatch_rw2.
      rewrite IHb.
      rewrite mapfst_Batch2.
      reflexivity.
  Qed.






















  (** * From DTFs *)

(** ** Relating <<toBatch3>> with <<toBatch>> *)
(******************************************************************************)
(*
Lemma toBatch3_toBatch
  `{Traverse_inst: Traverse T}
  `{Mapdt_inst: Mapdt E T}
  `{ToBatch_inst: ToBatch T}
  `{! Compat_Traverse_Mapdt}
  `{! Compat_ToBatch_Traverse}
  `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  {A B: Type} :
  toBatch (A := A) (A' := B) = mapfst_Batch extract ∘ toBatch3.
Proof.
  intros.
  unfold_ops @ToBatch3_Mapdt.
  rewrite toBatch_to_traverse.
  rewrite traverse_to_mapdt.
  rewrite <- (kdtfun_morph
               (G1 := Batch (E * A) B)
               (G2 := Batch A B)
               (ϕ := fun C => mapfst_Batch extract)).
  rewrite ret_natural.
  reflexivity.
Qed.
 *)

(** ** <<mapdt>> via  *)
(******************************************************************************)
Lemma runBatch_toBatch3
  `{Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  `{Applicative G} `(f: E * A -> G B) :
  runBatch f ∘ toBatch3 = mapdt (E := E) (T := T) f.
Proof.
  intros.
  unfold_ops @ToBatch3_Mapdt.
  rewrite <- kdtfun_morph.
  rewrite (runBatch_batch G).
  reflexivity.
Qed.

(** ** Naturality of <<toBatchDM>> *)
(******************************************************************************)
Lemma toBatch3_mapdt
  `{Mapdt_inst: Mapdt E T}
  `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  `{Applicative G}
  {A A' B: Type} (f: E * A -> G A') :
  map (F := G) (toBatch3 (A := A') (B := B)) ∘ mapdt (T := T) f =
    traverse (T := BATCH1 B (T B)) (strength ∘ cobind f) ∘ toBatch3.
Proof.
  rewrite (traverse_spec G).
  rewrite (runBatch_toBatch3 (A := A) (E := E) (T := T)
             (B := B) (G := G ∘ Batch (E * A') B)).
  unfold_ops @ToBatch3_Mapdt.
  rewrite kdtfun_mapdt2.
  unfold kc6.
  reflexivity.
Qed.

Lemma toBatch3_mapd
  `{Mapd_inst: Mapd E T}
  `{Mapdt_inst: Mapdt E T}
  `{! Compat_Mapd_Mapdt}
  `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  {A A' B: Type} (f: E * A -> A') :
  toBatch3 ∘ mapd (T := T) f =
    mapfst_Batch (cobind f) ∘ toBatch3 (A := A) (B := B).
Proof.
  unfold_ops @ToBatch3_Mapdt.
  rewrite mapdt_mapd.
  rewrite <- (kdtfun_morph
             (G1 := Batch (E * A) B)
             (G2 := Batch (E * A') B)
             (ϕ := fun C => mapfst_Batch (cobind f))).
  reflexivity.
Qed.

Lemma toBatch3_map
  `{Map_inst: Map T}
  `{Mapdt_inst: Mapdt E T}
  `{! Compat_Map_Mapdt}
  `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}
  {A A' B: Type} (f: A -> A') {C: Type} :
  toBatch3 ∘ map (F := T) f = mapfst_Batch (map f) ∘ toBatch3 (A := A) (B := B).
Proof.
  unfold_ops @ToBatch3_Mapdt.
  rewrite mapdt_map.
  rewrite <- (kdtfun_morph (H6 := mapfst_Batch1_Hom (map f))
               (ϕ := fun C => mapfst_Batch (map f))).
  rewrite ret_natural.
  reflexivity.
Qed.

Lemma toBatch3_mapfst3
  `{Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctorFull E T}
  `{ToBatch_inst: ToBatch T}
  `{! Compat_ToBatch_Traverse}
  {A A' B: Type} (f: E * A -> A') :
  toBatch (A := A') (A' := B) ∘ mapd (T := T) f =
    mapfst_Batch f ∘ toBatch3 (T := T) (A := A) (B := B).
Proof.
  rewrite toBatch3_toBatch.
  reassociate -> on left.
  rewrite toBatch3_mapd.
  reassociate <-.
  rewrite (mapfst_mapfst_Batch).
  rewrite (kcom_cobind0).
  reflexivity.
Qed.

(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.

  Context
    `{Map_inst: Map T}
    `{Mapd_inst: Mapd E T}
    `{Traverse_inst: Traverse T}
    `{Mapdt_inst: Mapdt E T}
    `{Subset_inst: ToSubset T}
    `{! Compat_Map_Mapdt}
    `{! Compat_Mapd_Mapdt}
    `{! Compat_Traverse_Mapdt}
    `{! Compat_ToSubset_Traverse T}
    `{! Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor E T}.

  Theorem toBatch3_toBatch
    {A B} `{ToBatch T} `{! Compat_ToBatch_Traverse}:
    toBatch (T := T) (A := A) (A' := B) =
      mapfst_Batch extract ∘ toBatch3 (T := T) (A := A).
  Proof.
    rewrite toBatch_to_traverse.
    rewrite traverse_to_mapdt.
    unfold toBatch3, ToBatch3_Mapdt.
    rewrite <- (kdtfun_morph (T := T)
                 (ϕ := fun X =>
                         mapfst_Batch (B := B) (C := X)
                           (A1 := E * A) (A2 := A)
                           (extract (W := prod E) (A := A)))
                 (batch B)).
    reflexivity.
  Qed.

  Theorem mapdt_through_runBatch `{Applicative G} `(f : E * A -> G B) :
    mapdt f = runBatch f ∘ toBatch3.
  Proof.
    intros. unfold_ops @ToBatch3_Mapdt.
    rewrite <- kdtfun_morph.
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Corollary traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse f = runBatch (f ∘ extract (W := (E ×))) ∘ toBatch3.
  Proof.
    rewrite traverse_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapd_through_runBatch `(f : E * A -> B) :
      mapd f = runBatch (F := fun A => A) f ∘ toBatch3.
  Proof.
    intros.
    rewrite mapd_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
      map f = runBatch (F := fun A => A) (f ∘ extract) ∘ toBatch3.
  Proof.
    intros.
    rewrite map_to_mapdt.
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  (** *** <<foldMapd>> a special case of <<runBatch>> *)
  (******************************************************************************)
  Lemma foldMapd_through_runBatch1 {A} `{Monoid M} : forall `(f : E * A -> M),
      foldMapd f = runBatch (F := const M) f (C := T False) ∘ toBatch3 (B := False).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_through_runBatch (G := const M)).
    reflexivity.
  Qed.

  Lemma foldMapd_through_runBatch2 `{Monoid M} : forall (A fake : Type) `(f : E * A -> M),
      foldMapd f = runBatch (F := const M) f (C := T fake) ∘ toBatch3 (B := fake).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite (mapdt_constant_applicative2 False False fake).
    rewrite mapdt_through_runBatch.
    reflexivity.
  Qed.

  (** *** Factoring through <<runBatch>> *)
  (******************************************************************************)
  Corollary toctxlist_through_runBatch3 {A : Type} (tag : Type) :
    toctxlist = runBatch (B := tag) (F := const (list (E * A))) (ret (T := list))
                  ∘ toBatch3.
  Proof.
    rewrite (toctxlist_to_mapdt2 A tag).
    now rewrite mapdt_through_runBatch.
  Qed.


  Corollary toctxset_through_runBatch1 {A : Type} :
    toctxset (F := T) = runBatch (B := False) (F := const (subset (E * A)))
                                (ret (T := subset)) ∘ toBatch3.
  Proof.
    rewrite (toctxset_to_mapdt1 A).
    now rewrite (mapdt_through_runBatch).
  Qed.

  Corollary toctxset_through_runBatch2 {A tag : Type} :
    toctxset (F := T) = runBatch (B := tag) (F := const (subset (E * A)))
                                (ret (T := subset)) ∘ toBatch3.
  Proof.
    rewrite (toctxset_to_mapdt2 A tag).
    now rewrite (mapdt_through_runBatch).
  Qed.

  Corollary ctx_elements_through_runBatch1 {A : Type} {p:E * A}:
    element_ctx_of (T := T) p =
      runBatch (B := False) (F := const Prop)
        (H0 := @Mult_const _ Monoid_op_or)
        (H1 := @Pure_const _ Monoid_unit_false)
        {{p}} ∘ toBatch3.
  Proof.
    rewrite element_ctx_of_to_foldMapd.
    rewrite foldMapd_through_runBatch1.
    reflexivity.
  Qed.

End runBatch.










(** Dec Tra Monads *)


Lemma toBatch6_to_toBatch7
  `{Monoid_op W}
  `{Monoid_unit W}
  `{Return T}
  `{Mapdt W U}
  `{Binddt W T U}
  `{Binddt W T T}
  `{! Compat_Mapdt_Binddt W T U}
  `{! DecoratedTraversableRightPreModule W T U}:
  forall A A' t,
    toBatch6 (A := A) (B := A') t =
      mapsnd_Batch (B1 := A') (B2 := T A')
        (ret (T := T) (A := A')) (toBatch7 (A := A) (B := A') t).
Proof.
  intros.
  unfold_ops @ToBatch6_Mapdt.
  unfold_ops @ToBatch7_Binddt.
  rewrite mapdt_to_binddt.
  compose near t on right.
  rewrite (kdtm_morph (A := A) (T := T)
             (Batch _ (T A'))
             (Batch _ A')
             (ϕ := fun C => mapsnd_Batch (B1 := A') (B2 := T A') ret)
             (batch (A := W * A) (T A'))).
  reflexivity.
Qed.


(** ** Factoring operations through <<toBatch>> *)
(******************************************************************************)
Section runBatch.


  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Monoid_inst: Monoid W}.

  Context
    `{ret_inst : Return T}
      `{Map_T_inst : Map T}
      `{Mapd_T_inst : Mapd W T}
      `{Traverse_T_inst : Traverse T}
      `{Bind_T_inst : Bind T T}
      `{Mapdt_T_inst : Mapdt W T}
      `{Bindd_T_inst : Bindd W T T}
      `{Bindt_T_inst : Bindt T T}
      `{Binddt_T_inst : Binddt W T T}
      `{ToSubset_T_inst: ToSubset T}
      `{! Compat_Map_Binddt W T T}
      `{! Compat_Mapd_Binddt W T T}
      `{! Compat_Traverse_Binddt W T T}
      `{! Compat_Bind_Binddt W T T}
      `{! Compat_Mapdt_Binddt W T T}
      `{! Compat_Bindd_Binddt W T T}
      `{! Compat_Bindt_Binddt W T T}.

  Context
    `{Map_U_inst : Map U}
      `{Mapd_U_inst : Mapd W U}
      `{Traverse_U_inst : Traverse U}
      `{Bind_U_inst : Bind T U}
      `{Mapdt_U_inst : Mapdt W U}
      `{Bindd_U_inst : Bindd W T U}
      `{Bindt_U_inst : Bindt T U}
      `{Binddt_U_inst : Binddt W T U}
      `{ToSubset_U_inst: ToSubset U}
      `{! Compat_Map_Binddt W T U}
      `{! Compat_Mapd_Binddt W T U}
      `{! Compat_Traverse_Binddt W T U}
      `{! Compat_Bind_Binddt W T U}
      `{! Compat_Mapdt_Binddt W T U}
      `{! Compat_Bindd_Binddt W T U}
      `{! Compat_Bindt_Binddt W T U}
      `{! Compat_ToSubset_Traverse T}
      `{! Compat_ToSubset_Traverse U}.

  Context
    `{Monad_inst : ! DecoratedTraversableMonad W T}
      `{Module_inst: ! DecoratedTraversableRightPreModule W T U}.

  Lemma binddt_through_runBatch `{Applicative G} `(f : W * A -> G (T B)) :
    binddt (U := U) f = runBatch f ∘ toBatch7.
  Proof.
    unfold_ops @ToBatch7_Binddt.
    rewrite (kdtm_morph _ _ (ϕ := @runBatch _ _ G _ _ _ f)).
    rewrite (runBatch_batch G).
    reflexivity.
  Qed.

  Lemma bindt_through_runBatch `{Applicative G} `(f : A -> G (T B)) :
    bindt (U := U) f = runBatch (f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite bindt_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Lemma bindd_through_runBatch `(f : W * A -> T B) :
    bindd (U := U) f = runBatch (F := fun A => A) f ∘ toBatch7.
  Proof.
    rewrite bindd_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Lemma traverse_through_runBatch `{Applicative G} `(f : A -> G B) :
    traverse (T := U) f = runBatch (map ret ∘ f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite traverse_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapdt_through_runBatch `{Applicative G} `(f : W * A -> G B) :
    mapdt (T := U) f = runBatch (F := G) (map ret ∘ f) ∘ toBatch7.
  Proof.
    rewrite mapdt_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary mapd_through_runBatch `(f : W * A -> B) :
    mapd (T := U) f = runBatch (F := fun A => A) (ret (T := T) ∘ f) ∘ toBatch7.
  Proof.
    rewrite mapd_to_binddt.
    rewrite binddt_through_runBatch.
    reflexivity.
  Qed.

  Corollary map_through_runBatch `(f : A -> B) :
    map (F := U) f = runBatch (F := fun A => A) (ret (T := T) ∘ f ∘ extract) ∘ toBatch7.
  Proof.
    rewrite map_to_traverse.
    rewrite traverse_through_runBatch.
    reflexivity.
  Qed.

  Corollary id_through_runBatch : forall (A : Type),
      id (A := U A) = runBatch (F := fun A => A) (ret (T := T) ∘ extract) ∘ toBatch7.
  Proof.
    intros.
    rewrite <- (fun_map_id (F := U)).
    rewrite map_through_runBatch.
    reflexivity.
  Qed.

End runBatch.

Require Import
  Tealeaves.Adapters.KleisliToCoalgebraic.TraversableMonad.

(** ** Relating <<toBatch7>> with <<toBatch>> *)
(******************************************************************************)
Lemma toBatch3D_toBatch3
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A B : Type} :
  toBatch3 (A := A) (B := B) = mapfst_Batch extract ∘ toBatch7.
Proof.
  intros.
  unfold_ops @ToBatch3_Bindt.
  unfold_ops @ToBatch7_Binddt.
  rewrite (kdtm_morph (Batch (W * A) (T B)) (Batch A (T B))
             (ϕ := fun C => mapfst_Batch extract)).
  rewrite kdtmf_bindt_compat.
  reflexivity.
Qed.

(** ** Naturality of <<toBatch7>> *)
(******************************************************************************)
Lemma toBatch7_mapfst1
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonad W T}
  {A A' B : Type} (f : W * A -> A') :
  toBatch7 ∘ mapd (T := T) f = mapfst_Batch (cobind f) ∘ toBatch7 (A := A) (B := B).
Proof.
  unfold_ops @ToBatch7_Binddt.
  rewrite (binddt_mapd).
  rewrite (kdtm_morph (T := T) (U := T)
                      (Batch (W * A) _)
                      (Batch (W * A') _)
                      (ϕ := fun A => mapfst_Batch (cobind f)) (batch (T B))).
  rewrite ret_natural.
  reflexivity.
Qed.

Lemma toBatch7_mapfst2
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A A' B : Type} (f : A -> A') {C : Type} :
  toBatch7 ∘ map (F := T) f = mapfst_Batch (map f) ∘ toBatch7 (A := A) (B := B).
Proof.
  rewrite (map_to_cobind W).
  rewrite <- toBatch7_mapfst1.
  rewrite map_to_mapd.
  reflexivity.
Qed.

Lemma toBatch7_mapfst3
  `{Kleisli.DecoratedTraversableMonad.DecoratedTraversableMonadFull W T}
  {A A' B : Type} (f : W * A -> A') :
  toBatch3 ∘ mapd (T := T) f = mapfst_Batch f ∘ toBatch7 (A := A) (B := B).
Proof.
  rewrite toBatch3D_toBatch3.
  unfold_ops @ToBatch7_Binddt.
  reassociate ->.
  rewrite (binddt_mapd).
  rewrite (kdtm_morph (T := T) (U := T)
                      (Batch (W * A') _)
                      (Batch A' _)
                      (ϕ := fun A => mapfst_Batch extract) (_)).
  rewrite (kdtm_morph (T := T) (U := T)
                      (Batch (W * A) _)
                      (Batch A' _)
                      (ϕ := fun A => mapfst_Batch f) (batch (T B))).
  rewrite ret_natural.
  unfold kc4.
  reassociate <- on left.
  rewrite ret_natural.
  reassociate -> on left.
  rewrite kcom_cobind0.
  reflexivity.
Qed.
