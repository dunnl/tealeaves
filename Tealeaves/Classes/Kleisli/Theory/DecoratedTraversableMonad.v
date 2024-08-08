From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Classes.Kleisli.Theory.DecoratedTraversableFunctor.

Import Monoid.Notations.
Import Subset.Notations.
Import List.ListNotations.
Import ContainerFunctor.Notations.
Import DecoratedContainerFunctor.Notations.

#[local] Generalizable Variable W M T U G A B C.

(** * Theory of DTMs *)
(******************************************************************************)
Section lemmas.

  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Monoid_inst: ! Monoid W}.

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

  (** ** Composition in the applicative functor *)
  (******************************************************************************)
  Lemma binddt_app_const_r:
    forall {G : Type -> Type}
      `{Monoid M} {A B : Type} `{Applicative G} (f : W * A -> G M),
      @binddt W T U _ (G ∘ const M)
        (Map_compose G (const M))
        (Pure_compose G (const M))
        (Mult_compose G (const M)) A B f =
        binddt (U := U) (G := const (G M)) (B := B) f.
  Proof.
    intros. fequal.
    - ext X Y h x.
      unfold_ops @Map_compose @Map_const.
      now rewrite (fun_map_id (Functor := app_functor)).
    - ext X Y [x y].
      unfold_ops @Mult_compose @Mult_const.
      unfold_ops @Monoid_op_applicative.
      reflexivity.
  Qed.

  (** ** Lemmas for particular applicative functors *)
  (******************************************************************************)

  (** *** <<binddt>> with constant applicative functors *)
  (******************************************************************************)
  Section constant_applicative.

    Context `{Monoid M}.

    Lemma binddt_constant_applicative1 {A B : Type}
      `(f : W * A -> const M (T B)) :
      binddt (T := T) (U := U) f =
        binddt (T := T) (U := U) (B := False) f.
    Proof.
      change_right (map (F := const M) (A := U False) (B := U B)
                      (map (F := U) (A := False) (B := B) exfalso)
                      ∘ binddt (T := T) (U := U) (B := False) f).
      rewrite (map_binddt (G1 := const M)).
      reflexivity.
    Qed.

    Lemma binddt_constant_applicative2 (fake1 fake2 : Type)
      `(f : W * A -> const M (T B)) :
      binddt (T := T) (U := U) (B := fake1) f =
        binddt (T := T) (U := U) (B := fake2) f.
    Proof.
      intros.
      rewrite (binddt_constant_applicative1 (B := fake1)).
      rewrite (binddt_constant_applicative1 (B := fake2)).
      reflexivity.
    Qed.

  End constant_applicative.


  (** ** Properties of <<foldMapd>> *)
  (******************************************************************************)

  (** *** Composition with monad operattions *)
  (******************************************************************************)
  Theorem foldMapd_ret `{Monoid M} : forall `(f : W * A -> M),
      foldMapd (T := T) f ∘ ret = f ∘ ret.
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1. (* todo get rid of this arg *)
    rewrite mapdt_to_binddt.
    rewrite (kdtm_binddt0 (G := const M) (A := A) (B := False)).
    reflexivity.
  Qed.

  Theorem foldMapd_binddt `{Applicative G} `{Monoid M} :
    forall `(g : W * B -> M) `(f : W * A -> G (T B)),
      map (foldMapd g) ∘ binddt f =
        foldMapd (fun '(w, a) => map (foldMapd (g ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    rewrite (kdtm_binddt2 (G2 := const M) (G1 := G)). (* TODO args *)
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    rewrite binddt_app_const_r.
    unfold foldMapd.
    (* TODO Make mapdt_to_binddt work immediately here *)
    fequal. ext [w a].
    unfold compose. cbn.
    rewrite mapdt_to_binddt.
    reflexivity.
  Qed.

  Corollary foldMap_binddt `{Applicative G} `{Monoid M} :
    forall `(g : B -> M) `(f : W * A -> G (T B)),
      map (foldMap g) ∘ binddt f =
        foldMapd (fun '(w, a) => map (foldMap g) (f (w, a))).
  Proof.
    intros.
    rewrite foldMap_to_foldMapd.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_binddt.
    fequal; ext [w a].
    rewrite extract_preincr2.
    reflexivity.
  Qed.

  Corollary foldMapd_binddt_I `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd g ∘ binddt (U := U) (G := fun A => A) f =
        foldMapd (T := U) (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
  Proof.
    intros.
    change (foldMapd g) with (map (F := fun A => A) (foldMapd (T := U) g)).
    rewrite (foldMapd_binddt (G := fun A => A)).
    reflexivity.
  Qed.

  Corollary foldMapd_bindd `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd g ∘ bindd f =
        foldMapd (fun '(w, a) => foldMapd (g ⦿ w) (f (w, a))).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite foldMapd_binddt_I.
    reflexivity.
  Qed.

  Corollary foldMap_bindd `{Monoid M} : forall `(g : B -> M) `(f : W * A -> T B),
      foldMap g ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap g (f (w, a))).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    rewrite foldMap_to_foldMapd.
    rewrite foldMapd_binddt_I.
    fequal; ext [w a].
    rewrite extract_preincr2.
    rewrite foldMap_to_foldMapd.
    reflexivity.
  Qed.

  (** ** <<tolistd>> *)
  (******************************************************************************)

  (** *** Relating <<tolistd>> and <<binddt>> / <<ret>> *)
  (******************************************************************************)
  Lemma toctxlist_ret : forall (A : Type) (a : A),
      toctxlist (ret (T := T) a) = [ (Ƶ, a) ].
  Proof.
    intros.
    rewrite toctxlist_to_foldMapd.
    compose near a on left.
    rewrite foldMapd_ret.
    reflexivity.
  Qed.

  Lemma toctxlist_binddt : forall `{Applicative G} `(f : W * A -> G (T B)),
      map (F := G) toctxlist ∘ binddt (G := G) f =
        foldMapd (T := U)
          (fun '(w, a) => map (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite toctxlist_to_foldMapd.
    rewrite foldMapd_binddt.
    reflexivity.
  Qed.

  Lemma toctxlist_bindd : forall `(f : W * A -> T B),
      toctxlist ∘ bindd f =
        foldMapd (T := U) (fun '(w, a) => (foldMapd (T := T) (ret (T := list) ⦿ w)) (f (w, a))).
  Proof.
    intros.
    rewrite toctxlist_to_foldMapd.
    rewrite foldMapd_bindd.
    reflexivity.
  Qed.

  (** *** Corollaries for the rest *)
  (******************************************************************************)
  Corollary tolist_binddt : forall `{Applicative G} `(f : W * A -> G (T B)),
      map tolist ∘ binddt f = foldMapd (T := U) (map tolist ∘ f).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_binddt.
    (* todo why isn't reflexivity enough... b.c. destructing the pair? *)
    fequal. ext [w a].
    reflexivity.
  Qed.

  Corollary tolist_bindd : forall `(f : W * A -> T B),
      tolist ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap (ret (T := list)) (f (w, a))).
  Proof.
    intros.
    rewrite tolist_to_foldMap.
    rewrite foldMap_bindd.
    reflexivity.
  Qed.

  Corollary tolist_to_binddt : forall (A : Type),
      tolist = binddt (G := const (list A))
                 (B := False) (ret (T := list) ∘ extract).
  Proof.
    intros.
    rewrite tolist_to_traverse1.
    rewrite traverse_to_binddt.
    reflexivity.
  Qed.

  (** ** Relating <<toctxset>>  *)
  (******************************************************************************)
  Corollary toctxset_ret : forall (A : Type) (a : A),
      toctxset (ret (T := T) a) = {{ (Ƶ, a) }}.
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    compose near a on left.
    rewrite foldMapd_ret.
    reflexivity.
  Qed.

  Lemma toctxset_bindd:
    forall `(f : W * A -> T B),
      toctxset ∘ bindd (T := T) (U := U) f =
        bindd (U := ctxset W) (toctxset (F := T) ∘ f) ∘ toctxset (F := U).
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_bindd.
    rewrite toctxset_to_foldMapd.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_morphism.
    fequal.
    ext [w a].
    change_right
      (bindd (T := ctxset W) (foldMapd (ret (T := subset)) ∘ f) {{(w, a)}}).
    rewrite bindd_ctxset_one.
    unfold compose.
    rewrite (DecoratedFunctor.shift_spec subset
               (W := W) (op := op) (A := B)).
    compose near (f (w, a)) on right.
    rewrite foldMapd_morphism.
    rewrite (natural (ϕ := @ret subset _)).
    reflexivity.
  Qed.

  Lemma tosubset_bindd : forall `(f : W * A -> T B),
      tosubset ∘ bindd f =
        foldMapd (fun '(w, a) => foldMap (ret (T := subset)) (f (w, a))).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_bindd.
    reflexivity.
  Qed.

  (** ** Set operations to binddt *)
  (******************************************************************************)
  Corollary toctxset_to_binddt : forall (A: Type),
      toctxset (F := U) = binddt (G := const (subset (W * A)))
                     (B := False) (ret (T := subset)).
  Proof.
    intros.
    rewrite toctxset_to_foldMapd.
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    reflexivity.
  Qed.

  Corollary tosubset_to_binddt : forall (A: Type),
      tosubset = binddt (G := const (subset A))
                     (B := False) (ret (T := subset) ∘ extract).
  Proof.
    intros.
    rewrite tosubset_to_foldMap.
    rewrite foldMap_to_traverse1.
    rewrite traverse_to_binddt.
    reflexivity.
  Qed.

  (** ** Characterizing <<∈d>> *)
  (******************************************************************************)
  Lemma element_ctx_of_ret: forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret (T := T) a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros.
    unfold element_ctx_of.
    rewrite toctxset_ret.
    unfold subset_one.
    rewrite pair_equal_spec.
    easy.
  Qed.

  Corollary element_of_to_binddt: forall (A: Type) (t: U A) (a: A),
      a ∈ t = binddt (G := const Prop)
                (H0 := @Pure_const Prop Monoid_unit_false)
                (H1 := @Mult_const Prop Monoid_op_or)
                (B := False) (eq a ∘ extract) t.
  Proof.
    intros.
    rewrite element_of_to_foldMap.
    rewrite foldMap_to_traverse1.
    rewrite traverse_to_binddt.
    reflexivity.
  Qed.

  Corollary element_ctx_of_to_binddt: forall (A: Type) (t: U A) (w: W) (a: A),
      (w, a) ∈d t = binddt (G := const Prop)
                      (H0 := @Pure_const Prop Monoid_unit_false)
                      (H1 := @Mult_const Prop Monoid_op_or)
                      (B := False) (eq (w, a)) t.
  Proof.
    intros.
    rewrite element_ctx_of_to_foldMapd.
    rewrite foldMapd_to_mapdt1.
    rewrite mapdt_to_binddt.
    reflexivity.
  Qed.

End lemmas.

Section instances.

  Context
    `{op : Monoid_op W}
      `{unit : Monoid_unit W}
      `{Monoid_inst: ! Monoid W}.

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

  #[export] Instance:
    DecoratedMonadHom W T (ctxset W) (@toctxset W T _).
  Proof.
    constructor.
    - intros.
      rewrite toctxset_bindd.
      reflexivity.
    - intros.
      ext a [w a']. unfold compose.
      rewrite toctxset_ret.
      cbv.
      apply propositional_extensionality.
      rewrite pair_equal_spec.
      easy.
  Qed.

  #[export] Instance DTM_ctxset_DecoratedMonadHom:
    DecoratedMonadHom W T (ctxset W) (@toctxset W T _).
  Proof.
    constructor.
    - intros.
      rewrite toctxset_bindd.
      reflexivity.
    - intros.
      ext a [w a']. unfold compose.
      rewrite toctxset_ret.
      cbv.
      apply propositional_extensionality.
      rewrite pair_equal_spec.
      easy.
  Qed.

  #[export] Instance DTM_ctxset_DecoratedModuleHom:
    ParallelDecoratedRightModuleHom
      T (ctxset W) U (ctxset W)
      (@toctxset W T _) (@toctxset W U _).
  Proof.
    constructor.
    intros.
    rewrite toctxset_bindd.
    reflexivity.
  Qed.

End instances.
