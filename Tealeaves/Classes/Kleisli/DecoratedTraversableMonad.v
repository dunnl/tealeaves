From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.DecoratedTraversableFunctor
  Functors.Constant.

Import Monoid.Notations.
Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedMonad.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import DecoratedTraversableFunctor.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

(** * Decorated traversable monads *)
(******************************************************************************)

(** ** Operation <<binddt>> *)
(******************************************************************************)
Class Binddt
  (W : Type)
  (U : Type -> Type)
  (T : Type -> Type)
  := binddt :
    forall (G : Type -> Type)
      `{Map G} `{Pure G} `{Mult G}
      (A B : Type),
      (W * A -> G (U B)) -> T A -> G (T B).

#[global] Arguments binddt {W}%type_scope {U} {T}%function_scope {Binddt}
  {G}%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc7
  {W : Type}
  {T : Type -> Type}
  `{Return T}
  `{Binddt W T T}
  `{op: Monoid_op W} `{unit: Monoid_unit W}
  {A B C : Type}
  (G1 G2 : Type -> Type)
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2} :
  (W * B -> G2 (T C)) ->
  (W * A -> G1 (T B)) ->
  (W * A -> G1 (G2 (T C))) :=
  fun g f '(w, a) =>
    map (F := G1) (A := T B) (B := G2 (T C))
      (binddt (g ⦿ w)) (f (w, a)).

#[local] Infix "⋆7" := (kc7 _ _) (at level 60) : tealeaves_scope.

(** ** DTM typeclass *)
(******************************************************************************)
Class DecoratedTraversableMonad
  (W : Type)
  (T : Type -> Type)
  `{Return T}
  `{Binddt W T T}
  `{op: Monoid_op W} `{unit: Monoid_unit W} :=
  { kdtm_monoid :> Monoid W;
    kdtm_binddt0 : forall {G : Type -> Type} `{Applicative G} (A B : Type) (f : W * A -> G (T B)),
      binddt f ∘ ret = f ∘ ret (T := (W ×));
    kdtm_binddt1 : forall (A : Type),
      binddt (G := fun A => A) (ret (T := T) ∘ extract (W := (W ×))) = @id (T A);
    kdtm_binddt2 :
    forall {G1 G2 : Type -> Type} `{Applicative G1} `{Applicative G2}
      (A B C : Type)
      (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
      map (F := G1) (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f);
    kdtm_morph :
    forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ}
      `(f : W * A -> G1 (T B)),
      ϕ (T B) ∘ binddt f = binddt (ϕ (T B) ∘ f);
}.

Class DecoratedTraversableMonadFull
  (W : Type)
  (T : Type -> Type)
  `{Return T}
  `{Binddt W T T}
  `{op: Monoid_op W} `{unit: Monoid_unit W}
  `{Bindt T T} `{Bindd W T T} `{Bind T T}
  `{Mapdt W T} `{Mapd W T} `{Traverse T} `{Map T} :=
  { kdtmf_ktm :> DecoratedTraversableMonad W T;
    kdtmf_map_compat : forall (A B : Type) (f : A -> B),
      map f = binddt (T := T) (G := fun A => A) (ret (T := T) ∘ f ∘ extract (W := (W ×)));
    kdtmf_mapd_compat : forall (A B : Type) (f : W * A -> B),
      mapd f = binddt (T := T) (G := fun A => A) (ret (T := T) ∘ f);
    kdtmf_bind_compat : forall (A B : Type) (f : A -> T B),
      bind f = binddt (T := T) (G := fun A => A) (f ∘ extract (W := (W ×)));
    kdtmf_traverse_compat :
    forall {G : Type -> Type} `{Mult G} `{Map G} `{Pure G}
      (A B : Type) (f : A -> G B),
      traverse f = binddt (map (F := G) ret ∘ f ∘ extract (W := (W ×)));
    kdtmf_mapdt_compat :
    forall {G : Type -> Type} `{Mult G} `{Map G} `{Pure G}
      (A B : Type) (f : W * A -> G B),
      mapdt f = binddt (T := T) (map (F := G) (ret (T := T)) ∘ f);
    kdtmf_bindd_compat : forall (A B : Type),
      @bindd W T T _ A B = @binddt W T T _ (fun A => A) _ _ _ A B;
    kdtmf_bindt_compat :
    forall {G : Type -> Type} `{Mult G} `{Map G} `{Pure G}
      (A B : Type) (f : A -> G (T B)),
      bindt f = binddt (T := T) (f ∘ extract (W := (W ×)));
  }.

(* version that works when f is a bound variable *)
Lemma kdtmf_mapdt_compat' `{DecoratedTraversableMonadFull W T} :
    forall {G : Type -> Type} `{Mult G} `{Map G} `{Pure G}
      (A B : Type),
      @mapdt W T _ G _ _ _ A B =
        fun f => (@binddt W T T _ G _ _ _ A B)
                (map (F := G) (ret (T := T)) ∘ f).
Proof.
  intros; ext f; now rewrite kdtmf_mapdt_compat.
Qed.

Ltac kdtmf_normalize :=
  repeat
    ( rewrite kdtmf_map_compat ||
        rewrite kdtmf_bind_compat ||
          rewrite kdtmf_traverse_compat ||
            rewrite kdtmf_mapd_compat ||
              rewrite kdtmf_mapdt_compat ||
                rewrite kdtmf_bindd_compat ||
                  rewrite kdtmf_bindt_compat).

(** * Tactical support (TODO move me) *)
(******************************************************************************)
Ltac unfold_map_id :=
  repeat (change (map (fun A => A) _ _ ?f) with f).

#[local] Hint Unfold kc7 kc6 kc5 kc4 kc3 kc2 kc1 : tealeaves_kc_unfold.

#[local] Ltac setup :=
  intros; autounfold with tealeaves_kc_unfold; ext [w a];
  unfold_map_id.

(** * Laws for Kleisli composition *)
(******************************************************************************)
Section kc7.

  Context
    `{Return T}
    `{Binddt W T T}
    `{op: Monoid_op W} `{unit: Monoid_unit W} `{! Monoid W}.

  (** ** Interaction with [incr], [preincr] *)
  (******************************************************************************)
  Section incr.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Lemma kc7_incr :
      forall `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)) (w : W),
        (g ∘ incr w) ⋆7 (f ∘ incr w) = (g ⋆7 f) ∘ incr w.
    Proof.
      intros. unfold kc7. ext [w' a].
      unfold preincr. reassociate ->.
      rewrite incr_incr.
      reflexivity.
    Qed.

    Lemma kc7_preincr :
      forall `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)) (w : W),
        (g ⦿ w) ⋆7 (f ⦿ w) = (g ⋆7 f) ⦿ w.
    Proof.
      intros. unfold preincr. rewrite kc7_incr.
      reflexivity.
    Qed.

  End incr.

  Context
    `{! DecoratedTraversableMonad W T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}
    {A B C D : Type}.

  (** ** Kleisi category laws *)
  (******************************************************************************)

  (** *** Left identity *)
  (******************************************************************************)
  Lemma kc7_id1 : forall (f : W * A -> G (T B)),
      kc7 G (fun A => A) (ret (T := T) ∘ extract (W := (W ×))) f = f.
  Proof.
    setup.
    rewrite preincr_assoc.
    rewrite extract_preincr.
    rewrite kdtm_binddt1.
    rewrite fun_map_id.
    reflexivity.
  Qed.

  (** *** Right identity *)
  (******************************************************************************)
  Lemma kc7_id2 : forall (g : W * A -> G (T B)),
      kc7 (fun A => A) G g (ret (T := T) ∘ extract (W := (W ×))) = g.
  Proof.
    setup.
    change_left ((binddt (T := T) (g ⦿ w) ∘ ret (T := T)) a).
    rewrite kdtm_binddt0.
    change (g (w ● Ƶ, a) = g (w, a)).
    simpl_monoid.
    reflexivity.
  Qed.

  (** *** Associativity *)
  (******************************************************************************)
  Lemma kc7_assoc :
    forall (h : W * C -> G3 (T D)) (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
      kc7 (G1 ∘ G2) G3 h (g ⋆7 f) = kc7 G1 (G2 ∘ G3) (h ⋆7 g) f.
  Proof.
    setup.
    unfold_ops @Map_compose.
    compose near (f (w, a)) on left.
    rewrite fun_map_map.
    rewrite kdtm_binddt2.
    rewrite kc7_preincr.
    reflexivity.
  Qed.

End kc7.

(** * Interaction of <<binddt>> with composition in the applicative functor *)
(******************************************************************************)
Section properties.

  Context
    `{DecoratedTraversableMonad W T}.

  Lemma binddt_app_l :
    forall {G : Type -> Type} {A B : Type}
      `{Applicative G} (f : W * A -> G (T B)),
      @binddt W T T _ ((fun A => A) ∘ G)
        (Map_compose (fun A => A) G)
        (Pure_compose (fun A => A) G)
        (Mult_compose (fun A => A) G) A B f =
        binddt (T := T) f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma binddt_app_r :
    forall {G : Type -> Type} {A B : Type}
      `{Applicative G} (f : W * A -> G (T B)),
      @binddt W T T _ (G ∘ (fun A => A))
        (Map_compose G (fun A => A))
        (Pure_compose G (fun A => A))
        (Mult_compose G (fun A => A)) A B f =
        binddt f.
  Proof.
    intros. fequal. now rewrite (Mult_compose_identity1 G).
  Qed.

  Lemma binddt_app_const_r :
    forall {G : Type -> Type} `{Monoid M} {A B : Type} `{Applicative G} (f : W * A -> G M),
      @binddt W T T _ (G ∘ const M)
        (Map_compose G (const M))
        (Pure_compose G (const M))
        (Mult_compose G (const M)) A B f =
        binddt (T := T) (G := const (G M)) (B := B) f.
  Proof.
    intros. fequal.
    - ext X Y h x.
      unfold_ops @Map_compose @Map_const.
      now rewrite fun_map_id.
    - ext X Y [x y].
      unfold_ops @Mult_compose @Mult_const.
      unfold_ops @Monoid_op_applicative.
      reflexivity.
  Qed.

End properties.

(** ** Derived operations *)
(******************************************************************************)
Section derived_operations.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Binddt W T T}
    `{Return T}.

  #[export] Instance Map_Binddt : Map T :=
    fun (A B : Type) (f : A -> B) => binddt (G := fun A => A) (ret (T := T) ∘ f ∘ extract (W := (W ×))).
  #[export] Instance Mapdt_Binddt: Mapdt W T
    := fun G _ _ _ A B f => binddt (map (F := G) (ret (T := T)) ∘ f).
  #[export] Instance Bindd_Binddt: Bindd W T T
    := fun A B f => binddt (G := fun A => A) f.
  #[export] Instance Bindt_Binddt: Bindt T T
    := fun G _ _ _ A B f => binddt (f ∘ extract (W := (W ×))).
  #[export] Instance Bind_Binddt: Bind T T
    := fun A B f => binddt (T := T) (G := fun A => A) (f ∘ extract (W := (W ×))).
  #[export] Instance Mapd_Binddt: Mapd W T
    := fun A B f => binddt (G := fun A => A) (ret (T := T) ∘ f).
  #[export] Instance Traverse_Binddt: Traverse T
    := fun G _ _ _ A B f => binddt (T := T) (map (F := G) (ret (T := T)) ∘ f ∘ extract (W := (W ×))).

  Section special_cases.

    Context
      `{Applicative G}.

    (** *** Rewriting rules for special cases of <<binddt>> *)
    (******************************************************************************)
    Lemma bindt_to_binddt `(f : A -> G (T B)):
      bindt f = binddt (f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma bindd_to_binddt `(f : W * A -> T B):
      bindd f = binddt (T := T) (G := fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mapdt_to_binddt `(f : W * A -> G B):
      mapdt f = binddt (T := T) (map (F := G) ret ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma bind_to_binddt `(f : A -> T B):
      bind f = binddt (T := T) (G := fun A => A) (f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma mapd_to_binddt `(f : W * A -> B):
      mapd f = binddt (T := T) (G := fun A => A) (ret (T := T) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_binddt `(f : A -> G B):
      traverse f = binddt (T := T) (map (F := G) ret ∘ f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_binddt `(f : A -> B):
      map f = binddt (T := T) (G := fun A => A) (ret (T := T) ∘ f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bindt>> *)
    (******************************************************************************)
    Lemma bind_to_bindt `(f : A -> T B):
      bind (T := T) f = bindt (T := T) f.
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_bindt `(f : A -> G B):
      traverse (T := T) (G := G) f = bindt (map (F := G) ret ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindt `(f : A -> B):
      map (F := T) f = bindt (T := T) (ret (T := T) ∘ f).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bindd>> *)
    (******************************************************************************)
    Lemma bind_to_bindd `(f : A -> T B):
      bind (T := T) f = bindd (T := T) (f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma mapd_to_bindd `(f : W * A -> B):
      mapd f = bindd (ret (T := T) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindd `(f : A -> B):
      map (F := T) f = bindd (T := T) (ret (T := T) ∘ f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mapdt>> *)
    (******************************************************************************)
    Lemma mapd_to_mapdt `(f : W * A -> B):
      mapd (T := T) f = mapdt (T := T) (G := fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_mapdt `(f : A -> B):
      map (F := T) f = mapdt (T := T) (G := fun A => A) (f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_mapdt `(f : A -> G B):
      traverse (T := T) (G := G) f = mapdt (T := T) (f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<traverse>> *)
    (******************************************************************************)
    Lemma map_to_traverse `(f : A -> B):
      map f = traverse (T := T) (G := fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mapd>> *)
    (******************************************************************************)
    Lemma map_to_mapd `(f : A -> B):
      map (F := T) f = mapd (f ∘ extract (W := (W ×))).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bind>> *)
    (******************************************************************************)
    Lemma map_to_bind `(f : A -> B):
      map (F := T) f = bind (ret ∘ f).
    Proof.
      reflexivity.
    Qed.

  End special_cases.

End derived_operations.

(** * Derived Instances *)
(******************************************************************************)
Section derived_instances.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DecoratedTraversableMonadFull W T}.

  (** ** Identity laws *)
  (******************************************************************************)
  Lemma bindd_id : forall A : Type,
      bindd (T := T) (ret ∘ extract (W := (W ×))) = @id (T A).
  Proof.
    intros.
    rewrite kdtmf_bindd_compat.
    apply kdtm_binddt1.
  Qed.

  Lemma bindt_id : forall A : Type,
      bindt (G := fun A => A) (ret (T := T)) = @id (T A).
  Proof.
    intros.
    rewrite (kdtmf_bindt_compat (G := fun A => A)).
    apply kdtm_binddt1.
  Qed.

  Lemma mapdt_id : forall A : Type,
      mapdt (G := fun A => A) (extract (W := (W ×))) = @id (T A).
  Proof.
    intros.
    rewrite (kdtmf_mapdt_compat (G := fun A => A)).
    apply kdtm_binddt1.
  Qed.

  Lemma mapd_id : forall A : Type,
      mapd (extract (W := (W ×))) = @id (T A).
  Proof.
    intros.
    rewrite kdtmf_mapd_compat.
    apply kdtm_binddt1.
  Qed.

  Lemma traverse_id : forall A : Type,
      traverse (T := T) (G := fun A => A) (@id A) = id.
  Proof.
    intros.
    rewrite kdtmf_traverse_compat.
    apply kdtm_binddt1.
  Qed.

  Lemma bind_id : forall A : Type,
      bind (ret (T := T)) = @id (T A).
  Proof.
    intros.
    rewrite kdtmf_bind_compat.
    apply kdtm_binddt1.
  Qed.

  Lemma map_id : forall A : Type,
      map (F := T) (@id A) = @id (T A).
  Proof.
    intros.
    rewrite kdtmf_map_compat.
    apply kdtm_binddt1.
  Qed.

  (** ** Composition with <<ret>> *)
  (******************************************************************************)
  Lemma bindd_ret :
     forall (A B : Type) (f : W * A -> T B),
      bindd (T := T) f ∘ ret (T := T) = f ∘ ret (T := (W ×)).
  Proof.
    intros.
    rewrite kdtmf_bindd_compat.
    rewrite (kdtm_binddt0 (G := fun A => A)).
    reflexivity.
  Qed.

  Lemma bindt_ret :
    forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt f ∘ ret (T := T) = f.
  Proof.
    intros.
    rewrite kdtmf_bindt_compat.
    rewrite kdtm_binddt0.
    reflexivity.
  Qed.

  Lemma bind_ret :
    forall (A B : Type) (f : A -> T B),
      bind f ∘ ret (T := T) = f.
  Proof.
    intros.
    rewrite kdtmf_bind_compat.
    rewrite (kdtm_binddt0 (G := fun A => A)).
    reflexivity.
  Qed.

  (** ** Interaction with applicative morphisms *)
  (******************************************************************************)
  Section applicative_morphisms.

    Context
      `{Hmorph : ApplicativeMorphism G1 G2 ϕ}.

    Lemma bindt_morph:
      forall (A B : Type) (f : A -> G1 (T B)),
        ϕ (T B) ∘ bindt f = bindt (ϕ (T B) ∘ f).
    Proof.
      intros.
      rewrite kdtmf_bindt_compat.
      rewrite (kdtm_morph G1 G2).
      reassociate <- on left.
      rewrite <- kdtmf_bindt_compat.
      reflexivity.
    Qed.

    Lemma mapdt_morph:
      forall (A B : Type) (f : W * A -> G1 B),
        mapdt (ϕ B ∘ f) = ϕ (T B) ∘ mapdt f.
    Proof.
      intros.
      rewrite kdtmf_mapdt_compat.
      reassociate <- on left.
      rewrite (natural (ϕ := ϕ)).
      reassociate -> on left.
      rewrite <- (kdtm_morph G1 G2).
      (*
      rewrite <- (kdtmf_mapdt_compat A B f).
      reflexivity.
    Qed.
       *)
      Admitted.

    Lemma traverse_morph:
      forall (A B : Type) (f : A -> G1 B),
        ϕ (T B) ∘ traverse (T := T) (G := G1) f = traverse (T := T) (G := G2) (ϕ B ∘ f).
    Proof.
      intros.
      rewrite kdtmf_traverse_compat.
      rewrite (kdtm_morph G1 G2).
      do 2 reassociate <- on left.
      rewrite <- (natural (ϕ := ϕ)).
      reassociate -> near f.
      rewrite <- kdtmf_traverse_compat.
      reflexivity.
    Qed.

  End applicative_morphisms.

  (** ** Homogeneous composition laws *)
  (******************************************************************************)
  Section composition.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Variables (A B C : Type).

    (** *** Lemmas <<kc7_xx>> *)
    (******************************************************************************)
    Lemma kc7_66 :
      forall (g : W * B -> G2 C) (f : W * A -> G1 B),
        (map (F := G2) (ret (T := T)) ∘ g) ⋆7
          (map (F := G1) (ret (T := T)) ∘ f) =
          map (F := G1 ∘ G2) (ret (T := T)) ∘ (g ⋆6 f).
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      (* LHS *)
      unfold compose at 2.
      compose near (f (w, a)).
      rewrite (fun_map_map (F := G1)).
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      (* RHS *)
      unfold kc6.
      unfold_ops @Map_compose.
      do 2 reassociate <- on right.
      unfold_compose_in_compose; rewrite (fun_map_map (F := G1)).
      unfold_ops @Cobind_reader; unfold strength.
      unfold compose at 3 4.
      compose near (f (w, a)) on right.
      rewrite (fun_map_map (F := G1)).
      reflexivity.
    Qed.

    Lemma kc7_55 : forall
        `(g : W * B -> T C) `(f : W * A -> T B),
        kc7 (fun A => A) (fun A => A) g f = g ⋆5 f.
    Proof.
      intros.
      unfold kc5.
      ext [w a].
      rewrite kdtmf_bindd_compat.
      reflexivity.
    Qed.

    Lemma kc7_44 : forall
        `(g : W * B -> C) `(f : W * A -> B),
        kc7 (fun A => A) (fun A => A)
          (ret (T := T) ∘ g) (ret (T := T) ∘ f) =
          ret (T := T) ∘ (g ⋆4 f).
    Proof.
      intros.
      rewrite kc7_55.
      unfold kc5.
      ext [w a].
      unfold compose at 2.
      compose near (f (w, a)) on left.
      rewrite bindd_ret.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_33 :
      forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        kc7 G1 G2
          (g ∘ extract (W := (W ×)))
          (f ∘ extract (W := (W ×))) =
          (g ⋆3 f) ∘ extract (W := (W ×)).
    Proof.
      setup.
      rewrite kdtmf_bindt_compat.
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    Lemma kc7_22 :
      forall (g : B -> G2 C) (f : A -> G1 B),
        kc7 G1 G2
          (map (F := G2) (ret (T := T)) ∘ g ∘ extract (W := (W ×)))
          (map (F := G1) (ret (T := T)) ∘ f ∘ extract (W := (W ×))) =
          map (F := G1 ∘ G2) (ret (T := T)) ∘
            (map (F := G1) g ∘ f) ∘ extract (W := (W ×)).
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      rewrite preincr_assoc.
      do 2 reassociate ->.
      rewrite extract_preincr.
      unfold compose at 1 2 3 4; cbn.
      compose near (f a) on left.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      unfold_ops @Map_compose.
      unfold compose; cbn.
      compose near (f a) on right.
      rewrite fun_map_map.
      reflexivity.
    Qed.

    Lemma kc7_11 :
      forall (g : B -> T C) (f : A -> T B),
        kc7 (fun A => A) (fun A => A)
          (g ∘ extract (W := (W ×)))
          (f ∘ extract (W := (W ×))) =
          (g ⋆1 f) ∘ extract (W := (W ×)).
    Proof.
      setup.
      rewrite (kdtmf_bind_compat (T := T)).
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    Lemma kc7_00 :
      forall (g : B -> C) (f : A -> B),
        kc7 (fun A => A) (fun A => A)
          (ret (T := T) ∘ g ∘ extract (W := (W ×)))
          (ret (T := T) ∘ f ∘ extract (W := (W ×))) =
          (ret (T := T) ∘ g ∘ f ∘ extract (W := (W ×))).
    Proof.
      setup; unfold compose; cbn.
      compose near (f a) on left.
      unfold_ops @Map_I.
      rewrite (kdtm_binddt0 (T := T) (G := fun A => A)).
      rewrite preincr_ret.
      reflexivity.
    Qed.

  End composition.

  (** ** Homogeneous composition laws *)
  (******************************************************************************)
  Section composition.

    Context
      `{Applicative G1}
      `{Applicative G2}.

    Variables (A B C : Type).

    (* composition_66 *)
    Lemma mapdt_mapdt: forall
        (g : W * B -> G2 C)
        (f : W * A -> G1 B),
        map (F := G1) (A := T B) (B := G2 (T C))
          (mapdt g) ∘ mapdt f =
          mapdt (G := G1 ∘ G2) (g ⋆6 f).
    Proof.
      intros.
      do 2 rewrite kdtmf_mapdt_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_66.
      rewrite <- kdtmf_mapdt_compat.
      reflexivity.
    Qed.

    (* composition_55 *)
    Lemma bindd_bindd : forall
        (g : W * B -> T C)
        (f : W * A -> T B),
        bindd g ∘ bindd f = bindd (g ⋆5 f).
    Proof.
      intros.
      do 2 rewrite kdtmf_bindd_compat.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (T := T) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_55.
      rewrite <- kdtmf_bindd_compat.
      reflexivity.
    Qed.

    (* composition_44 *)
    Lemma mapd_mapd : forall (g : W * B -> C) (f : W * A -> B),
        mapd g ∘ mapd f = mapd (g ∘ cobind (W := (W ×)) f).
    Proof.
      intros.
      do 2 rewrite kdtmf_mapd_compat.
      change (binddt (ret (T := T) ∘ g)) with
        (map (F := fun A => A) (binddt (ret (T := T) ∘ g))).
      rewrite (kdtm_binddt2 (T := T) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_44.
      rewrite <- kdtmf_mapd_compat.
      reflexivity.
    Qed.

    (* composition_33 *)
    Lemma bindt_bindt : forall
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        map (F := G1) (bindt g) ∘ bindt f =
          bindt (G := G1 ∘ G2) (g ⋆3 f).
    Proof.
      intros.
      do 2 rewrite kdtmf_bindt_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_33.
      rewrite <- (kdtmf_bindt_compat (T := T) (G := G1 ∘ G2)).
      reflexivity.
    Qed.

    (* composition_22 *)
    Lemma traverse_traverse : forall (g : B -> G2 C) (f : A -> G1 B),
        map (F := G1) (traverse (G := G2) g) ∘ traverse (G := G1) f =
          traverse (G := G1 ∘ G2) (map g ∘ f).
    Proof.
      intros.
      do 2 rewrite kdtmf_traverse_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_22.
      rewrite <- kdtmf_traverse_compat.
      reflexivity.
    Qed.

    (* composition_11 *)
    Lemma bind_bind : forall (g : B -> T C) (f : A -> T B),
        bind g ∘ bind f = bind (g ⋆1 f).
    Proof.
      intros.
      do 2 rewrite kdtmf_bind_compat.
      change (binddt (g ∘ extract)) with
        (map (F := fun A => A) (binddt (g ∘ extract))).
      rewrite (kdtm_binddt2 (T := T) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_11.
      rewrite <- kdtmf_bind_compat.
      reflexivity.
    Qed.

    (* composition_00 *)
    Lemma map_map : forall (f : A -> B) (g : B -> C),
        map g ∘ map f = map (F := T) (g ∘ f).
    Proof.
      intros.
      do 2 rewrite kdtmf_map_compat.
      change (binddt (?ret ∘ g ∘ ?extract)) with
        (map (F := fun A => A) (binddt (ret ∘ g ∘ extract))).
      rewrite (kdtm_binddt2 (T := T) (G1 := fun A => A) (G2 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_00.
      change (?ret ∘ g ∘ f ∘ ?extract) with
        (ret ∘ (g ∘ f) ∘ extract).
      rewrite <- kdtmf_map_compat.
      reflexivity.
    Qed.

  End composition.

  (** ** Derived typeclass instances *)
  (******************************************************************************)
  Ltac solve_full :=
    try (typeclasses eauto ||
           intros; now kdtmf_normalize).

  #[export] Instance KDM_KDTM: DecoratedMonad W T :=
    {| kmond_bindd0 := bindd_ret;
      kmond_bindd1 := bindd_id;
      kmond_bindd2 := @bindd_bindd;
    |}.

  #[export] Instance KDMF_KDTMF: DecoratedMonadFull W T.
  Proof with solve_full.
    constructor...
  Qed.

  #[export] Instance KTM_KDTM: TraversableMonad T :=
    {| ktm_bindt0 := bindt_ret;
      ktm_bindt1 := bindt_id;
      ktm_bindt2 := @bindt_bindt;
      ktm_morph := @bindt_morph;
    |}.

  #[export] Instance KTMF_KDTMF: TraversableMonadFull T.
  Proof with solve_full.
    constructor...
    intros; ext f...
  Qed.

  #[export] Instance KDT_KDTM: DecoratedTraversableFunctor W T :=
    {| kdtfun_mapdt1 := mapdt_id;
      kdtfun_mapdt2 := @mapdt_mapdt;
      kdtfun_morph := @mapdt_morph;
    |}.

  #[export] Instance KDTF_KDTMF: DecoratedTraversableFunctorFull W T.
  Proof with solve_full.
    constructor...
  Qed.

  #[export] Instance KD_KDTM: DecoratedFunctor W T :=
    {| dfun_mapd1 := mapd_id;
      dfun_mapd2 := @mapd_mapd;
    |}.

  #[export] Instance KDF_KDTMF: DecoratedFunctorFull W T.
  Proof with solve_full.
    constructor...
  Qed.

  #[export] Instance KT_KDTM: TraversableFunctor T :=
    {| trf_traverse_id := traverse_id;
      trf_traverse_traverse := @traverse_traverse;
      trf_traverse_morphism := @traverse_morph;
    |}.

  #[export] Instance KFF_KDTMF: TraversableFunctorFull T.
  Proof with solve_full.
    constructor...
    ext A B f...
  Qed.

  #[export] Instance KM_KDTM : Monad T :=
    {| kmon_bind0 := bind_ret;
      kmon_bind1 := bind_id;
      kmon_bind2 := @bind_bind;
    |}.

  #[export] Instance KMF_KDTMF : MonadFull T.
  Proof with solve_full.
    constructor...
  Qed.

  #[export] Instance: Classes.Functor.Functor T :=
    {| fun_map_id := map_id;
      fun_map_map := @map_map;
    |}.

End derived_instances.

(** * Other composition laws *)
(******************************************************************************)
Section other_composition_laws.

  Context
    `{DecoratedTraversableMonadFull W T}.

  (** ** Rewriting rules for special cases of <<kc7>> *)
  (******************************************************************************)
  Section kc7_special_cases.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C D : Type}.

    Ltac kdtmf_normalize_T T :=
      repeat
        ( rewrite (kdtmf_map_compat (T := T)) ||
            rewrite (kdtmf_bind_compat (T := T)) ||
              rewrite (kdtmf_traverse_compat (T := T)) ||
                rewrite (kdtmf_mapd_compat (T := T)) ||
                  rewrite (kdtmf_mapdt_compat (T := T)) ||
                    rewrite (kdtmf_bindd_compat (T := T)) ||
                      rewrite (kdtmf_bindt_compat (T := T))).

    Ltac solve_kc7 :=
      setup;
      kdtmf_normalize_T T;
      try (reflexivity ||
             rewrite preincr_assoc;
           rewrite extract_preincr;
           reflexivity).

    (** *** Lemmas <<kc7_x7>> *)
    (******************************************************************************)
    Lemma kc7_07 :
      forall (g : B -> C) (f : W * A -> G1 (T B)),
        ret (T := T) ∘ g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1) (map (F := T) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_17 :
      forall (g : B -> T C) (f : W * A -> G1 (T B)),
        g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1)(bind (T := T) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_27 :
      forall (g : B -> G2 C) (f : W * A -> G1 (T B)),
        map (F := G2) (ret (T := T)) ∘ g ∘ extract (W := (W ×)) ⋆7 f =
          map (F := G1) (traverse (T := T) (G := G2) g) ∘ f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_37 :
      forall (g : B -> G2 (T C)) (f : W * A -> G1 (T B)),
        (g ∘ extract (W := (W ×))) ⋆7 f = g ⋆3 f.
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_47 :
      forall (g : W * B -> C) (f : W * A -> G1 (T B)),
        kc7 G1 (fun A => A) (ret (T := T) ∘ g) f =
          (fun '(w, a) => map (F := G1) (mapd (g ⦿ w)) (f (w, a))).
    Proof.
      solve_kc7.
    Qed.


    Lemma kc7_57 :
      forall (g : W * B -> T C) (f : W * A -> G1 (T B)),
        kc7 G1 (fun A => A) g f = g ⋆7 f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc7_67 :
      forall (g : W * B -> G2 C) (f : W * A -> G1 (T B)),
        (map (F := G2) (ret (T := T)) ∘ g) ⋆7 f =
          (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f (w, a))).
    Proof.
      solve_kc7.
    Qed.

    (** *** Lemmas <<kc7_7x>> *)
    (******************************************************************************)
    Lemma kc7_76 :
      forall (g : W * B -> G2 (T C)) (f : W * A -> G1 B),
        g ⋆7 (map (F := G1) ret ∘ f) = g ⋆6 f.
    Proof.
      intros. unfold kc7, kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)).
      rewrite fun_map_map.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_75 :
      forall (g : W * B -> G2 (T C)) (f : W * A -> T B),
        kc7 (fun A => A) G2 g f = fun '(w, a) => binddt (g ⦿ w) (f (w, a)).
    Proof.
      reflexivity.
    Qed.

    Lemma kc7_74 :
      forall (g : W * B -> G2 (T C)) (f : W * A -> B),
        kc7 (fun A => A) G2 g (ret (T := T) ∘ f) = g ⋆4 f.
    Proof.
      intros. unfold kc7.
      ext [w a].
      unfold compose at 1.
      compose near (f (w, a)).
      change (map (F := fun A => A) ?f) with f.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_73 :
      forall (g : W * B -> G2 (T C)) (f : A -> G1 (T B)),
        g ⋆7 (f ∘ extract (W := (W ×))) =
          fun '(w, a) => map (F := G1) (binddt (g ⦿ w)) (f a).
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_72 :
      forall (g : W * B -> G2 (T C)) (f : A -> G1 B),
        g ⋆7 (map (F := G1) ret ∘ f ∘ extract (W := (W ×))) =
          fun '(w, a) => map (F := G1) (g ∘ pair w) (f a).
    Proof.
      setup.
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_71 :
      forall (g : W * B -> G2 (T C)) (f : A -> T B),
        kc7 (fun A => A) G2 g (f ∘ extract (W := (W ×))) =
          fun '(w, a) => binddt (g ⦿ w) (f a).
    Proof.
      solve_kc7.
    Qed.

    Lemma kc7_70 :
      forall (g : W * B -> G2 (T C)) (f : A -> B),
        kc7 (fun A => A) G2 g (ret (T := T) ∘ f ∘ extract (W := (W ×))) =
          g ∘ map (F := (W ×)) f.
    Proof.
      setup.
      unfold compose; cbn.
      compose near (f a) on left.
      change (map (F := fun A => A) ?f) with f.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    (** *** Other lemmas *)
    (******************************************************************************)
    Lemma kc7_56 :
      forall (g : W * B -> T C) (f : W * A -> G1 B),
        g ⋆7 map (F := G1)(ret (T := T)) ∘ f =
          (fun '(w, a) => map (F := G1) (g ∘ pair w) (f (w, a))).
    Proof.
      setup.
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite fun_map_map.
      rewrite (kdtm_binddt0 (G := fun A => A)).
      rewrite preincr_ret.
      reflexivity.
    Qed.

    Lemma kc7_36 :
      forall (g : B -> G2 (T C)) (f : W * A -> G1 B),
        g ∘ extract ⋆7 map ret ∘ f = map g ∘ f.
    Proof.
      setup.
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite fun_map_map.
      rewrite kdtm_binddt0.
      rewrite preincr_ret.
      reflexivity.
    Qed.

  End kc7_special_cases.

  (* Open a new section here so G1 and G2 can be generalized for later lemmas to instantiate *)
  Section composition_special_cases_top.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<binddt>> on the right *)
    (******************************************************************************)
    (* composition_67 *)
    Lemma mapdt_binddt:
      forall (g : W * B -> G2 C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (mapdt g) ∘ binddt f =
          binddt (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite kdtmf_mapdt_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_67.
      reflexivity.
    Qed.

    (* composition_57 *)
    Lemma bindd_binddt:
      forall (g : W * B -> T C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (bindd g) ∘ binddt f =
          binddt (fun '(w, a) => map (F := G1) (bindd (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite kdtmf_bindd_compat.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite binddt_app_r.
      unfold kc7.
      reflexivity.
    Qed.

    (* composition_47 *)
    Lemma mapd_binddt: forall
        (g : W * B -> C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (mapd g) ∘ binddt f =
          binddt (fun '(w, a) => map (F := G1) (mapd (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite kdtmf_mapd_compat.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite binddt_app_r.
      rewrite kc7_47.
      reflexivity.
    Qed.

    (* composition_37 *)
    Lemma bindt_binddt:
      forall (g : B -> G2 (T C))
        (f : W * A -> G1 (T B)),
        map (F := G1) (bindt g) ∘ binddt f =
          binddt (G := G1 ∘ G2) (map (F := G1) (bindt g) ∘ f).
    Proof.
      intros.
      rewrite kdtmf_bindt_compat at 1.
      rewrite kdtm_binddt2.
      rewrite kc7_37.
      reflexivity.
    Qed.

    (* composition_27 *)
    Lemma traverse_binddt: forall
        (g : B -> G2 C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (traverse (T := T) (G := G2) g) ∘ binddt f =
          binddt (T := T) (G := G1 ∘ G2) (map (F := G1) (traverse (T := T) (G := G2)  g) ∘ f).
    Proof.
      intros.
      rewrite kdtmf_traverse_compat at 1.
      rewrite kdtm_binddt2.
      rewrite kc7_27.
      reflexivity.
    Qed.

    (* composition_17 *)
    Lemma bind_binddt: forall
        (g : B -> T C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (bind g) ∘ binddt f =
          binddt (map (F := G1) (bind g) ∘ f).
    Proof.
      intros.
      rewrite kdtmf_bind_compat at 1.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite kc7_17.
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (* composition_07 *)
    Lemma map_binddt:
      forall (g : B -> C)
        (f : W * A -> G1 (T B)),
        map (F := G1) (map (F := T) g) ∘ binddt f =
          binddt (map (F := G1) (map (F := T) g) ∘ f).
    Proof.
      intros.
      rewrite kdtmf_map_compat at 1.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite kc7_07.
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (** *** <<binddt>> on the left *)
    (******************************************************************************)
    (* composition_76 *)
    Lemma binddt_mapdt: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> G1 B),
        map (F := G1) (binddt g) ∘ mapdt f =
          binddt (T := T) (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (fun b => g (w, b)) (f (w, a))).
    Proof.
      intros.
      rewrite kdtmf_mapdt_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_76.
      rewrite kc6_spec.
      reflexivity.
    Qed.

    (* composition_75 *)
    Lemma binddt_bindd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> T B),
        binddt g ∘ bindd f =
          binddt (fun '(w, a) => binddt (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      rewrite kdtmf_bindd_compat.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_l.
      reflexivity.
    Qed.

    (* composition_74 *)
    Lemma binddt_mapd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> B),
        binddt g ∘ mapd f = binddt (g ⋆4 f).
    Proof.
      intros.
      rewrite kdtmf_mapd_compat.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite kc7_74.
      rewrite binddt_app_l.
      reflexivity.
    Qed.

    (* composition_73 *)
    Lemma binddt_bindt: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 (T B)),
        map (F := G1) (binddt g) ∘ bindt f =
          binddt (T := T) (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (binddt (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite kdtmf_bindt_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_73.
      reflexivity.
    Qed.

    (* composition_72 *)
    Lemma binddt_traverse: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 B),
        map (F := G1) (binddt g) ∘ traverse (T := T) (G := G1) f =
          binddt (T := T) (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (fun b => g (w, b)) (f a)).
    Proof.
      intros.
      rewrite kdtmf_traverse_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_72.
      reflexivity.
    Qed.

    (* composition_71 *)
    Lemma binddt_bind: forall
        (g : W * B -> G2 (T C))
        (f : A -> T B),
        binddt g ∘ bind f =
          binddt (fun '(w, a) => binddt (g ⦿ w) (f a)).
    Proof.
      intros.
      rewrite kdtmf_bind_compat.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_71.
      reflexivity.
    Qed.

    (* composition_70 *)
    Lemma binddt_map: forall
        (g : W * B -> G2 (T C))
        (f : A -> B),
        binddt g ∘ map (F := T) f =
          binddt (g ∘ map (F := (W ×)) f).
    Proof.
      intros.
      rewrite kdtmf_map_compat.
      change (binddt g) with (map (F := fun A => A) (binddt g)).
      rewrite (kdtm_binddt2 (G1 := fun A => A)).
      rewrite binddt_app_l.
      rewrite kc7_70.
      reflexivity.
    Qed.

  End composition_special_cases_top.

  Section composition_special_cases_middle.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<bindd>>, <<mapdt>>, <<bindt>> *)
    (******************************************************************************)
    (* composition_56 *)
    Lemma bindd_mapdt: forall
        (g : W * B -> T C)
        (f : W * A -> G1 B),
        map (F := G1) (bindd g) ∘ mapdt f =
          binddt (fun '(w, a) => map (F := G1) (g ∘ pair w) (f (w, a))).
    Proof.
      intros.
      rewrite kdtmf_bindd_compat.
      rewrite (binddt_mapdt (G2 := fun A => A)).
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (* composition_65 *)
    Lemma mapdt_bindd: forall
        (g : W * B -> G2 C)
        (f : W * A -> T B),
        mapdt g ∘ bindd f =
          binddt (fun '(w, a) => mapdt (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      rewrite kdtmf_mapdt_compat.
      rewrite binddt_bindd.
      fequal. ext [w a]. (* TODO can this be improved? *)
      rewrite kdtmf_mapdt_compat.
      reflexivity.
    Qed.

    (* composition_35 *)
    Lemma bindt_bindd: forall
        (g : B -> G2 (T C))
        (f : W * A -> T B),
        bindt g ∘ bindd f = binddt (bindt g ∘ f).
    Proof.
      intros.
      rewrite kdtmf_bindt_compat.
      rewrite binddt_bindd.
      fequal. ext [w a].
      rewrite extract_preincr2.
      reflexivity.
    Qed.

    (* composition_53 *)
    Lemma bindd_bindt: forall
        (g : W * B -> T C)
        (f : A -> G1 (T B)),
        map (F := G1) (bindd g) ∘ bindt f =
          binddt (fun '(w, a) => map (F := G1) (bindd (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite kdtmf_bindd_compat.
      rewrite kdtmf_bindt_compat.
      rewrite (kdtm_binddt2 (G2 := fun A => A)).
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (* composition_63 *)
    Lemma mapdt_bindt: forall
        (g : W * B -> G2 C)
        (f : A -> G1 (T B)),
        map (F := G1) (mapdt g) ∘ bindt f =
          binddt (G := G1 ∘ G2) (fun '(w, a) => map (F := G1) (mapdt (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite kdtmf_mapdt_compat.
      rewrite kdtmf_bindt_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_73.
      rewrite kdtmf_mapdt_compat'.
      reflexivity.
    Qed.

    (* composition_36 *)
    Lemma bindt_mapdt: forall
        (g : B -> G2 (T C))
        (f : W * A -> G1 B),
        map (F := G1) (bindt g) ∘ mapdt f =
          binddt (T := T) (G := G1 ∘ G2) (map (F := G1) g ∘ f).
    Proof.
      intros.
      rewrite kdtmf_mapdt_compat.
      rewrite kdtmf_bindt_compat.
      rewrite kdtm_binddt2.
      rewrite kc7_36.
      reflexivity.
    Qed.

  End composition_special_cases_middle.

  (* The lemmas below can cite the ones above *)
  Section composition_special_cases_bottom.

    Context
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<bindd>> on the right *)
    (******************************************************************************)

    (* composition_25 *)
    Lemma traverse_bindd: forall
        (g : B -> G2 C)
        (f : W * A -> T B),
        traverse (T := T) (G := G2) g ∘ bindd f =
          binddt (fun '(w, a) => traverse (T := T) (G := G2) g (f (w, a))).
    Proof.
      intros.
      rewrite kdtmf_traverse_compat.
      rewrite kdtmf_bindd_compat.
      change (binddt (?mapret ∘ g ∘ ?extract)) with
        (map (F := fun A => A) (binddt (mapret ∘ g ∘ extract))).
      rewrite (kdtm_binddt2 (T := T) (G1 := fun A => A)).
      rewrite (binddt_app_l).
      fequal. ext [w a].
      unfold kc7.
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

  (*
    (* composition_45 *)
    Lemma mapd_bindd: forall
        (g : W * B -> C)
        (f : W * A -> T B),
        mapd W T B C g ∘ bindd W T T A B f =
          bindd W T T A C (fun '(w, a) => mapd W T B C (g ⦿ w) (f (w, a))).
    Proof.
      intros. rewrite mapd_to_bindd.
      rewrite bindd_bindd.
      reflexivity.
    Qed.


    (* composition_15 *)
    Lemma bind_bindd: forall
        (g : B -> T C)
        (f : W * A -> T B),
        bind T T B C g ∘ bindd W T T A B f =
          bindd W T T A C (bind T T B C g ∘ f).
    Proof.
      intros. rewrite bind_to_bindd.
      rewrite bindd_bindd.
      fequal. unfold kc5. ext [w a].
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    (* composition_05 *)
    Lemma map_bindd: forall
        (g : B -> C)
        (f : W * A -> T B),
        map T B C g ∘ bindd W T T A B f =
          bindd W T T A C (map T B C g ∘ f).
    Proof.
      intros. rewrite map_to_bindd.
      rewrite bindd_bindd.
      fequal. unfold kc5. ext [w a].
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    (** *** <<bindd>> on the left *)
    (******************************************************************************)
    (* composition_54 *)
    Lemma bindd_mapd: forall
        (g : W * B -> T C)
        (f : W * A -> B),
        bindd W T T B C g ∘ mapd W T A B f =
          bindd W T T A C (g ⋆4 f).
    Proof.
      intros. rewrite mapd_to_bindd.
      rewrite bindd_bindd.
      rewrite kc5_54.
      reflexivity.
    Qed.

    (* composition_52 *)
    (* TODO bindd_traverse *)

    (* composition_51 *)
    Lemma bindd_bind: forall
        (g : W * B -> T C)
        (f : A -> T B),
        bindd W T T B C g ∘ bind T T A B f =
          bindd W T T A C (fun '(w, a) => bindd W T T B C (g ⦿ w) (f a)).
    Proof.
      intros. rewrite bind_to_bindd.
      rewrite bindd_bindd.
      reflexivity.
    Qed.

    (** *** <<mapdt>> on the left *)
    (******************************************************************************)

    (* composition_64 *)
    Lemma mapdt_mapd : forall (g : W * B -> G2 C) (f : W * A -> B),
        mapdt W T G2 B C g ∘ mapd W T A B f = mapdt W T G2 A C (g ⋆4 f).
    Proof.
      introv.
      rewrite mapd_to_mapdt.
      pose (mapdt_mapdt g f) as lemma.
      change (map (fun A => A) ?A ?B ?f) with f in lemma.
      rewrite lemma; clear lemma.
      rewrite mapdt_to_binddt.
      rewrite binddt_app_l.
      rewrite map_compose_id1.
      rewrite kc6_64.
      reflexivity.
    Qed.

    (** *** <<bindt>> on the right *)
    (******************************************************************************)
    (* composition_43 *)
    Lemma mapd_bindt : forall (g : W * B -> C) (f : A -> G1 (T B)),
        map G1 (T B) (T C) (mapd W T B C g) ∘ bindt T T G1 A B f
        = binddt W T T G1 A C (fun '(w, a) => map G1 (T B) (T C) (mapd W T B C (g ⦿ w)) (f a)).
    Proof.
      introv.
    Abort.

    (* composition_13 *)
    Lemma bind_bindt : forall (g : B -> T C) (f : A -> G1 (T B)),
        map G1 (T B) (T C) (bind T T B C g) ∘ bindt T T G1 A B f =
          bindt T T G1 A C (map G1 (T B) (T C) (bind T T B C g) ∘ f).
    Proof.
      introv.
      rewrite bind_to_bindt.
      rewrite (bindt_bindt (G2 := fun A => A)).
      rewrite bindt_to_binddt.
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (* composition_03 *)
    Lemma map_bindt : forall (g : B -> C) (f : A -> G1 (T B)),
        map G1 (T B) (T C) (map T B C g) ∘ bindt T T G1 A B f =
          bindt T T G1 A C (map G1 (T B) (T C) (map T B C g) ∘ f).
    Proof.
      intros.
      rewrite map_to_bindt.
      rewrite (bindt_bindt (G2 := fun A => A)).
      rewrite bindt_to_binddt.
      rewrite binddt_app_r.
      reflexivity.
    Qed.

    (** *** <<bindt>> on the left *)
    (******************************************************************************)
    Lemma bindt_bind : forall (g : B -> G2 (T C)) (f : A -> T B),
        bindt T T G2 B C g ∘ bind T T A B f = bindt T T G2 A C (bindt T T G2 B C g ∘ f).
    Proof.
      intros.
      rewrite bind_to_bindt.
      change (bindt T T ?X ?B ?C g) with (map (fun A => A) _ _ (bindt T T X B C g)).
      rewrite (bindt_bindt (G1 := fun A => A)).
      rewrite bindt_to_binddt.
      rewrite binddt_app_l.
      reflexivity.
    Qed.

    (* composition_30 *)
    Lemma bindt_map : forall `(g : B -> G2 (T C)) `(f : A -> B),
        bindt T T G2 B C g ∘ map T A B f = bindt T T G2 A C (g ∘ f).
    Proof.
      intros.
      rewrite map_to_bindt.
      change (bindt T T ?X ?B ?C g) with (map (fun A => A) _ _ (bindt T T X B C g)).
      rewrite (bindt_bindt (G1 := fun A => A)).
      rewrite bindt_to_binddt.
      rewrite binddt_app_l.
      rewrite kc3_30.
      reflexivity.
    Qed.

    Lemma mapd_mapdt : forall (g : W * B -> C) (f : W * A -> G1 B),
        map G1 (T B) (T C) (mapd W T B C g) ∘ mapdt W T G1 A B f =
          mapdt W T G1 A C (map G1 (W * B) C g ∘ strength ∘ cobind (W ×) A (G1 B) f).
    Proof.
      introv.
      rewrite mapd_to_mapdt.
      rewrite (mapdt_mapdt (G2 := fun A => A)).
      do 2 rewrite mapdt_to_binddt.
      rewrite binddt_app_r.
      reflexivity.
    Qed.
    *)

  End composition_special_cases_bottom.

End other_composition_laws.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆7" := (kc7 _ _) (at level 60) : tealeaves_scope.
End Notations.
