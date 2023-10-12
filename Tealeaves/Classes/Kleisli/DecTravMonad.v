From Tealeaves Require Export
  Classes.Kleisli.DecoratedFunctor
  Classes.Kleisli.DecoratedMonad
  Classes.Kleisli.TraversableFunctor
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.DecTravFunctor.

Import Monoid.Notations.
Import Product.Notations.
Import Monad.Notations.
Import Comonad.Notations.
Import DecoratedMonad.Notations.
Import TraversableFunctor.Notations.
Import TraversableMonad.Notations.
Import DecTravFunctor.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

(* Locally enable explicit arguments *)
#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.
#[local] Arguments cobind W%function_scope {Cobind} (A B)%type_scope _%function_scope _.
#[local] Arguments bindt (U T)%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments bindd W%type_scope (U T)%function_scope {Bindd} (A B)%type_scope _%function_scope _.
#[local] Arguments mapdt (E)%type_scope (T)%function_scope {Mapdt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
#[local] Arguments mapd E%type_scope (T)%function_scope {Mapd} (A B)%type_scope _%function_scope _.
#[local] Arguments bind (U T)%function_scope {Bind} (A B)%type_scope _%function_scope _.

(** * Operational typeclasses for DTM hierarchy *)
(******************************************************************************)
Class Binddt
  (W : Type)
  (U : Type -> Type)
  (T : Type -> Type) := binddt :
    forall (G : Type -> Type)
      `{Map G} `{Pure G} `{Mult G}
      (A B : Type),
      (W * A -> G (U B)) -> T A -> G (T B).

#[global] Arguments binddt {W}%type_scope {U} (T)%function_scope {Binddt} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments binddt W%type_scope (U T)%function_scope {Binddt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

Definition kc7
  (W : Type)
  (T : Type -> Type)
  `{Return T}
  `{Binddt W T T}
  `{op: Monoid_op W} `{unit: Monoid_unit W}
  {A B C}
  (G1 G2 : Type -> Type)
  `{Map G1} `{Pure G1} `{Mult G1}
  `{Map G2} `{Pure G2} `{Mult G2} :
  (W * B -> G2 (T C)) ->
  (W * A -> G1 (T B)) ->
  (W * A -> G1 (G2 (T C))) :=
  fun g f '(w, a) => map G1 (T B) (G2 (T C)) (binddt W T T G2 B C (g ⦿ w)) (f (w, a)).

#[local] Infix "⋆7" := (kc7 _ _ _ _) (at level 60) : tealeaves_scope.

Section class.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Return T}
    `{Binddt W T T}
    `{op: Monoid_op W} `{unit: Monoid_unit W}.

  Class DecTravMonad :=
    { kdtm_monoid :> Monoid W;
      kdtm_binddt0 : forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : W * A -> G (T B)),
        binddt W T T G A B f ∘ ret T A = f ∘ ret (W ×) A;
      kdtm_binddt1 : forall (A : Type),
        binddt W T T (fun A => A) A A (ret T A ∘ extract (W ×) A) = @id (T A);
      kdtm_binddt2 :
      forall (G1 G2 : Type -> Type) `{Applicative G1} `{Applicative G2}
        (A B C : Type)
        (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (binddt W T T G2 B C g) ∘ binddt W T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (g ⋆7 f);
      kdtm_morph : forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : W * A -> G1 (T B)),
        ϕ (T B) ∘ binddt W T T G1 A B f = binddt W T T G2 A B (ϕ (T B) ∘ f);
    }.

End class.

Arguments incr {W}%type_scope {op} {A}%type_scope _ _.
Arguments preincr {W}%type_scope {op} {A B}%type_scope f%function_scope w _.

(** * Interaction of [traverse] with functor composition *)
(******************************************************************************)
Section properties.

  Context
    (T : Type -> Type)
    `{DecTravMonad W T}.


  Lemma binddt_app_l :
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : W * A -> G (T B)),
      @binddt W T T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G) (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f = binddt W T T G A B f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma binddt_app_r :
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : W * A -> G (T B)),
      @binddt W T T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A)) (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f = binddt W T T G A B f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity1.
  Qed.

End properties.


(** * Laws for <<kc7>> *)
(******************************************************************************)
Section kc7.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Return T}
    `{Binddt W T T}
    `{op: Monoid_op W} `{unit: Monoid_unit W}
    `{! Monoid W}.

  (** ** Interaction with [incr], [preincr] *)
  (******************************************************************************)
  Lemma kc7_incr : forall
      `{Applicative G1} `{Applicative G2}
      `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)) (w : W),
      (g ∘ incr w) ⋆7 (f ∘ incr w) = (g ⋆7 f) ∘ incr w.
  Proof.
    intros. unfold kc7. ext [w' a].
    unfold preincr. reassociate ->.
    now rewrite (incr_incr W).
  Qed.

  Lemma kc7_preincr : forall
      `{Applicative G1} `{Applicative G2}
      `(g : W * B -> G2 (T C)) `(f : W * A -> G1 (T B)) (w : W),
      (g ⦿ w) ⋆7 (f ⦿ w) = (g ⋆7 f) ⦿ w.
  Proof.
    intros. unfold preincr. rewrite kc7_incr.
    reflexivity.
  Qed.

  Context
    `{! DecTravMonad W T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}
    {A B C D : Type}.

  (** ** Category laws *)
  (******************************************************************************)
  Lemma kc7_id1 : forall (f : W * A -> G (T B)),
      kc7 W T G (fun A => A) (ret T B ∘ extract (W ×) B) f = f.
  Proof.
    intros. unfold kc7.
    ext [w a].
    rewrite (preincr_assoc).
    rewrite (extract_preincr W).
    rewrite (kdtm_binddt1 W T).
    rewrite (fun_map_id).
    reflexivity.
  Qed.

  Lemma kc7_id2 : forall (g : W * A -> G (T B)),
      kc7 W T (fun A => A) G g (ret T A ∘ extract (W ×) A) = g.
  Proof.
    intros. unfold kc7. ext [w a].
    change (map (fun A => A) _ _ ?f) with f.
    change_left ((binddt W T T G A B (g ⦿ w) ∘ ret T A) a).
    rewrite (kdtm_binddt0 W T G).
    change ((g ⦿ w) (Ƶ, a)  = g (w, a)).
    change (g (w ● Ƶ, a)  = g (w, a)).
    simpl_monoid.
    reflexivity.
  Qed.

  Lemma kc7_assoc :
    forall (h : W * C -> G3 (T D)) (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
      kc7 W T (G1 ∘ G2) G3 h (g ⋆7 f) =
        kc7 W T G1 (G2 ∘ G3) (h ⋆7 g) f.
  Proof.
    intros. unfold kc7.
    ext [w a].
    unfold_ops @Map_compose.
    compose near (f (w, a)) on left.
    rewrite (fun_map_map).
    fequal.
    rewrite (kdtm_binddt2 W T); auto.
    fequal.
    rewrite kc7_preincr.
    reflexivity.
  Qed.

End kc7.

(** * Derived Instances *)
(******************************************************************************)
Module DerivedInstances.

  (** ** Derived operations *)
  (******************************************************************************)
  Section operations.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Binddt W T T}
      `{Return T}.

    #[export] Instance Map_Binddt : Map T :=
      fun (A B : Type) (f : A -> B) => binddt W T T (fun A => A) A B (ret T B ∘ f ∘ extract (W ×) A).
    #[export] Instance Mapdt_Binddt: Mapdt W T
      := fun G _ _ _ A B f => binddt W T T G A B (map G B (T B) (ret T B) ∘ f).
    #[export] Instance Bindd_Binddt: Bindd W T T
      := fun A B f => binddt W T T (fun A => A) A B f.
    #[export] Instance Bindt_Binddt: Bindt T T
      := fun G _ _ _ A B f => binddt W T T G A B (f ∘ extract (W ×) A).
    #[export] Instance Bind_Binddt: Bind T T
      := fun A B f => binddt W T T (fun A => A) A B (f ∘ extract (W ×) A).
    #[export] Instance Mapd_Binddt: Mapd W T
      := fun A B f => binddt W T T (fun A => A) A B (ret T B ∘ f).
    #[export] Instance Traverse_Binddt: Traverse T
      := fun G _ _ _ A B f => binddt W T T G A B (map G B (T B) (ret T B) ∘ f ∘ extract (W ×) A).

  End operations.

  Section special_cases.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Return T}
      `{Binddt W T T}
      `{Applicative G}.

    (** *** Rewriting rules for special cases of <<binddt>> *)
    (******************************************************************************)
    Lemma bindt_to_binddt `(f : A -> G (T B)):
      bindt T T G A B f = binddt W T T G A B (f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    Lemma bindd_to_binddt `(f : W * A -> T B):
      bindd W T T A B f = binddt W T T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    Lemma mapdt_to_binddt `(f : W * A -> G B):
      mapdt W T G A B f = binddt W T T G A B (map G B (T B) (ret T B) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma bind_to_binddt `(f : A -> T B):
      bind T T A B f = binddt W T T (fun A => A) A B (f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    Lemma mapd_to_binddt `(f : W * A -> B):
      mapd W T A B f = binddt W T T (fun A => A) A B (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_binddt `(f : A -> G B):
      traverse T G A B f = binddt W T T G A B (map G B (T B) (ret T B) ∘ f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_binddt `(f : A -> B):
      map T A B f = binddt W T T (fun A => A) A B (ret T B ∘ f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bindt>> *)
    (******************************************************************************)
    Lemma bind_to_bindt `(f : A -> T B):
      bind T T A B f = bindt T T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_bindt `(f : A -> G B):
      traverse T G A B f = bindt T T G A B (map G B (T B) (ret T B) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindt `(f : A -> B):
      map T A B f = bindt T T (fun A => A) A B (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bindd>> *)
    (******************************************************************************)
    Lemma bind_to_bindd `(f : A -> T B):
      bind T T A B f = bindd W T T A B (f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    Lemma mapd_to_bindd `(f : W * A -> B):
      mapd W T A B f = bindd W T T A B (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindd `(f : A -> B):
      map T A B f = bindd W T T A B (ret T B ∘ f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mapdt>> *)
    (******************************************************************************)
    Lemma mapd_to_mapdt `(f : W * A -> B):
      mapd W T A B f = mapdt W T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_mapdt `(f : A -> B):
      map T A B f = mapdt W T (fun A => A) A B (f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_mapdt `(f : A -> G B):
      traverse T G A B f = mapdt W T G A B (f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<traverse>> *)
    (******************************************************************************)
    Lemma map_to_traverse `(f : A -> B):
      map T A B f = traverse T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mapd>> *)
    (******************************************************************************)
    Lemma map_to_mapd `(f : A -> B):
      map T A B f = mapd W T A B (f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bind>> *)
    (******************************************************************************)
    Lemma map_to_bind `(f : A -> B):
      map T A B f = bind T T A B (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

  End special_cases.

  (** ** Rewriting rules for special cases of <<kc7>> *)
  (******************************************************************************)
  Section kc7_special_cases.

    Context
      (W : Type)
      (T : Type -> Type)
      `{DecTravMonad W T}
      `{Applicative G1}
      `{Applicative G2}
      {A B C D : Type}.

    (** *** Lemmas for <<kcx_yz>> (x < 7) *)
    (******************************************************************************)
    Lemma kc5_54 :
      forall `(g : W * B -> T C) `(f : W * A -> B),
        g ⋆5 ret T B ∘ f = g ⋆4 f.
    Proof.
      intros.
      unfold kc5, kc4.
      ext [w a].
      unfold preincr, compose; cbn.
      change (id ?x) with x.
      compose near (f (w, a)) on left.
      rewrite (bindd_to_binddt W T).
      rewrite (kdtm_binddt0 W T (fun A => A)).
      unfold compose; cbn.
      simpl_monoid.
      reflexivity.
    Qed.

    Lemma kc5_44 :
      forall `(g : W * B -> C) `(f : W * A -> B),
        ret T C ∘ g ⋆5 ret T B ∘ f = ret T C ∘ (g ⋆4 f).
    Proof.
      intros.
      unfold kc5, kc4.
      ext [w a].
      unfold preincr, compose; cbn.
      change (id ?x) with x.
      compose near (f (w, a)) on left.
      rewrite (bindd_to_binddt W T).
      rewrite (kdtm_binddt0 W T (fun A => A)).
      unfold compose; cbn.
      simpl_monoid.
      reflexivity.
    Qed.

    (** *** Lemmas <<kc7_xx>> *)
    (******************************************************************************)
    Lemma kc7_66 :
        forall (g : W * B -> G2 C) (f : W * A -> G1 B),
        (map G2 C (T C) (ret T C) ∘ g) ⋆7 (map G1 B (T B) (ret T B) ∘ f) =
          map (G1 ∘ G2) C (T C) (ret T C) ∘ (g ⋆6 f).
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      unfold compose at 2.
      compose near (f (w, a)).
      rewrite (fun_map_map).
      rewrite (kdtm_binddt0 W T G2 B C).
      unfold kc6.
      unfold_ops @Map_compose;
        do 2 reassociate <-;
          unfold_compose_in_compose.
      rewrite (fun_map_map).
      unfold compose; cbn.
      compose near (f (w, a)) on right.
      rewrite (fun_map_map).
      unfold preincr, compose; cbn.
      simpl_monoid.
      reflexivity.
    Qed.

    Lemma kc7_55 : forall
        `(g : W * B -> T C) `(f : W * A -> T B),
        kc7 W T (fun A => A) (fun A => A) g f = kc5 W T g f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc7_44 : forall
        `(g : W * B -> C) `(f : W * A -> B),
        kc7 W T (fun A => A) (fun A => A) (ret T C ∘ g) (ret T B ∘ f) =
          ret T C ∘ (g ⋆4 f).
    Proof.
      intros. rewrite kc7_55. rewrite kc5_44.
      reflexivity.
    Qed.

    Lemma kc7_33 :
      forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        kc7 W T G1 G2 (g ∘ extract (W ×) B) (f ∘ extract (W ×) A) =
          (g ⋆3 f) ∘ extract (W ×) A.
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    Lemma kc7_22 :
      forall (g : B -> G2 C) (f : A -> G1 B),
        kc7 W T G1 G2
          (map G2 C (T C) (ret T C) ∘ g ∘ extract (W ×) B)
          (map G1 B (T B) (ret T B) ∘ f ∘ extract (W ×) A) =
          map (G1 ∘ G2) C (T C) (ret T C) ∘ (map G1 B (G2 C) g ∘ f) ∘ extract (W ×) A.
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      rewrite preincr_assoc.
      reassociate ->.
      reassociate ->.
      rewrite extract_preincr.
      unfold compose at 1 2 3 4; cbn.
      compose near (f a) on left.
      rewrite (fun_map_map).
      rewrite (kdtm_binddt0 W T G2).
      unfold_ops @Map_compose.
      unfold compose; cbn.
      compose near (f a) on right.
      rewrite (fun_map_map).
      reflexivity.
    Qed.

    Lemma kc7_11 :
      forall (g : B -> T C) (f : A -> T B),
        kc7 W T (fun A => A) (fun A => A)
          (g ∘ extract (W ×) B)
          (f ∘ extract (W ×) A) =
          (g ⋆1 f) ∘ extract (W ×) A.
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    Lemma kc7_00 :
      forall (g : B -> C) (f : A -> B),
        kc7 W T (fun A => A) (fun A => A) (ret T C ∘ g ∘ extract (W ×) B) (ret T B ∘ f ∘ extract (W ×) A) =
          (ret T C ∘ g ∘ f ∘ extract (W ×) A).
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      change (map (fun A => A) _ _ ?f) with f.
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite (kdtm_binddt0 W T (fun A => A)).
      rewrite (preincr_ret W).
      unfold compose; cbn.
      reflexivity.
    Qed.

    (** *** Lemmas <<kc7_x7>> *)
    (******************************************************************************)
    Theorem kc7_07 :
      forall (g : B -> C) (f : W * A -> G1 (T B)),
        ret T C ∘ g ∘ extract (prod W) B ⋆7 f =
          map G1 (T B) (T C) (map T B C g) ∘ f.
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      rewrite (preincr_assoc).
      rewrite (extract_preincr).
      reflexivity.
    Qed.

    Theorem kc7_17 :
      forall (g : B -> T C) (f : W * A -> G1 (T B)),
        g ∘ extract (prod W) B ⋆7 f =
          map G1 (T B) (T C) (bind T T B C g) ∘ f.
    Proof.
      intros.
      unfold kc7.
      ext [w a].
      rewrite (preincr_assoc).
      rewrite (extract_preincr).
      reflexivity.
    Qed.

    Theorem kc7_27 :
      forall (g : B -> G2 C) (f : W * A -> G1 (T B)),
        map G2 C (T C) (ret T C) ∘ g ∘ extract (prod W) B ⋆7 f =
          map G1 (T B) (G2 (T C)) (traverse T G2 B C g) ∘ f.
    Proof.
      intros. unfold kc7.
      ext [w a].
      rewrite (preincr_assoc).
      rewrite (extract_preincr).
      reflexivity.
    Qed.

    Theorem kc7_37 :
      forall (g : B -> G2 (T C)) (f : W * A -> G1 (T B)),
        (g ∘ extract (W ×) B) ⋆7 f = g ⋆3 f.
    Proof.
      intros. unfold kc7.
      ext [w a].
      rewrite (preincr_assoc).
      rewrite (extract_preincr).
      reflexivity.
    Qed.

    Theorem kc7_47 :
      forall (g : W * B -> C) (f : W * A -> G1 (T B)),
        kc7 W T G1 (fun A => A) (ret T C ∘ g) f = (fun '(w, a) => map G1 (T B) (T C) (mapd W T B C (g ⦿ w)) (f (w, a))).
    Proof.
      reflexivity.
    Qed.


    Theorem kc7_57 :
      forall (g : W * B -> T C) (f : W * A -> G1 (T B)),
        kc7 W T G1 (fun A => A) g f = g ⋆7 f.
    Proof.
      reflexivity.
    Qed.

    Theorem kc7_67 :
      forall (g : W * B -> G2 C) (f : W * A -> G1 (T B)),
        (map G2 C (T C) (ret T C) ∘ g) ⋆7 f = (fun '(w, a) => map G1 (T B) (G2 (T C)) (mapdt W T G2 B C (g ⦿ w)) (f (w, a))).
    Proof.
      reflexivity.
    Qed.

    (** *** Lemmas <<kc7_7x>> *)
    (******************************************************************************)
    Theorem kc7_76 :
      forall (g : W * B -> G2 (T C)) (f : W * A -> G1 B),
        g ⋆7 (map G1 B (T B) (ret T B) ∘ f) = g ⋆6 f.
    Proof.
      intros. unfold kc7, kc6.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)).
      rewrite (fun_map_map).
      rewrite (fun_map_map).
      rewrite (kdtm_binddt0 W T G2).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

    Theorem kc7_75 :
      forall (g : W * B -> G2 (T C)) (f : W * A -> T B),
        kc7 W T (fun A => A) G2 g f = fun '(w, a) => binddt W T T G2 B C (g ⦿ w) (f (w, a)).
    Proof.
      reflexivity.
    Qed.

    Lemma kc7_74 :
        forall (g : W * B -> G2 (T C)) (f : W * A -> B),
          kc7 W T (fun A => A) G2 g (ret T B ∘ f) = g ⋆4 f.
    Proof.
      intros. unfold kc7.
      ext [w a].
      unfold compose at 1.
      compose near (f (w, a)).
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (kdtm_binddt0 W T G2).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

    Theorem kc7_73 :
      forall (g : W * B -> G2 (T C)) (f : A -> G1 (T B)),
        g ⋆7 (f ∘ extract (W ×) A) =
          fun '(w, a) => map G1 (T B) (G2 (T C)) (binddt W T T G2 B C (g ⦿ w)) (f a).
    Proof.
      intros. unfold kc7.
      ext [w a]. unfold compose. cbn.
      reflexivity.
    Qed.

    Theorem kc7_72 :
      forall (g : W * B -> G2 (T C)) (f : A -> G1 B),
        g ⋆7 (map G1 B (T B) (ret T B) ∘ f ∘ extract (W ×) A) =
          fun '(w, a) => map G1 B (G2 (T C)) (g ∘ pair w) (f a).
    Proof.
      intros. unfold kc7.
      ext [w a].
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite (fun_map_map).
      rewrite (kdtm_binddt0 W T G2).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

    Theorem kc7_71 :
      forall (g : W * B -> G2 (T C)) (f : A -> T B),
        kc7 W T (fun A => A) G2 g (f ∘ extract (W ×) A) =
          fun '(w, a) => binddt W T T G2 B C (g ⦿ w) (f a).
    Proof.
      intros. unfold kc7.
      ext [w a].
      unfold compose; cbn.
      change (map (fun A => A) _ _ ?f) with f.
      reflexivity.
    Qed.

    Lemma kc7_70 :
      forall (g : W * B -> G2 (T C)) (f : A -> B),
        kc7 W T (fun A => A) G2 g (ret T B ∘ f ∘ extract (W ×) A) = g ∘ map (W ×) A B f.
    Proof.
      intros. unfold kc7.
      ext [w a].
      unfold compose; cbn.
      compose near (f a) on left.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (kdtm_binddt0 W T G2).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

    (** *** Other lemmas *)
    (******************************************************************************)
    Lemma kc3_30 :
      forall (g : B -> G2 (T C))
        (f : A -> B),
        (g ⋆3 ret T B ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc3.
      reassociate <-.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (bindt_to_binddt).
      rewrite (kdtm_binddt0 W T G2).
      reflexivity.
    Qed.

    Lemma kc6_64 :
      forall (g : W * B -> G2 C) (f : W * A -> B),
        g ⋆6 f = g ⋆4 f.
    Proof.
      intros. now ext [w a].
    Qed.

    Lemma kc7_56 :
      forall (g : W * B -> T C) (f : W * A -> G1 B),
        g ⋆7 map G1 B (T B) (ret T B) ∘ f = (fun '(w, a) => map G1 B (T C) (g ∘ pair w) (f (w, a))).
    Proof.
      intros. unfold kc7.
      ext [w a].
      unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite (fun_map_map).
      rewrite (kdtm_binddt0 W T (fun A => A)).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

End kc7_special_cases.

  Section assume_dtm.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DecTravMonad W T}.


  (* Open a new section here so G1 and G2 can be generalized for later lemmas to instantiate *)
  Section composition_special_cases_top.

    Context
      (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<binddt>> on the right *)
    (******************************************************************************)
    (* composition_67 *)
    Lemma mapdt_binddt:
      forall (g : W * B -> G2 C)
        (f : W * A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (mapdt W T G2 B C g) ∘ binddt W T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (fun '(w, a) => map G1 (T B) (G2 (T C)) (mapdt W T G2 B C (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite mapdt_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 G2 A B C).
      rewrite (kc7_67).
      reflexivity.
    Qed.

    (* composition_57 *)
    Lemma bindd_binddt:
      forall (g : W * B -> T C)
        (f : W * A -> G1 (T B)),
        map G1 (T B) (T C) (bindd W T T B C g) ∘ binddt W T T G1 A B f =
          binddt W T T G1 A C (fun '(w, a) => map G1 (T B) (T C) (bindd W T T B C (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 (fun A => A)).
      rewrite (binddt_app_r T G1).
      (* rewrite kc7_57 *)
      reflexivity.
    Qed.

    (* composition_47 *)
    Lemma mapd_binddt: forall
        (g : W * B -> C)
        (f : W * A -> G1 (T B)),
        map G1 (T B) (T C) (mapd W T B C g) ∘ binddt W T T G1 A B f =
          binddt W T T G1 A C (fun '(w, a) => map G1 (T B) (T C) (mapd W T B C (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite mapd_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 (fun A => A) A B).
      rewrite (binddt_app_r T G1).
      rewrite kc7_47.
      reflexivity.
    Qed.

    (* composition_37 *)
    Lemma bindt_binddt:
      forall (g : B -> G2 (T C))
        (f : W * A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (bindt T T G2 B C g) ∘ binddt W T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (map G1 (T B) (G2 (T C)) (bindt T T G2 B C g) ∘ f).
    Proof.
      intros.
      rewrite bindt_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 G2 A B C).
      rewrite kc7_37.
      reflexivity.
    Qed.

    (* composition_27 *)
    Lemma traverse_binddt: forall
        (g : B -> G2 C)
        (f : W * A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (traverse T G2 B C g) ∘ binddt W T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (map G1 (T B) (G2 (T C)) (traverse T G2 B C  g) ∘ f).
    Proof.
      intros.
      rewrite (traverse_to_binddt) at 1.
      rewrite (kdtm_binddt2 W T G1 G2 A B C).
      rewrite (kc7_27).
      reflexivity.
    Qed.

    (* composition_17 *)
    Lemma bind_binddt: forall
        (g : B -> T C)
        (f : W * A -> G1 (T B)),
        map G1 (T B) (T C) (bind T T B C g) ∘ binddt W T T G1 A B f =
          binddt W T T G1 A C (map G1 (T B) (T C) (bind T T B C g) ∘ f).
    Proof.
      intros.
      rewrite bind_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 (fun A => A)).
      rewrite kc7_17.
      rewrite (binddt_app_r T G1).
      reflexivity.
    Qed.

    (* composition_07 *)
    Lemma map_binddt:
      forall (g : B -> C)
        (f : W * A -> G1 (T B)),
        map G1 (T B) (T C) (map T B C g) ∘ binddt W T T G1 A B f =
          binddt W T T G1 A C (map G1 (T B) (T C) (map T B C g) ∘ f).
    Proof.
      intros.
      rewrite map_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 (fun A => A)).
      rewrite kc7_07.
      rewrite (binddt_app_r T G1).
      reflexivity.
    Qed.

    (** *** <<binddt>> on the left *)
    (******************************************************************************)
    (* composition_76 *)
    Lemma binddt_mapdt: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> G1 B),
        map G1 (T B) (G2 (T C)) (binddt W T T G2 B C g) ∘ mapdt W T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (fun '(w, a) => map G1 B (G2 (T C)) (fun b => g (w, b)) (f (w, a))).
    Proof.
      intros.
      rewrite (mapdt_to_binddt).
      rewrite (kdtm_binddt2 W T G1 G2 A B C).
      rewrite (kc7_76 W T).
      unfold kc6.
      fequal. ext [w a].
      unfold compose, strength; cbn.
      compose near (f (w, a)) on left.
      rewrite (fun_map_map).
      reflexivity.
    Qed.

    (* composition_75 *)
    Lemma binddt_bindd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> T B),
        binddt W T T G2 B C g ∘ bindd W T T A B f =
          binddt W T T G2 A C (fun '(w, a) => binddt W T T G2 B C (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      change (binddt W T T G2 B C g) with (map (fun A => A) (T B) (G2 (T C)) (binddt W T T G2 B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) G2).
      rewrite (binddt_app_l T G2).
      reflexivity.
    Qed.

    (* composition_74 *)
    Lemma binddt_mapd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> B),
        binddt W T T G2 B C g ∘ mapd W T A B f =
          binddt W T T G2 A C (g ⋆4 f).
    Proof.
      intros.
      rewrite (mapd_to_binddt) at 1.
      change (binddt W T T G2 B C g) with (map (fun A => A) (T B) (G2 (T C)) (binddt W T T G2 B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) G2 A B C).
      rewrite (kc7_74 W T).
      rewrite (binddt_app_l T G2).
      reflexivity.
    Qed.

    (* composition_73 *)
    Lemma binddt_bindt: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (binddt W T T G2 B C g) ∘ bindt T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (fun '(w, a) => map G1 (T B) (G2 (T C)) (binddt W T T G2 B C (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite (bindt_to_binddt).
      rewrite (kdtm_binddt2 W T G1 G2).
      rewrite kc7_73.
      reflexivity.
    Qed.

    (* composition_72 *)
    Lemma binddt_traverse: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 B),
        map G1 (T B) (G2 (T C)) (binddt W T T G2 B C g) ∘ traverse T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (fun '(w, a) => map G1 B (G2 (T C)) (fun b => g (w, b)) (f a)).
    Proof.
      intros.
      rewrite (traverse_to_binddt).
      rewrite (kdtm_binddt2 W T G1 G2 A B C).
      rewrite (kc7_72 W T).
      reflexivity.
    Qed.

    (* composition_71 *)
    Lemma binddt_bind: forall
        (g : W * B -> G2 (T C))
        (f : A -> T B),
        binddt W T T G2 B C g ∘ bind T T A B f =
          binddt W T T G2 A C (fun '(w, a) => binddt W T T G2 B C (g ⦿ w) (f a)).
    Proof.
      intros.
      rewrite (bind_to_binddt).
      change (binddt W T T G2 B C g) with (map (fun A => A) (T B) (G2 (T C)) (binddt W T T G2 B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) G2 A B C).
      rewrite (binddt_app_l T G2).
      rewrite (kc7_71).
      reflexivity.
    Qed.

    (* composition_70 *)
    Lemma binddt_map: forall
        (g : W * B -> G2 (T C))
        (f : A -> B),
        binddt W T T G2 B C g ∘ map T A B f =
          binddt W T T G2 A C (g ∘ map (W ×) A B f).
    Proof.
      intros.
      rewrite (map_to_binddt).
      change (binddt W T T G2 B C g) with (map (fun A => A) _ _ (binddt W T T G2 B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) G2 A B C).
      rewrite (binddt_app_l T G2).
      rewrite (kc7_70 W T).
      reflexivity.
    Qed.

  End composition_special_cases_top.

  (* The lemmas below can cite the ones above *)
  (* We look at compositions involving 6, 5, and 3 *)
  Section composition_special_cases_middle.

    Context
      (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<bindd>>, <<mapdt>>, <<bindt>> *)
    (******************************************************************************)
    (* composition_66 *)
    Lemma mapdt_mapdt: forall
        (g : W * B -> G2 C)
        (f : W * A -> G1 B),
        map G1 (T B) (G2 (T C)) (mapdt W T G2 B C g) ∘ mapdt W T G1 A B f =
          mapdt W T (G1 ∘ G2) A C (g ⋆6 f).
    Proof.
      intros.
      do 2 rewrite (mapdt_to_binddt) at 1.
      rewrite (kdtm_binddt2 W T G1 G2).
      rewrite (kc7_66 W T).
      reflexivity.
    Qed.

    (* composition_55 *)
    Lemma bindd_bindd : forall
        (g : W * B -> T C)
        (f : W * A -> T B),
        bindd W T T B C g ∘ bindd W T T A B f = bindd W T T A C (g ⋆5 f).
    Proof.
      intros.
      do 2 rewrite (bindd_to_binddt).
      change (binddt W T T ?X ?B ?C g) with (map (fun A => A) _ _ (binddt W T T X B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) (fun A => A)).
      rewrite (binddt_app_l T (fun A => A)).
      reflexivity.
    Qed.

    (* composition_33 *)
    Lemma bindt_bindt : forall
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (bindt T T G2 B C g) ∘ bindt T T G1 A B f = bindt T T (G1 ∘ G2) A C (g ⋆3 f).
    Proof.
      intros.
      do 2 rewrite (bindt_to_binddt).
      rewrite (kdtm_binddt2 W T); auto.
      rewrite (kc7_33).
      reflexivity.
    Qed.

    (* composition_56 *)
    Lemma bindd_mapdt: forall
        (g : W * B -> T C)
        (f : W * A -> G1 B),
        map G1 (T B) (T C) (bindd W T T B C g) ∘ mapdt W T G1 A B f =
          binddt W T T G1 A C (fun '(w, a) => map G1 B (T C) (g ∘ pair w) (f (w, a))).
    Proof.
      intros.
      rewrite (bindd_to_binddt).
      rewrite (binddt_mapdt G1 (fun A => A)).
      rewrite (binddt_app_r T G1).
      reflexivity.
    Qed.

    (* composition_65 *)
    Lemma mapdt_bindd: forall
        (g : W * B -> G2 C)
        (f : W * A -> T B),
        mapdt W T G2 B C g ∘ bindd W T T A B f =
          binddt W T T G2 A C (fun '(w, a) => mapdt W T G2 B C (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      rewrite (mapdt_to_binddt).
      rewrite (binddt_bindd G2).
      reflexivity.
    Qed.

    (* composition_35 *)
    Lemma bindt_bindd: forall
        (g : B -> G2 (T C))
        (f : W * A -> T B),
        bindt T T G2 B C g ∘ bindd W T T A B f =
          binddt W T T G2 A C (bindt T T G2 B C g ∘ f).
    Proof.
      intros.
      rewrite (bindt_to_binddt).
      rewrite (binddt_bindd G2).
      fequal; ext [w a].
      rewrite (preincr_assoc).
      rewrite (extract_preincr).
      reflexivity.
    Qed.

    (* composition_53 *)
    Lemma bindd_bindt: forall
        (g : W * B -> T C)
        (f : A -> G1 (T B)),
        map G1 _ _ (bindd W T T B C g) ∘ bindt T T G1 A B f =
          binddt W T T G1 A C (fun '(w, a) => map G1 _ _ (bindd W T T B C (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite (bindd_to_binddt).
      rewrite (bindt_to_binddt).
      rewrite (kdtm_binddt2 W T G1 (fun A => A) A B C).
      rewrite (binddt_app_r T G1).
      reflexivity.
    Qed.

    (* composition_63 *)
    Lemma mapdt_bindt: forall
        (g : W * B -> G2 C)
        (f : A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (mapdt W T G2 B C g) ∘ bindt T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (fun '(w, a) => map G1 (T B) (G2 (T C)) (mapdt W T G2 B C (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite (mapdt_to_binddt).
      rewrite (bindt_to_binddt).
      rewrite (kdtm_binddt2 W T G1 G2 A B C).
      reflexivity.
    Qed.

    (* composition_36 *)
    Lemma bindt_mapdt: forall
        (g : B -> G2 (T C))
        (f : W * A -> G1 B),
        map G1 _ _ (bindt T T G2 _ _ g) ∘ mapdt W T G1 _ _ f =
          binddt W T T (G1 ∘ G2) _ _ (map G1 B (G2 (T C)) g ∘ f).
    Proof.
      intros.
      rewrite bindt_to_binddt.
      rewrite (binddt_mapdt G1 G2).
      fequal. now ext [w a].
    Qed.

  End composition_special_cases_middle.

  (* The lemmas below can cite the ones above *)
  Section composition_special_cases_bottom.

    Context
      (G1 G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** *** <<bindd>> on the right *)
    (******************************************************************************)
    (* composition_45 *)
    Lemma mapd_bindd: forall
        (g : W * B -> C)
        (f : W * A -> T B),
        mapd W T B C g ∘ bindd W T T A B f =
          bindd W T T A C (fun '(w, a) => mapd W T B C (g ⦿ w) (f (w, a))).
    Proof.
      intros. rewrite (mapd_to_bindd W T).
      rewrite (bindd_bindd).
      reflexivity.
    Qed.

    (* composition_25 *)
    Lemma traverse_bindd: forall
        (g : B -> G2 C)
        (f : W * A -> T B),
        traverse T G2 B C g ∘ bindd W T T A B f =
          binddt W T T G2 A C (fun '(w, a) => traverse T G2 B C g (f (w, a))).
    Proof.
      intros. rewrite (traverse_to_mapdt).
      rewrite (mapdt_bindd G2).
      fequal; ext [w a].
      rewrite (preincr_assoc W).
      rewrite (extract_preincr W).
      reflexivity.
    Qed.

    (* composition_15 *)
    Lemma bind_bindd: forall
        (g : B -> T C)
        (f : W * A -> T B),
        bind T T B C g ∘ bindd W T T A B f =
          bindd W T T A C (bind T T B C g ∘ f).
    Proof.
      intros. rewrite (bind_to_bindd W T).
      rewrite (bindd_bindd).
      fequal. unfold kc5. ext [w a].
      rewrite (preincr_assoc W).
      rewrite (extract_preincr W).
      reflexivity.
    Qed.

    (* composition_05 *)
    Lemma map_bindd: forall
        (g : B -> C)
        (f : W * A -> T B),
        map T B C g ∘ bindd W T T A B f =
          bindd W T T A C (map T B C g ∘ f).
    Proof.
      intros. rewrite (map_to_bindd W T).
      rewrite (bindd_bindd).
      fequal. unfold kc5. ext [w a].
      rewrite (preincr_assoc W).
      rewrite (extract_preincr W).
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
      intros. rewrite (mapd_to_bindd W T).
      rewrite (bindd_bindd).
      rewrite (kc5_54 W T).
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
      intros. rewrite (bind_to_bindd W T).
      rewrite (bindd_bindd).
      reflexivity.
    Qed.

    (* composition_50 *)
    (* TODO bindd_map *)

    (** *** <<mapdt>> on the right *)
    (******************************************************************************)
    (* composition_46 *)
    Lemma mapd_mapdt : forall (g : W * B -> C) (f : W * A -> G1 B),
        map G1 (T B) (T C) (mapd W T B C g) ∘ mapdt W T G1 A B f =
          mapdt W T G1 A C (map G1 (W * B) C g ∘ strength G1 ∘ cobind (W ×) A (G1 B) f).
    Proof.
      introv.
      rewrite (mapd_to_mapdt).
      rewrite (mapdt_mapdt G1 (fun A => A)).
      do 2 rewrite (mapdt_to_binddt).
      rewrite (binddt_app_r T G1).
      reflexivity.
    Qed.

    (* composition_16 *)
    (* TODO bind_mapdt *)

    (* composition_26 *)
    (* TODO traverse_mapdt *)

    (* composition_06 *)
    (* TODO map_mapdt *)

    (** *** <<mapdt>> on the left *)
    (******************************************************************************)

    (* composition_64 *)
    Lemma mapdt_mapd : forall (g : W * B -> G2 C) (f : W * A -> B),
        mapdt W T G2 B C g ∘ mapd W T A B f = mapdt W T G2 A C (g ⋆4 f).
    Proof.
      introv.
      rewrite (mapd_to_mapdt).
      pose (mapdt_mapdt (fun A => A) G2 (A := A) (B := B) (C := C) g f) as lemma.
      change (map (fun A => A) ?A ?B ?f) with f in lemma.
      rewrite lemma; clear lemma.
      rewrite (mapdt_to_binddt).
      rewrite (binddt_app_l T G2).
      rewrite (map_id_l G2).
      rewrite (kc6_64).
      reflexivity.
    Qed.

    (* composition_61 *)
    (* TODO mapdt_bind *)

    (* composition_62 *)
    (* TODO mapdt_traverse *)

    (* composition_60 *)
    (* TODO mapdt_map *)

    (** *** <<bindt>> on the right *)
    (******************************************************************************)
    (* composition_43 *)
    Lemma mapd_bindt : forall (g : W * B -> C) (f : A -> G1 (T B)),
        map G1 (T B) (T C) (mapd W T B C g) ∘ bindt T T G1 A B f
        = binddt W T T G1 A C (fun '(w, a) => map G1 (T B) (T C) (mapd W T B C (g ⦿ w)) (f a)).
    Proof.
      introv.
    Abort.

    (* composition_23 *)
    (* traverse_bindt *)

    (* composition_13 *)
    Lemma bind_bindt : forall (g : B -> T C) (f : A -> G1 (T B)),
        map G1 (T B) (T C) (bind T T B C g) ∘ bindt T T G1 A B f =
          bindt T T G1 A C (map G1 (T B) (T C) (bind T T B C g) ∘ f).
    Proof.
      introv.
      rewrite (bind_to_bindt).
      rewrite (bindt_bindt G1 (fun A => A)).
      rewrite (bindt_to_binddt).
      rewrite (binddt_app_r T G1).
      reflexivity.
    Qed.

    (* composition_03 *)
    Lemma map_bindt : forall (g : B -> C) (f : A -> G1 (T B)),
        map G1 (T B) (T C) (map T B C g) ∘ bindt T T G1 A B f =
          bindt T T G1 A C (map G1 (T B) (T C) (map T B C g) ∘ f).
    Proof.
      intros.
      rewrite (map_to_bindt).
      rewrite (bindt_bindt G1 (fun A => A)).
      rewrite (bindt_to_binddt).
      rewrite (binddt_app_r T G1).
      reflexivity.
    Qed.

    (** *** <<bindt>> on the left *)
    (******************************************************************************)
    (* composition_34 *)
    (* TODO bindt_mapd *)

    (* composition_32 *)
    (* TODO bindt_map *)

    (* composition_31 *)
    Lemma bindt_bind : forall (g : B -> G2 (T C)) (f : A -> T B),
        bindt T T G2 B C g ∘ bind T T A B f = bindt T T G2 A C (bindt T T G2 B C g ∘ f).
    Proof.
      intros.
      rewrite (bind_to_bindt).
      change (bindt T T ?X ?B ?C g) with (map (fun A => A) _ _ (bindt T T X B C g)).
      rewrite (bindt_bindt (fun A => A) G2).
      rewrite (bindt_to_binddt).
      rewrite (binddt_app_l T G2).
      reflexivity.
    Qed.

    (* composition_30 *)
    Lemma bindt_map : forall `(g : B -> G2 (T C)) `(f : A -> B),
        bindt T T G2 B C g ∘ map T A B f = bindt T T G2 A C (g ∘ f).
    Proof.
      intros.
      rewrite (map_to_bindt).
      change (bindt T T ?X ?B ?C g) with (map (fun A => A) _ _ (bindt T T X B C g)).
      rewrite (bindt_bindt (fun A => A) G2).
      rewrite (bindt_to_binddt).
      rewrite (binddt_app_l T G2).
      rewrite (kc3_30 W T).
      reflexivity.
    Qed.

    (** *** <<traverse>> on the right *)
    (******************************************************************************)
    (* composition_42 *)
    (* TODO mapd_traverse *)

    (* composition_22 *)
    Lemma traverse_traverse : forall `(g : B -> G2 C) `(f : A -> G1 B),
        map G1 _ _ (traverse T G2 B C g) ∘ traverse T G1 A B f =
          traverse T (G1 ∘ G2) _ _ (map G1 _ _ g ∘ f).
    Proof.
      intros.
      do 3 rewrite traverse_to_binddt.
      rewrite (kdtm_binddt2 W T G1 G2).
      rewrite (kc7_22 W T).
      reflexivity.
    Qed.

    (* composition_12 *)
    (* TODO bind_traverse *)

    (* composition_02 *)
    (* TODO map_traverse *)

    (** *** <<traverse>> on the left *)
    (******************************************************************************)
    (* composition_24 *)
    (* TODO traverse_mapd *)

    (* composition_21 *)
    (* TODO traverse_bind *)

    (* composition_20 *)
    (* TODO traverse_map *)

    (** *** <<mapd>> on the right *)
    (******************************************************************************)
    (* composition_44 *)
    Lemma mapd_mapd : forall (g : W * B -> C) (f : W * A -> B),
        mapd W T B C g ∘ mapd W T A B f = mapd W T A C (g ∘ cobind (W ×) A B f).
    Proof.
      intros.
      do 3 rewrite (mapd_to_binddt).
      change (binddt W T T ?X ?B ?C ?g) with (map (fun A => A) _ _ (binddt W T T X B C g)) at 1.
      rewrite (kdtm_binddt2 W T (fun A => A) (fun A => A)).
      rewrite (binddt_app_l T (fun A => A)).
      rewrite (kc7_44 W T).
      reflexivity.
    Qed.

    (* composition_14 *)
    (* TODO bind_mapd *)

    (* composition_24 *)
    (* TODO traverse_mapd *)

    (* composition_04 *)
    (* TODO map_mapd *)

    (** *** <<mapd>> on the left *)
    (******************************************************************************)
    (* composition_42 *)
    (* TODO mapd_traverse *)

    (* composition_41 *)
    (* TODO mapd_bind *)

    (* composition_40 *)
    (* TODO mapd_map *)

    (** *** <<bind>> on right *)
    (******************************************************************************)
    (* composition_11 *)
    Lemma bind_bind : forall (g : B -> T C) (f : A -> T B),
        bind T T B C g ∘ bind T T A B f = bind T T A C (g ⋆1 f).
    Proof.
      intros.
      do 3 rewrite (bind_to_binddt).
      change (binddt W T T ?X ?B ?C ?g) with (map (fun A => A) _ _ (binddt W T T X B C g)) at 1.
      rewrite (kdtm_binddt2 W T (fun A => A) (fun A => A)).
      rewrite (binddt_app_l T (fun A => A)).
      rewrite (kc7_11).
      reflexivity.
    Qed.

    (** *** <<map>> *)
    (******************************************************************************)
    (* composition_00 *)
    Lemma map_map : forall (f : A -> B) (g : B -> C),
        map T B C g ∘ map T A B f = map T A C (g ∘ f).
    Proof.
      intros.
      do 3 rewrite (map_to_binddt).
      change (binddt W T T ?I B C ?g) with (map (fun A => A) _ _ (binddt W T T I B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) (fun A => A)).
      rewrite (binddt_app_l T (fun A => A)).
      rewrite (kc7_00 W T).
      reflexivity.
    Qed.

  End composition_special_cases_bottom.

  (** ** Identity laws *)
  (******************************************************************************)
  Lemma bindd_id : forall A : Type,
      bindd W T T A A (ret T A ∘ extract (prod W) A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma bindt_id : forall A : Type,
      bindt T T (fun A : Type => A) A A (ret T A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma mapdt_id : forall A : Type,
      mapdt W T (fun A => A) A A (extract (W ×) A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma mapd_id : forall A : Type,
      mapd W T A A (extract (W ×) A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma traverse_id : forall A : Type,
      traverse T (fun A => A) A A (@id A) = id.
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma bind_id : forall A : Type,
      bind T T A A (ret T A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma map_id : forall A : Type,
      map T A A (@id A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  (** ** Composition with <<ret>> *)
  (******************************************************************************)
  Lemma bindd_ret :
     forall (A B : Type) (f : W * A -> T B),
      bindd W T T A B f ∘ ret T A = f ∘ ret (prod W) A.
  Proof.
    intros.
    rewrite (bindd_to_binddt).
    rewrite (kdtm_binddt0 W T (fun A => A)).
    reflexivity.
  Qed.

  Lemma bindt_ret :
    forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt T T G A B f ∘ ret T A = f.
  Proof.
    intros.
    rewrite (bindt_to_binddt).
    rewrite (kdtm_binddt0 W T G).
    reflexivity.
  Qed.

  Lemma bind_ret :
    forall (A B : Type) (f : A -> T B),
      bind T T A B f ∘ ret T A = f.
  Proof.
    intros.
    rewrite (bind_to_binddt).
    rewrite (kdtm_binddt0 W T (fun A => A)).
    reflexivity.
  Qed.

  (** ** Interaction with applicative morphisms *)
  (******************************************************************************)
  Section applicative_morphisms.

    Context
      (G1 G2 : Type -> Type)
      `{Map G1} `{Pure G1} `{Mult G1}
      `{Map G2} `{Pure G2} `{Mult G2}
      (ϕ : forall A : Type, G1 A -> G2 A)
      `{Hmorph : ! ApplicativeMorphism G1 G2 ϕ}.

    Lemma bindt_morph:
      forall (A B : Type) (f : A -> G1 (T B)),
        ϕ (T B) ∘ bindt T T G1 A B f = bindt T T G2 A B (ϕ (T B) ∘ f).
    Proof.
      intros.
      rewrite (bindt_to_binddt).
      rewrite (kdtm_morph W T G1 G2).
      reflexivity.
    Qed.

    Lemma mapdt_morph:
      forall (A B : Type) (f : W * A -> G1 B),
        mapdt W T G2 A B (ϕ B ∘ f) = ϕ (T B) ∘ mapdt W T G1 A B f.
    Proof.
      intros.
      rewrite (mapdt_to_binddt W T (G := G1)) at 1.
      rewrite (kdtm_morph W T G1 G2).
      reassociate <-.
      rewrite (mapdt_to_binddt W T).
      fequal. inversion Hmorph. ext a.
      unfold compose. rewrite appmor_natural.
      reflexivity.
    Qed.

    Lemma traverse_morph:
      forall (A B : Type) (f : A -> G1 B),
        ϕ (T B) ∘ traverse T G1 A B f = traverse T G2 A B (ϕ B ∘ f).
    Proof.
      intros.
      rewrite (traverse_to_bindt).
      rewrite (bindt_morph).
      reassociate <-.
      rewrite (traverse_to_bindt W T).
      fequal. inversion Hmorph. ext a.
      unfold compose. rewrite appmor_natural.
      reflexivity.
    Qed.

  End applicative_morphisms.

  (** ** Derived typeclass instances *)
  (******************************************************************************)
  #[export] Instance KDM_KDTM: DecoratedMonad T :=
    {| kmond_bindd0 := bindd_ret;
      kmond_bindd1 := bindd_id;
      kmond_bindd2 := @bindd_bindd;
    |}.

  #[export] Instance KTM_KDTM: TraversableMonad T :=
    {| ktm_bindt0 := bindt_ret;
      ktm_bindt1 := bindt_id;
      ktm_bindt2 := @bindt_bindt;
      ktm_morph := bindt_morph;
    |}.

  #[export] Instance KDT_KDTM: DecoratedTraversableFunctor W T :=
    {| kdtfun_mapdt1 := mapdt_id;
      kdtfun_mapdt2 := @mapdt_mapdt;
      kdtfun_morph := mapdt_morph;
    |}.

  #[export] Instance KD_KDTM: DecoratedFunctor W T :=
    {| dfun_mapd1 := mapd_id;
      dfun_mapd2 := @mapd_mapd;
    |}.

  #[export] Instance KT_KDTM: TraversableFunctor T :=
    {| trf_traverse_id := traverse_id;
      trf_traverse_traverse := @traverse_traverse;
      trf_traverse_morphism := traverse_morph;
    |}.

  #[export] Instance KM_KDTM : Monad T :=
    {| kmon_bind0 := bind_ret;
      kmon_bind1 := bind_id;
      kmon_bind2 := @bind_bind;
    |}.

  #[export] Instance: Classes.Functor.Functor T :=
    {| fun_map_id := map_id;
      fun_map_map := @map_map;
    |}.

  End assume_dtm.

End DerivedInstances.

Module Notations.
  Infix "⋆7" := (kc7 _ _ _ _) (at level 60) : tealeaves_scope.
End Notations.
