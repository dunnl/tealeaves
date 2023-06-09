From Tealeaves Require Import
  Classes.Kleisli
  Functors.Writer.

Import Product.Notations.
Import Monoid.Notations.
Import Kleisli.Notations.

#[local] Generalizable Variables G A B C.

Arguments incr {W}%type_scope {op} {A}%type_scope _ _.
Arguments preincr {W}%type_scope {op} {A B}%type_scope f%function_scope w _.

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
    `{! DTM W T}
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    `{Applicative G3}
    {A B C D : Type}.

  Lemma kc7_id1 : forall (f : W * A -> G (T B)),
      kc7 W T G (fun A => A) (ret T B ∘ extract (W ×) B) f = f.
  Proof.
    intros. unfold kc7.
    ext [w a].
    rewrite (preincr_assoc).
    rewrite (extract_preincr W).
    rewrite (kdtm_binddt1 W T).
    rewrite (fun_map_id G).
    reflexivity.
  Qed.

  Lemma kc7_id2 : forall (g : W * A -> G (T B)),
      kc7 W T  (fun A => A) G g (ret T A ∘ extract (W ×) A) = g.
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
    rewrite (fun_map_map G1).
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

  (** ** Operations *)
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

  (** ** Rewrite rules for derived operations *)
  (******************************************************************************)
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

    Lemma mapt_to_binddt `(f : A -> G B):
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

    Lemma mapt_to_bindt `(f : A -> G B):
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

    Lemma mapt_to_mapdt `(f : A -> G B):
      traverse T G A B f = mapdt W T G A B (f ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mapt>> *)
    (******************************************************************************)
    Lemma map_to_mapt `(f : A -> B):
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
      `{Monoid_op W} `{Monoid_unit W}
      `{Return T}
      `{Binddt W T T}
      `{Applicative G1}
      `{Applicative G2}
      `{! DTM W T}
      {A B C D : Type}.

    (*
    d/t/m:
    000 0 no d or t or m
    001 1 monad
    010 2 traversable functor
    011 3 traversable monad
    100 4 decorated functor
    101 5 decorated monad
    110 6 decorated traversable functor
    111 7 decorated traversable monad
     *)

    Theorem kc7_73 :
      forall (g : B -> G2 (T C)) (f : W * A -> G1 (T B)),
        (g ∘ extract (W ×) B) ⋆7 f = g ⋆3 f.
    Proof.
      intros. unfold kc7.
      ext [w a].
      rewrite (preincr_assoc).
      rewrite (extract_preincr).
      reflexivity.
    Qed.

    Lemma kc7_33 :
      forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        kc7 W T G1 G2 (g ∘ extract (W ×) B) (f ∘ extract (W ×) A) =
          (kc3 T G1 G2 g f) ∘ extract (W ×) A.
    Proof.
      intros. unfold kc7.
      ext [w a]. rewrite preincr_assoc.
      rewrite extract_preincr.
      reflexivity.
    Qed.

    Theorem kc7_75 :
      forall (g : W * B -> T C) (f : W * A -> G1 (T B)),
        kc7 W T G1 (fun A => A) g f = g ⋆7 f.
    Proof.
      reflexivity.
    Qed.

    Theorem kc7_67 :
      forall (g : W * B -> G2 C) (f : W * A -> G1 (T B)),
        (map G2 C (T C) (ret T C) ∘ g) ⋆7 f = (map G2 C (T C) (ret T C) ∘ g) ⋆7 f.
    Proof.
      reflexivity.
    Qed.

    (** Composition when neither <<g>> or <<f>> perform a substitution *)
    Lemma kc7_66 :
        forall (g : W * B -> G2 C) (f : W * A -> G1 B),
        (map G2 C (T C) (ret T C) ∘ g) ⋆7 (map G1 B (T B) (ret T B) ∘ f) =
          map (G1 ∘ G2) C (T C) (ret T C) ∘ (g ⋆6 f).
    Proof.
      intros. unfold kc7.
      ext [w a]. unfold compose at 2.
      compose near (f (w, a)).
      rewrite (fun_map_map G1).
      rewrite (kdtm_binddt0 W T G2 B C).
      rewrite preincr_ret.
      unfold kcompose_dt. unfold_ops @Map_compose.
      do 2 reassociate <-.
      unfold_compose_in_compose.
      rewrite (fun_map_map G1).
      unfold strength.
      unfold compose; cbn.
      compose near (f (w, a)) on right.
      rewrite (fun_map_map G1).
      reflexivity.
    Qed.




  End kc7_special_cases.



























































  Section laws.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Kleisli.DTM W T}.

    Lemma map_id : forall (A : Type),
        map T A A (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Map_Binddt.
      change (ret T A ∘ id) with (ret T A).
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
        map T g ∘ map T f = map T (g ∘ f).
    Proof.
      intros. unfold_ops @Map_Binddt.
      change (binddt T (fun A0 : Type => A0) (ret T ∘ g ∘ extract (prod W)))
        with (map (fun A => A) (binddt T (fun A0 : Type => A0) (ret T ∘ g ∘ extract (prod W)))).
      rewrite (kdtm_binddt2 W T _ _ _ (G1 := fun A => A) (G2 := fun A => A)).
      fequal.
      - now rewrite Mult_compose_identity1.
      - unfold kc7. ext [w a].
        unfold_ops @Map_I.
        compose near (w, a) on left.
        do 2 reassociate <- on left.
        unfold_compose_in_compose.
        rewrite (kdtm_binddt0 W T _ _ (G := fun A => A)).
        unfold_ops @Return_writer @Monoid_unit_product.
        unfold compose; cbn.
        reflexivity.
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_map_id := map_id;
        fun_map_map := map_map;
      |}.

    Lemma map_binddt: forall (G1 : Type -> Type) (A B C : Type) `{Applicative G1}
                         (g : B -> C)
                         (f : W * A -> G1 (T B)),
        map G1 (map T g) ∘ binddt T G1 f =
          binddt T G1 (map G1 (map T g) ∘ f).
    Proof.
      intros. unfold_ops @Map_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := fun A => A)).
      fequal.
      - now rewrite Mult_compose_identity1.
      - ext [w a]. cbn. now rewrite Decorated.Monad.preincr_extract.
    Qed.


    Lemma binddt_map: forall (G2 : Type -> Type) (A B C : Type) `{Applicative G2}
                         (g : W * B -> G2 (T C))
                         (f : A -> B),
        binddt T G2 g ∘ map T f =
          binddt T G2 (fun '(w, a) => g (w, f a)).
    Proof.
      intros. unfold_ops @Map_Binddt.
      change (binddt T G2 g) with (map (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      unfold kc7. ext [w a].
      change (map (fun A => A) ?f) with f.
      unfold compose; cbn.
      compose near (f a) on left.
      rewrite (kdtm_binddt0 W T _ _ _ (G := G2)).
      cbv. change (op w unit0) with (w ● Ƶ).
      now simpl_monoid.
    Qed.

  End with_monad.


  End special_cases.

  Import Kleisli.Traversable.Monad.Notations.
  Import Kleisli.DT.Functor.Notations.
  Import Kleisli.Decorated.Monad.Notations.
  Import Kleisli.Monad.Notations.
  Import Comonad.Notations.

  (** ** Special cases of Kleisli composition *)
  (******************************************************************************)
  Section kleisli_composition.

    Context
      (W : Type)
      (T : Type -> Type)
      `{DT.Monad.Monad W T}.

    (*
    d/t/m:
    000 0 no d or t or m
    001 1 no context or effect
    010 2 no context or subst
    011 3 no context
    100 4 no effect or subst
    101 5 no effect
    110 6 no subst
    111 7 everything
     *)


    (** *** Composition when <<g>> has no substitution *)
    (******************************************************************************)


    (** *** Composition when <<g>> has no applicative effect *)
    (******************************************************************************)

    (** Composition when neither <<g>> or <<f>> has an applicative effect *)
    Lemma kc7_55 : forall
        `(g : W * B -> T C) `(f : W * A -> T B),
        kc7 (G1 := fun A => A) (G2 := fun A => A) g f =
          kcompose_dm g f.
    Proof.
      reflexivity.
    Qed.

    (** Composition when neither <<g>> or <<f>> has an applicative effect or substitution *)
    Lemma kc7_44 : forall
        `(g : W * B -> C) `(f : W * A -> B),
        kc7 (G1 := fun A => A) (G2 := fun A => A)
          (ret T ∘ g) (ret T ∘ f) = ret T ∘ (g co⋆ f).
    Proof.
      intros. rewrite kc7_55.
      unfold kcompose_dm.
      ext [w a].
      intros. unfold_ops @Bindd_Binddt.
      unfold compose. compose near (f (w, a)).
      rewrite (kdtm_binddt0 W T _ _ (G := fun A => A)).
      cbv. change (op w unit0) with (w ● Ƶ). now simpl_monoid.
    Qed.


    (** *** Composition when <<f>> has no applicative effect *)
    (******************************************************************************)

    (** Composition when <<f>> has no applicative effect *)
    Theorem dtm_kleisli_75 {A B C} : forall
        `{Applicative G2}
        (g : W * B -> G2 (T C)) (f : W * A -> T B),
        kc7 (G1 := fun A => A) g f = fun '(w, a) => binddt T G2 (preincr w g) (f (w, a)).
    Proof.
      reflexivity.
    Qed.

    (** Composition when <<f>> has no applicative effect, substitution, or context-sensitivity *)
    Lemma kc7_70 : forall
        `{Applicative G}
        `(g : W * B -> G (T C)) `(f : A -> B),
        kc7 (G1 := fun A => A) (G2 := G)
          g (ret T ∘ f ∘ extract (W ×)) = g ∘ map (W ×) f.
    Proof.
      intros. unfold kc7.
      ext [w a]. unfold compose.
      cbn. compose near (f a) on left.
      change (map (fun A => A) ?f) with f.
      rewrite (kdtm_binddt0 W T _ _ (G := G)).
      now rewrite preincr_ret.
    Qed.

    (** Composition when <<f>> is just a map *)
    Theorem dtm_kleisli_70 {A B C} : forall
        `{Applicative G2}
        (g : W * B -> G2 (T C)) (f : A -> B),
        kc7 (G1 := fun A => A) (G2 := G2) g
          (ret T ∘ f ∘ extract (W ×)) = g ∘ map (W ×) f.
    Proof.
      intros. unfold kc7.
      ext [w a]. unfold compose. cbn.
      compose near (f a) on left.
      change (map (fun A => A) ?f) with f.
      rewrite (kdtm_binddt0 W T); auto.
      now rewrite (preincr_ret).
    Qed.

    (** Composition when <<f>> has no applicative effect or substitution *)
    Lemma kc7_74 : forall
        `{Applicative G}
        `(g : W * B -> G (T C)) `(f : W * A -> B),
        kc7 (G1 := fun A => A) (G2 := G)
          g (ret T ∘ f) = g co⋆ f.
    Proof.
      intros. unfold kc7.
      ext [w a]. unfold compose.
      compose near (f (w, a)).
      change (map (fun A => A) ?f) with f.
      rewrite (kdtm_binddt0 W T _ _ (G := G)).
      now rewrite preincr_ret.
    Qed.

    (** *** Others *)
    (******************************************************************************)

    (** Composition when <<f>> is context-agnostic *)
    Theorem dtm_kleisli_73 {A B C} : forall
        `{Applicative G1} `{Applicative G2}
        (g : W * B -> G2 (T C)) (f : A -> G1 (T B)),
        g ⋆7 (f ∘ extract (W ×)) =
          ((fun '(w, t) => map G1 (binddt T G2 (preincr w g)) t) ∘ map (W ×) f).
    Proof.
      intros. unfold kc7.
      ext [w a]. unfold compose. cbn.
      reflexivity.
    Qed.
    (** Composition when <<f>> has no substitution *)
    Theorem dtm_kleisli_76 {A B C} : forall
        `{Applicative G1} `{Applicative G2}
        (g : W * B -> G2 (T C)) (f : W * A -> G1 B),
        g ⋆7 (map G1 (ret T) ∘ f) = g ⋆dt f.
    Proof.
      intros. unfold kc7.
      ext [w a]. unfold kcompose_dt.
      unfold compose. cbn.
      compose near (f (w, a)).
      rewrite (fun_map_map G1).
      rewrite (fun_map_map G1).
      fequal.
      rewrite (kdtm_binddt0 W T); auto.
      now rewrite (preincr_ret).
    Qed.

  End kleisli_composition.

  (** * Lesser Kleisli typeclass instances *)
  (******************************************************************************)
  Section instances.

    Context
      (W : Type)
        (T : Type -> Type)
        `{Kleisli.DT.Monad.Monad W T}.

    (** ** Monad *)
    (******************************************************************************)
    Lemma kmon_bind0_T : forall (A B : Type) (f : A -> T B),
        bind T f ∘ ret T = f.
    Proof.
      intros. unfold_ops @Bind_Binddt.
      rewrite (kdtm_binddt0 W T _ _ _ (G := fun A => A)).
      reflexivity.
    Qed.

    Lemma kmon_bind1_T : forall A : Type,
        bind T (ret T) = @id (T A).
    Proof.
      intros. unfold_ops @Bind_Binddt.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma kmon_bind2_T : forall (B C : Type) (g : B -> T C) (A : Type) (f : A -> T B),
        bind T g ∘ bind T f = bind T (g ⋆ f).
    Proof.
      intros. unfold_ops @Bind_Binddt.
      change (binddt T (fun A0 : Type => A0) (g ∘ extract (prod W)))
        with (map (fun A => A)
                (binddt T (fun A0 : Type => A0) (g ∘ extract (prod W)))).
      rewrite (kdtm_binddt2 W T _ _ _ (G1 := fun A => A) (G2 := fun A => A)).
      fequal.
      - now rewrite Mult_compose_identity1.
      - change_left ((g ∘ extract (prod W)) ⋆dm (f ∘ extract (W ×))).
        unfold kcompose_dm. ext [w a]. unfold compose at 2. cbn.
        rewrite preincr_extract.
        reflexivity.
    Qed.

    #[export] Instance KM_KDTM : Kleisli.Monad.Monad T :=
      {| kmon_bind0 := kmon_bind0_T;
        kmon_bind1 := kmon_bind1_T;
        kmon_bind2 := kmon_bind2_T;
      |}.

    (** ** Decorated monad *)
    (******************************************************************************)
    Lemma kmond_bindd0_T : forall (A B : Type) (f : W * A -> T B),
        bindd T f ∘ ret T = f ∘ ret (prod W).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      now rewrite (kdtm_binddt0 W T _ _ _ (G := fun A => A)).
    Qed.

    Lemma kmond_bindd1_T : forall A : Type,
        bindd T (ret T ∘ extract (prod W)) = @id (T A).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma kmond_bindd2_T : forall (B C : Type) (g : W * B -> T C) (A : Type) (f : W * A -> T B),
        bindd T g ∘ bindd T f = bindd T (g ⋆dm f).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      change (binddt T ?I g) with (map (fun A => A) (binddt T I g)).
      rewrite (kdtm_binddt2 W T _ _ _ (G1 := fun A => A) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    #[export] Instance KDM_KDTM: Kleisli.Decorated.Monad.Monad T :=
      {| kmond_bindd0 := kmond_bindd0_T;
        kmond_bindd1 := kmond_bindd1_T;
        kmond_bindd2 := kmond_bindd2_T;
      |}.

    (** ** Traversable monad *)
    (******************************************************************************)
    Lemma ktm_bindt0_T : forall
        (A B : Type) (G : Type -> Type) (H1 : Map G)
        (H2 : Pure G) (H3 : Mult G),
        Applicative G ->
        forall f : A -> G (T B), bindt T G f ∘ ret T = f.
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (kdtm_binddt0 W T); auto.
    Qed.

    Lemma ktm_bindt1_T : forall A : Type,
        bindt T (fun A : Type => A) (ret T) = @id (T A).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma ktm_bindt2_T : forall
        (A B C : Type) (G1 : Type -> Type) (H1 : Map G1)
        (H2 : Pure G1) (H3 : Mult G1),
        Applicative G1 ->
        forall (G2 : Type -> Type) (H5 : Map G2) (H6 : Pure G2) (H7 : Mult G2),
          Applicative G2 ->
          forall (g : B -> G2 (T C)) (f : A -> G1 (T B)),
            map G1 (bindt T G2 g) ∘ bindt T G1 f = bindt T (G1 ∘ G2) (g ⋆tm f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (kdtm_binddt2 W T); auto.
      fequal. rewrite (kc7_33 W T).
      reflexivity.
    Qed.

    Lemma ktm_morph_T : forall
        (G1 G2 : Type -> Type) (H1 : Map G1) (H2 : Pure G1) (H3 : Mult G1) (H4 : Map G2)
        (H5 : Pure G2) (H6 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : A -> G1 (T B)),
          ϕ (T B) ∘ bindt T G1 f = bindt T G2 (ϕ (T B) ∘ f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      now rewrite (kdtm_morph W T G1 G2).
    Qed.

    #[export] Instance KTM_KDTM: Traversable.Monad.Monad T :=
      {| ktm_bindt0 := ktm_bindt0_T;
        ktm_bindt1 := ktm_bindt1_T;
        ktm_bindt2 := ktm_bindt2_T;
        ktm_morph := ktm_morph_T;
      |}.

    (** ** Decorated-traversable functor *)
    (******************************************************************************)
    Lemma kdtfun_mapdt1_T : forall A : Type,
        mapdt T (fun A0 : Type => A0) (extract (W ×)) = @id (T A).
    Proof.
      intros. unfold_ops @Mapdt_Binddt.
      change (map (fun A => A) ?f) with f.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma kdtfun_mapdt2_T :
      forall (G1 : Type -> Type) (H0 : Map G1) (H1 : Pure G1) (H2 : Mult G1) (H3 : Applicative G1)
        (G2 : Type -> Type) (H4 : Map G2) (H5 : Pure G2) (H6 : Mult G2) (H7 : Applicative G2)
        (B C : Type) (g : W * B -> G2 C) (A : Type) (f : W * A -> G1 B),
        map G1 (mapdt T G2 g) ∘ mapdt T G1 f = mapdt T (G1 ∘ G2) (g ⋆dt f).
    Proof.
      intros. unfold_ops @Mapdt_Binddt.
      rewrite (kdtm_binddt2 W T); auto.
      fequal. now rewrite (kc7_66 W T).
    Qed.

    Lemma kdtfun_morph_T :
      forall (G1 G2 : Type -> Type) (H0 : Map G1) (H1 : Pure G1) (H2 : Mult G1)
        (H3 : Map G2) (H4 : Pure G2) (H5 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : W * A -> G1 B), mapdt T G2 (ϕ B ∘ f) = ϕ (T B) ∘ mapdt T G1 f.
    Proof.
      intros. unfold_ops @Mapdt_Binddt.
      rewrite (kdtm_morph W T _ _ (ϕ := ϕ)).
      fequal. reassociate <-.
      unfold compose. ext [w a]. now rewrite (appmor_natural G1 G2).
    Qed.

    #[export] Instance KDT_KDTM: DT.Functor.DecoratedTraversableFunctor W T :=
      {| kdtfun_mapdt1 := kdtfun_mapdt1_T;
        kdtfun_mapdt2 := kdtfun_mapdt2_T;
        kdtfun_morph := kdtfun_morph_T;
      |}.

    (** ** Decorated functor *)
    (******************************************************************************)
    Lemma dfun_mapd1_T : forall A : Type,
        mapd T (extract (W ×)) = @id (T A).
    Proof.
      intros. unfold_ops @Mapd_Binddt.
      now rewrite (kdtm_binddt1 W T).
    Qed.

    Lemma dfun_mapd2_T : forall (A B C : Type) (g : W * B -> C) (f : W * A -> B),
        mapd T g ∘ mapd T f = mapd T (g ∘ cobind (W ×) f).
    Proof.
      intros. unfold_ops @Mapd_Binddt.
      change (binddt T (fun A0 : Type => A0) ?g) with
        (map (fun A => A) (binddt T (fun A0 : Type => A0) g)) at 1.
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      now rewrite (kc7_44 W T).
    Qed.

    #[export] Instance KD_KDTM: Kleisli.Decorated.Functor.DecoratedFunctor W T :=
      {| dfun_mapd1 := dfun_mapd1_T;
        dfun_mapd2 := dfun_mapd2_T;
      |}.

    (** ** Traversable functor *)
    (******************************************************************************)
    Lemma trf_traverse_id_T : forall A : Type,
        traverse T (fun A0 : Type => A0) (@id A) = id.
    Proof.
      unfold_ops @Traverse_Binddt @Map_I.
      apply (kdtm_binddt1 W T).
    Qed.

    Lemma trf_traverse_traverse_T : forall (G1 G2 : Type -> Type) (H0 : Map G2) (H1 : Pure G2) (H2 : Mult G2),
        Applicative G2 ->
        forall (H4 : Map G1) (H5 : Pure G1) (H6 : Mult G1),
          Applicative G1 ->
          forall (B C : Type) (g : B -> G2 C) (A : Type) (f : A -> G1 B),
            map G1 (traverse T G2 g) ∘ traverse T G1 f =
              traverse T (G1 ∘ G2) (map G1 g ∘ f).
    Proof.
      intros. unfold_ops @Traverse_Binddt.
      rewrite (kdtm_binddt2 W T); auto.
      rewrite (kc7_33 W T).
      rewrite (kcompose_tm_ret T).
      reflexivity.
    Qed.

    Lemma trf_traverse_morphism_T : forall (G1 G2 : Type -> Type) (H0 : Map G1) (H1 : Pure G1)
                                      (H2 : Mult G1) (H3 : Map G2) (H4 : Pure G2)
                                      (H5 : Mult G2) (ϕ : forall A : Type, G1 A -> G2 A),
        ApplicativeMorphism G1 G2 ϕ ->
        forall (A B : Type) (f : A -> G1 B),
          ϕ (T B) ∘ traverse T G1 f = traverse T G2 (ϕ B ∘ f).
    Proof.
      intros. unfold_ops @Traverse_Binddt.
      rewrite (kdtm_morph W T G1 G2).
      do 2 reassociate <- on left.
      fequal. unfold compose; ext x.
      inversion H8.
      rewrite appmor_natural.
      reflexivity.
    Qed.

    #[export] Instance KT_KDTM: Traversable.Functor.TraversableFunctor T :=
      {| trf_traverse_id := trf_traverse_id_T;
        trf_traverse_traverse := trf_traverse_traverse_T;
        trf_traverse_morphism := trf_traverse_morphism_T;
      |}.

    (** ** Functor *)
    (******************************************************************************)

  End instances.
  Section binddt.

    Context
      (T : Type -> Type)
      (G1 G2 : Type -> Type)
      `{DT.Monad.Monad W T}
      `{Applicative G1}
      `{Applicative G2}
      {A B C : Type}.

    (** ** <<binddt>> on the right *)
    (******************************************************************************)
    Lemma bindd_binddt: forall
        (g : W * B -> T C)
        (f : W * A -> G1 (T B)),
        map G1 (bindd T g) ∘ binddt T G1 f =
          binddt T G1 (fun '(w, a) => map G1 (bindd T (preincr w g)) (f (w, a))).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    Lemma mapdt_binddt: forall
        (g : W * B -> G2 C)
        (f : W * A -> G1 (T B)),
        map G1 (mapdt T G2 g) ∘ binddt T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => map G1 (mapdt T G2 (preincr w g)) (f (w, a))).
    Proof.
      intros. unfold_ops @Mapdt_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := G2)).
      reflexivity.
    Qed.

    Lemma bindt_binddt: forall
        (g : B -> G2 (T C))
        (f : W * A -> G1 (T B)),
        map G1 (bindt T G2 g) ∘ binddt T G1 f =
          binddt T (G1 ∘ G2) (map G1 (bindt T G2 g) ∘ f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := G2)).
      fequal. unfold kc7. ext [w a].
      now rewrite preincr_extract.
    Qed.

    Lemma bind_binddt: forall
        (g : B -> T C)
        (f : W * A -> G1 (T B)),
        map G1 (bind T g) ∘ binddt T G1 f =
          binddt T G1 (map G1 (bind T g) ∘ f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      unfold_ops @Bind_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := fun A => A)).
      fequal.
      - now rewrite Mult_compose_identity1.
      - ext [w a]. cbn. now rewrite (preincr_extract).
    Qed.

    Lemma mapd_binddt: forall
        (g : W * B -> C)
        (f : W * A -> G1 (T B)),
        map G1 (mapd T g) ∘ binddt T G1 f =
          binddt T G1 (fun '(w, a) => map G1 (mapd T (preincr w g)) (f (w, a))).
    Proof.
      intros. unfold_ops @Mapd_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    Lemma mapt_binddt: forall
        (g : B -> G2 C)
        (f : W * A -> G1 (T B)),
        map G1 (traverse T G2 g) ∘ binddt T G1 f =
          binddt T (G1 ∘ G2) (map G1 (traverse T G2 g) ∘ f).
    Proof.
      intros.
      intros. unfold_ops @Traverse_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1) (G2 := G2)).
      fequal. ext [w a]. cbn.
      now rewrite preincr_extract.
    Qed.

    (** ** <<binddt>> on the left *)
    (******************************************************************************)
    Lemma binddt_bindd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> T B),
        binddt T G2 g ∘ bindd T f =
          binddt T G2 (fun '(w, a) => binddt T G2 (preincr w g) (f (w, a))).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      change (binddt T G2 g) with (map (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
    Qed.

    Lemma binddt_mapdt: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> G1 B),
        map G1 (binddt T G2 g) ∘ mapdt T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => map G1 (fun b => g (w, b)) (f (w, a))).
    Proof.
      intros. unfold_ops @Mapdt_Binddt.
      rewrite (kdtm_binddt2 W T A B C).
      fequal. ext [w a]. unfold compose; cbn.
      compose near (f (w, a)) on left.
      rewrite (fun_map_map G1).
      fequal. ext b. unfold compose; cbn.
      compose near b on left.
      rewrite (kdtm_binddt0 W T); auto.
      now rewrite preincr_ret.
    Qed.

    Lemma binddt_bindt: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 (T B)),
        map G1 (binddt T G2 g) ∘ bindt T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => map G1 (binddt T G2 (preincr w g)) (f a)).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      now rewrite (kdtm_binddt2 W T).
    Qed.

    Lemma binddt_bind: forall
        (g : W * B -> G2 (T C))
        (f : A -> T B),
        binddt T G2 g ∘ bind T f =
          binddt T G2 (fun '(w, a) => binddt T G2 (preincr w g) (f a)).
    Proof.
      intros. unfold_ops @Bind_Binddt.
      change (binddt T G2 g) with (map (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
    Qed.

    Lemma binddt_mapd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> B),
        binddt T G2 g ∘ mapd T f =
          binddt T G2 (fun '(w, a) => g (w, f (w, a))).
    Proof.
      intros. unfold_ops @Mapd_Binddt.
      change (binddt T G2 g) with (map (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      rewrite dtm_kleisli_75; auto.
      ext [w a]. unfold compose.
      compose near (f (w, a)).
      rewrite (kdtm_binddt0 W T); auto.
      now rewrite preincr_ret.
    Qed.

    Lemma binddt_mapt: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 B),
        map G1 (binddt T G2 g) ∘ traverse T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => map G1 (fun b => g (w, b)) (f a)).
    Proof.
      intros. unfold_ops @Traverse_Binddt.
      rewrite (kdtm_binddt2 W T A B C (G1 := G1)).
      fequal. unfold kc7.
      ext [w a]. unfold compose. cbn.
      compose near (f a) on left.
      rewrite (fun_map_map G1).
      rewrite (kdtm_binddt0 W T); auto.
      rewrite preincr_ret.
      reflexivity.
    Qed.

    (*
    Lemma binddt_map: forall
        (g : W * B -> G2 (T C))
        (f : A -> B),
        binddt T G2 g ∘ map T f =
          binddt T G2 (g ∘ map (W ×) f).
    Proof.
      intros. unfold_ops @Map_Binddt.
      change (binddt T G2 g) with (map (fun A => A) (binddt T G2 g)).
      rewrite (kdtm_binddt2 W T A B C (G2 := G2) (G1 := fun A => A)).
      fequal. now rewrite Mult_compose_identity2.
      ext [w a]. unfold compose. cbn.
      compose near (f a) on left.
      change (map (fun A => A) ?f) with f.
      rewrite (kdtm_binddt0 W T); auto.
      rewrite preincr_ret.
      reflexivity.
    Qed.
     *)

  End binddt.

  (** ** <<bindd>>, <<mapdt>>, <<bindt>> *)
  (******************************************************************************)
  Section composition_laws.

    Context
      (T : Type -> Type)
        (G1 G2 : Type -> Type)
        `{DT.Monad.Monad W T}
        `{Applicative G1}
        `{Applicative G2}
        {A B C : Type}.

    (* <<bindd_bindd>> is already given. *)
    (* bindt_bindt already given *)
    (* mapdt_mapdt already given *)

    Lemma bindd_mapdt: forall
        (g : W * B -> T C)
        (f : W * A -> G1 B),
        map G1 (bindd T g) ∘ mapdt T G1 f =
          binddt T G1 (fun '(w, a) => map G1 (g ∘ pair w) (f (w, a))).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      rewrite (binddt_mapdt T G1 (fun A => A)).
      fequal. now rewrite Mult_compose_identity1.
    Qed.

    Lemma mapdt_bindd: forall
        (g : W * B -> G2 C)
        (f : W * A -> T B),
        mapdt T G2 g ∘ bindd T f =
          binddt T G2 (fun '(w, a) => mapdt T G2 (preincr w g) (f (w, a))).
    Proof.
      intros. unfold_ops @Bindd_Binddt.
      change (mapdt T G2 g) with (map (fun A => A) (mapdt T G2 g)).
      rewrite (mapdt_binddt T (fun A => A) G2).
      fequal. now rewrite Mult_compose_identity2.
    Qed.

    Lemma bindt_bindd: forall
        (g : B -> G2 (T C))
        (f : W * A -> T B),
        bindt T G2 g ∘ bindd T f =
          binddt T G2 (bindt T G2 g ∘ f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (binddt_bindd T G2).
      fequal. ext [w a].
      now rewrite (preincr_extract).
    Qed.

    Lemma bindd_bindt: forall
        (g : W * B -> T C)
        (f : A -> G1 (T B)),
        map G1 (bindd T g) ∘ bindt T G1 f =
          binddt T G1 (fun '(w, a) => map G1 (bindd T (preincr w g)) (f a)).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (bindd_binddt T G1).
      reflexivity.
    Qed.

    Lemma mapdt_bindt: forall
        (g : W * B -> G2 C)
        (f : A -> G1 (T B)),
        map G1 (mapdt T G2 g) ∘ bindt T G1 f =
          binddt T (G1 ∘ G2) (fun '(w, a) => map G1 (mapdt T G2 (preincr w g)) (f a)).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (mapdt_binddt T G1 G2).
      reflexivity.
    Qed.

    Lemma bindt_mapdt: forall
        (g : B -> G2 (T C))
        (f : W * A -> G1 B),
        map G1 (bindt T G2 g) ∘ mapdt T G1 f =
          binddt T (G1 ∘ G2) (map G1 g ∘ f).
    Proof.
      intros. unfold_ops @Bindt_Binddt.
      rewrite (binddt_mapdt T G1 G2).
      fequal. now ext [w a].
    Qed.

    (** ** <<bindd>> on the right *)
    (******************************************************************************)
    Lemma bind_bindd: forall
        (g : B -> T C)
        (f : W * A -> T B),
        bind T g ∘ bindd T f =
          bindd T (bind T g ∘ f).
    Proof.
      intros. rewrite (bind_to_bindd W T).
      rewrite (kmond_bindd2 T).
      fequal. unfold kcompose_dm.
      ext [w a]. now rewrite (preincr_extract).
    Qed.

    Lemma mapd_bindd: forall
        (g : W * B -> C)
        (f : W * A -> T B),
        mapd T g ∘ bindd T f =
          bindd T (fun '(w, a) => mapd T (preincr w g) (f (w, a))).
    Proof.
      intros. rewrite (mapd_to_bindd W T).
      rewrite (kmond_bindd2 T).
      reflexivity.
    Qed.

    (* traverse_bindd *)
    (* map_bindd *)

    (** ** <<bindd>> on the left *)
    (******************************************************************************)
    Lemma bindd_bind: forall
        (g : W * B -> T C)
        (f : A -> T B),
        bindd T g ∘ bind T f =
          bindd T (fun '(w, a) => bindd T (preincr w g) (f a)).
    Proof.
      intros. rewrite (bind_to_bindd W T).
      rewrite (kmond_bindd2 T).
      reflexivity.
    Qed.

    Lemma bindd_mapd: forall
        (g : W * B -> T C)
        (f : W * A -> B),
        bindd T g ∘ mapd T f =
          bindd T (g co⋆ f).
    Proof.
      intros. rewrite (mapd_to_bindd W T).
      rewrite (kmond_bindd2 T).
      fequal. ext [w a]. unfold kcompose_dm, compose.
      compose near (f (w, a)).
      rewrite (kmond_bindd0 T).
      now rewrite preincr_ret.
    Qed.

    (* bindd_traverse *)
    (* bindd_map *)

    (** ** <<mapdt>> on the right *)
    (******************************************************************************)
    (* bind_mapdt *)

    Lemma mapd_mapdt : forall (g : W * B -> C) (f : W * A -> G1 B),
        map G1 (mapd T g) ∘ mapdt T G1 f = mapdt T G1 (map G1 g ∘ strength G1 ∘ cobind (W ×) f).
    Proof.
      introv.
      change (@Mapd_Binddt T W _ _) with (@DT.Functor.Derived.Mapd_Mapdt T W _).
      rewrite (DT.Functor.Derived.mapd_mapdt T G1).
      reflexivity.
    Qed.

    (* traverse_mapdt *)

    (* map_mapdt *)

    (** ** <<mapdt>> on the left *)
    (******************************************************************************)
    (* mapdt_bind *)
    Lemma mapdt_mapd : forall (g : W * B -> G2 C) (f : W * A -> B),
        mapdt T G2 g ∘ mapd T f = mapdt T G2 (g co⋆ f).
    Proof.
      introv.
      change (@Mapd_Binddt T W _ _) with (@DT.Functor.Derived.Mapd_Mapdt T W _).
      rewrite (DT.Functor.Derived.mapdt_mapd T G2).
      reflexivity.
    Qed.

    (* mapdt_traverse *)

    (* mapdt_map *)

    (** ** <<bindt>> on the right *)
    (******************************************************************************)
    Lemma bind_bindt : forall (g : B -> T C) (f : A -> G1 (T B)),
        map G1 (bind T g) ∘ bindt T G1 f = bindt T G1 (map G1 (bind T g) ∘ f).
    Proof.
      introv.
      change (@Bind_Binddt T W _) with (@Derived.Bind_Bindt T _).
      rewrite (Traversable.Monad.Derived.bind_bindt T G1).
      reflexivity.
    Qed.

    Lemma mapd_bindt : forall (g : W * B -> C) (f : A -> G1 (T B)),
        map G1 (mapd T g) ∘ bindt T G1 f = binddt T G1 (fun '(w, a) => map G1 (mapd T (preincr w g)) (f a)).
    Proof.
      introv.
    Abort.

    (* traverse_bindt *)
    Lemma map_bindt : forall (g : B -> C) (f : A -> G1 (T B)),
        map G1 (map T g) ∘ bindt T G1 f = bindt T G1 (map G1 (map T g) ∘ f).
    Proof.
      intros.
      change (@Map_Binddt T W H0 H) with (@Derived.Map_Bindt T _ _).
      rewrite (Traversable.Monad.Derived.map_bindt T G1).
      reflexivity.
    Qed.

    (** ** <<bindt>> on the left *)
    (******************************************************************************)
    Lemma bindt_bind : forall (g : B -> G2 (T C)) (f : A -> T B),
        bindt T G2 g ∘ bind T f = bindt T G2 (bindt T G2 g ∘ f).
    Proof.
      introv.
      change (@Bind_Binddt T W _) with (@Traversable.Monad.Derived.Bind_Bindt T _).
      rewrite (Traversable.Monad.Derived.bindt_bind T G2).
      reflexivity.
    Qed.

    (* bindt_mapd *)
    (* bindt_traverse *)
    (* bindt_map *)
    Lemma bindt_map : forall `(g : B -> G2 (T C)) `(f : A -> B),
        bindt T G2 g ∘ map T f = bindt T G2 (g ∘ f).
    Proof.
      intros.
      change (@Map_Binddt T W H0 H) with (@Derived.Map_Bindt T _ _).
      rewrite (Traversable.Monad.Derived.bindt_map T G2).
      reflexivity.
    Qed.

    (** ** <<traverse>> on the right *)
    (******************************************************************************)
    (* bind_traverse *)
    (* mapd_traverse *)
    (* traverse_traverse *)

    (* map_traverse *)

    (** ** <<traverse>> on the left *)
    (******************************************************************************)
    (* traverse_bind *)
    (* traverse_mapd *)
    (* traverse_traverse *)

    (* traverse_map *)

    (** ** <<mapd>> on the right *)
    (******************************************************************************)
    (* bind_mapd *)
    (* mapd_mapd *)
    (* traverse_mapd *)

    (* map_mapd *)

    (** ** <<mapd>> on the left *)
    (******************************************************************************)
    (* mapd_bind *)
    (* mapd_mapd *)
    (* mapd_traverse *)

    (* mapd_map *)

    (** ** <<bindd>> on the right *)
    (******************************************************************************)
    Lemma map_bindd : forall (g : B -> C) (f : W * A -> T B),
        map T g ∘ bindd T f = bindd T (map T g ∘ f).
    Proof.
      intros.
      Set Printing All.
      change (@Map_Binddt T W H0 H) with (@Derived.Map_Bindd T _ W _).
    (* pose (Decorated.Monad.Derived.map_bindd T).
    reflexivity.
  Qed. *)
    Abort.

    (** ** <<bindd>> on the left *)
    (******************************************************************************)

  End composition_laws.

End Derived.

(** * Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    (T : Type -> Type)
      `{DT.Monad.Monad W T}.

  Import Derived.

  Lemma binddt_constant_applicative1
    `{Monoid M} {B : Type}
    `(f : W * A -> const M (T B)) :
    binddt (B := B) T (const M) f =
      binddt (B := False) T (const M) (f : W * A -> const M (T False)).
  Proof.
    change_right (map (B := T B) (const M) (map T exfalso)
                    ∘ (binddt (B := False) T (const M) (f : W * A -> const M (T False)))).
    rewrite (map_binddt T (const M)).
    - reflexivity.
    - typeclasses eauto.
  Qed.

  Lemma binddt_constant_applicative2 (fake1 fake2 : Type) `{Monoid M}
    `(f : W * A -> const M (T B)) :
    binddt (B := fake1) T (const M)
      (f : W * A -> const M (T fake1))
    = binddt (B := fake2) T (const M)
        (f : W * A -> const M (T fake2)).
  Proof.
    intros. rewrite (binddt_constant_applicative1 (B := fake1)).
    rewrite (binddt_constant_applicative1 (B := fake2)). easy.
  Qed.

End lemmas.


(*
(** * Expressing lesser operations with <<runSchedule>> *)
(******************************************************************************)
Section derived_operations_composition.


  #[local] Generalizable Variables A B W G.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}
    `{Applicative G1}
    `{Applicative G2}
    {A B C : Type}.

  Corollary bindd_to_runSchedule :
    forall (A B : Type) (t : T A)
      (f : W * A -> T B),
      bindd T f t = runSchedule T (fun A => A) f (iterate T B t).
  Proof.
    intros. rewrite bindd_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary bindt_to_runSchedule :
    forall `{Applicative G} (A B : Type) (t : T A)
      (f : A -> G (T B)),
      bindt T G f t = runSchedule T G (f ∘ extract (W ×)) (iterate T B t).
  Proof.
    intros. rewrite bindt_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary mapdt_to_runSchedule  :
    forall `{Applicative G} (A B : Type) (t : T A)
      `(f : W * A -> G B),
      mapdt T G f t = runSchedule T G (map G (ret T) ∘ f) (iterate T B t).
  Proof.
    intros. rewrite mapdt_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary bind_to_runSchedule :
    forall (A B : Type) (t : T A)
      (f : A -> T B),
      bind T f t = runSchedule T (fun A => A) (f ∘ extract (W ×)) (iterate T B t).
  Proof.
    intros. rewrite bind_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary mapd_to_runBatch `(f : W * A -> B) (t : T A) :
    mapd T f t = runSchedule T (fun A => A) (ret T ∘ f) (iterate T B t).
  Proof.
    rewrite mapd_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary mapt_to_runBatch `{Applicative G} `(f : A -> G B) (t : T A) :
    traverse T G f t = runSchedule T G (map G (ret T) ∘ f ∘ extract (W ×)) (iterate T B t).
  Proof.
    rewrite mapt_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

  Corollary map_to_runBatch `(f : A -> B) (t : T A) :
    map T f t = runSchedule T (fun A => A) (ret T ∘ f ∘ extract (W ×)) (iterate T B t).
  Proof.
    rewrite map_to_binddt. now rewrite (binddt_to_runSchedule T).
  Qed.

End derived_operations_composition.
*)


(** * Batch *)
(******************************************************************************)
Section with_functor.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Definition toBatchdm {A : Type} (B : Type) : T A -> @Batch (W * A) (T B) (T B) :=
    binddt T (Batch (W * A) (T B)) (batch (T B)).

End with_functor.

(** ** Expressing <<binddt>> with <<runBatch>> *)
(******************************************************************************)
Section with_monad.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import DT.Monad.Derived.

  Theorem binddt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G (T B)) (t : T A),
      binddt T G f t = runBatch f (toBatchdm T B t).
  Proof.
    intros.
    unfold toBatchdm.
    compose near t on right.
    rewrite (kdtm_morph W T (Batch (W * A) (T B)) G).
    now rewrite (runBatch_batch).
  Qed.

  Theorem bindd_to_runBatch :
    forall (A B : Type) (f : W * A -> T B) (t : T A),
      bindd T f t =
        runBatch (F := fun A => A) f (toBatchdm T B t).
  Proof.
    intros.
    unfold toBatchdm.
    compose near t on right.
    rewrite (kdtm_morph W T (Batch (W * A) (T B)) (fun A => A)).
    reflexivity.
  Qed.

  Theorem mapdt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G B) (t : T A),
      mapdt T G f t = runBatch f (toBatchd T B t).
  Proof.
    intros. apply (mapdt_to_runBatch T).
  Qed.

  Theorem mapd_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> B) (t : T A),
      mapd T f t = runBatch f (toBatchd T B t).
  Proof.
    intros.
    change (@Mapd_Binddt T W _ _) with
      (@Derived.Mapd_Mapdt T _ _).
    apply (mapd_to_runBatch T).
  Qed.

  Theorem map_to_runBatch : forall (A B : Type) (f : A -> B),
      map T f = runBatch f ∘ toBatch T B.
  Proof.
    intros.
    change (@Map_Binddt T W H0 H) with (@Derived.Map_Mapdt T _ _).
    change (@Traverse_Binddt T W _ _) with (@Derived.Traverse_Mapdt T _ _).
    apply (map_to_runBatch T).
  Qed.

End with_monad.

Import Derived.

Section with_monad.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  (** *** Composition with monad operattions *)
  (******************************************************************************)
  Lemma foldMapd_ret `{Monoid M} : forall `(f : W * A -> M),
      foldMapd T f ∘ ret T = f ∘ ret (W ×).
  Proof.
    intros. unfold foldMapd. unfold_ops @Mapdt_Binddt.
    rewrite (kdtm_binddt0 W T _ _ (G := const M)).
    reflexivity.
  Qed.

  Lemma foldMapd_binddt `{Applicative G} `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> G (T B)),
      map G (foldMapd T g) ∘ binddt T G f =
        foldMapd T (fun '(w, a) => map G (foldMapd T (preincr w g)) (f (w, a))).
  Proof.
    intros. unfold foldMapd. unfold_ops @Mapdt_Binddt.
    rewrite (kdtm_binddt2 W T _ _ _ (G1 := G) (G2 := const M)).
    fequal.
    - unfold Map_compose.
      ext A' B' f'.
      enough (hyp : map G (map (const M) f') = id).
      + rewrite hyp. reflexivity.
      + ext m. rewrite <- (fun_map_id G).
        reflexivity.
    - ext A' B' [t1 t2]. reflexivity.
  Qed.

  Corollary foldMapd_binddt_I `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd T g ∘ binddt T (fun A => A) f =
        foldMapd T (fun '(w, a) => foldMapd T (preincr w g) (f (w, a))).
  Proof.
    intros. change (foldMapd T g) with (map (fun A => A) (foldMapd T g)).
    now rewrite (foldMapd_binddt (G := fun A => A)).
  Qed.


  (** *** Composition with lessor operations *)
  (******************************************************************************)
  Lemma foldMapd_bindd `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd T g ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMapd T (preincr w g) (f (w, a))).
  Proof.
    intros. unfold_ops @Bindd_Binddt.
    change (foldMapd T g) with (map (fun A => A) (foldMapd T g)).
    now rewrite (foldMapd_binddt (G := fun A => A)).
  Qed.

End with_monad.

Import List.ListNotations.
Import Sets.Notations.

(** * Shape and contents *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import DT.Monad.Derived.

  (** ** Relating <<tolistd>> and <<binddt>> / <<ret>> *)
  (******************************************************************************)
  Lemma tolistd_ret : forall (A : Type) (a : A),
      tolistd T (ret T a) = [ (Ƶ, a) ].
  Proof.
    unfold tolistd.
    intros. compose near a.
    now rewrite (foldMapd_ret T).
  Qed.

  Lemma tolistd_binddt : forall `{Applicative G} `{Monoid M} `(f : W * A -> G (T B)),
      map G (tolistd T) ∘ binddt T G f =
        foldMapd T (fun '(w, a) => map G (foldMapd T (preincr w (ret list))) (f (w, a))).
  Proof.
    intros. unfold tolistd. now rewrite (foldMapd_binddt T).
  Qed.

  (** ** Relating <<tolistd>> and lesser operations *)
  (******************************************************************************)
  Lemma tolistd_bindd : forall `{Monoid M} `(f : W * A -> T B),
      tolistd T ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMapd T (preincr w (ret list)) (f (w, a))).
  Proof.
    intros. unfold_ops @Bindd_Binddt.
    change (@tolistd T _ _ B) with (map (fun A => A) (@tolistd T _ _ B)).
    rewrite (tolistd_binddt (G := fun A => A)).
    reflexivity.
  Qed.

  (** ** Corollaries for the rest *)
  (******************************************************************************)
  Corollary tosetd_ret : forall (A : Type) (a : A),
      tosetd T (ret T a) = {{ (Ƶ, a) }}.
  Proof.
    intros. unfold_ops @Tosetd_Kleisli.
    compose near a.
    now rewrite (foldMapd_ret T).
  Qed.

  Corollary tolist_binddt : forall `{Applicative G} `{Monoid M} `(f : W * A -> G (T B)),
      map G (tolist T) ∘ binddt T G f =
        foldMapd T (map G (tolist T) ∘ f).
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt _ _ _).
    rewrite (tolist_to_tolistd T).
    rewrite <- (fun_map_map G).
    reassociate ->.
    rewrite tolistd_binddt.
    rewrite (foldMapd_morphism T).
    rewrite (fun_map_map G).
    fequal. unfold tolistd.
    ext [w a]. unfold compose at 1 2.
    compose near (f (w, a)) on left.
    rewrite (fun_map_map G).
    rewrite (foldMapd_morphism T).
    rewrite (foldMapd_morphism T).
    fequal. fequal.
    ext [w' b]. reflexivity.
  Qed.

  (** ** Relating <<tolist>> and lesser operations *)
  (******************************************************************************)
  Lemma tolist_bindd : forall `{Monoid M} `(f : W * A -> T B),
      tolist T ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMap T (ret list) (f (w, a))).
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt T W _).
    rewrite (tolist_to_tolistd T).
    reassociate ->. rewrite (tolistd_bindd).
    rewrite (foldMapd_morphism T).
    fequal. ext [w a].
    cbn. compose near (f (w, a)) on left.
    rewrite (foldMapd_morphism T).
    rewrite (foldMap_to_foldMapd T).
    fequal. now ext [w' a'].
  Qed.

End DTM_tolist.

Import Setlike.Functor.Notations.

(** ** Characterizing membership in list operations *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import Derived.

  Lemma ind_iff_in_tolistd : forall (A : Type) (a : A) (w : W) (t : T A),
      (w, a) ∈d t <-> toset list (tolistd T t) (w, a).
  Proof.
    intros. unfold tolistd.
    unfold_ops @Tosetd_Kleisli.
    compose near t on right.
    rewrite (foldMapd_morphism T (ϕ := toset list)).
    replace (@ret set (Return_set) (W * A)) with (toset (A := W * A) list ∘ ret list).
    reflexivity. ext [w' a']. solve_basic_set.
  Qed.

  Lemma in_iff_in_tolist : forall (A : Type) (a : A) (t : T A),
      (a ∈ t) <-> toset list (tolist T t) a.
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt _ _ _).
    rewrite (toset_to_tolist T).
    reflexivity.
  Qed.

End DTM_tolist.

(** * Characterizing <<∈d>> *)
(******************************************************************************)
Section section.

  Context
    (T : Type -> Type)
    `{DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Existing Instance Toset_set.
  Existing Instance SetlikeFunctor_set.
  Lemma ind_iff_in : forall (A : Type) (a : A) (t : T A),
      a ∈ t <-> exists w, (w, a) ∈d t.
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt T _ _).
    now rewrite (ind_iff_in T).
  Qed.

  Lemma ind_ret_iff : forall {A : Type} (w : W) (a1 a2 : A),
      (w, a1) ∈d ret T a2 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros. unfold_ops @Tosetd_Kleisli.
    compose near a2 on left. rewrite (foldMapd_ret T).
    unfold compose. split.
    now inversion 1.
    inversion 1. subst. solve_basic_set.
  Qed.

  Lemma in_ret_iff : forall {A : Type} (a1 a2 : A),
      a1 ∈ ret T a2 <-> a1 = a2.
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Bindt T _ _).
    now rewrite (in_ret_iff T).
  Qed.

  Lemma ind_bindd_iff1 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd T f t ->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold Tosetd_Kleisli, tosetd, compose in *.
    change (foldMapd T (ret set) (bindd T f t) (wtotal, b))
      with (((foldMapd T (ret set) ∘ bindd T f) t) (wtotal, b)) in hyp.
    rewrite (foldMapd_bindd T) in hyp.
    rewrite (foldMapd_to_runBatch T) in hyp.
    rewrite (foldMapd_to_runBatch T).
    (* HACK: We want to call "rewrite (foldMapd_to_runBatch T)" but
    this fails under the binder. The following is a kludge. *)
    cut (exists (w1 w2 : W) (a : A),
               runBatch (B := False) (F := fun _ => set (W * A))
                 (@ret set Return_set (W * A)) (toBatchd T (A:=A) False t) (w1, a) /\
                 runBatch (B := False) (F := fun _ => set (W * B)) (ret set) (toBatchd T (A:=B) False (f (w1, a))) (w2, b) /\ wtotal = w1 ● w2).
    { intro. preprocess. repeat eexists; try rewrite (foldMapd_to_runBatch T B); eauto. }
    induction (toBatchd T False t).
    - cbv in hyp. inversion hyp.
    - destruct x as [wx ax].
      cbn in hyp. destruct hyp as [hyp | hyp].
      + (* (wtotal, b) in b0 *)
        specialize (IHb0 hyp).
        destruct IHb0 as [w1 [w2 [a [IH_a_in [IH_b_in IH_sum]]]]].
        exists w1 w2 a. split; [now left | auto].
      + (* (wotal, b) in f (wx,ax) *)
        clear IHb0.
        rewrite (foldMapd_to_runBatch T) in hyp.
        assert (lemma : exists w2 : W, runBatch (B := False) (F := fun _ => set (W * B)) (ret set) (toBatchd T False (f (wx, ax))) (w2, b) /\ wtotal = wx ● w2).
        { induction (toBatchd T False (f (wx, ax))).
          - cbv in hyp. inversion hyp.
          - destruct hyp as [hyp|hyp].
            + specialize (IHb1 hyp). destruct IHb1 as [w2 [IHb1' IHb1'']].
              exists w2. split. now left. assumption.
            + destruct x as [wx2 b2]. cbv in hyp. inverts hyp.
              exists wx2. split. now right. reflexivity. }
        destruct lemma as [w2 rest].
        exists wx w2 ax. split. now right. assumption.
  Qed.

  Lemma ind_bindd_iff2 :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
    (exists (w1 w2 : W) (a : A),
      (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2) ->
      (wtotal, b) ∈d bindd T f t.
  Proof.
    introv [w1 [w2 [a [a_in [b_in wsum]]]]]. subst.
    unfold tosetd, Tosetd_Kleisli, compose in *.
    compose near t.
    rewrite (foldMapd_bindd T).
    rewrite (foldMapd_to_runBatch T).
    rewrite (foldMapd_to_runBatch T) in a_in.
    rewrite (foldMapd_to_runBatch T) in b_in.
    induction (toBatchd T False t).
    - cbv in a_in. inversion a_in.
    - cbn in a_in. destruct a_in as [a_in | a_in].
      + destruct x as [wx ax].
        specialize (IHb0 a_in b_in).
        left. assumption.
      + clear IHb0. destruct x as [wx ax].
        inverts a_in. right.
        { rewrite (foldMapd_to_runBatch T).
          induction (toBatchd T False (f (w1, a))).
          - inversion b_in.
          - destruct b_in.
            + left. auto.
            + right. destruct x. unfold preincr, compose. cbn.
              inverts H2. easy.
        }
  Qed.

  Theorem ind_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bindd T f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using ind_bindd_iff1, ind_bindd_iff2.
  Qed.

  Theorem ind_bind_iff :
    forall `(f : A -> T B) (t : T A) (wtotal : W) (b : B),
      (wtotal, b) ∈d bind T f t <->
      exists (w1 w2 : W) (a : A),
        (w1, a) ∈d t /\ (w2, b) ∈d f a
        /\ wtotal = w1 ● w2.
  Proof.
    intros. apply ind_bindd_iff.
  Qed.

  (** ** Characterizing <<∈>> with <<bindd>> *)
  (******************************************************************************)
  Corollary in_bindd_iff :
    forall `(f : W * A -> T B) (t : T A) (b : B),
      b ∈ bindd T f t <->
      exists (w1 : W) (a : A),
        (w1, a) ∈d t /\ b ∈ f (w1, a).
  Proof.
    intros.
    rewrite (ind_iff_in).
    setoid_rewrite ind_bindd_iff.
    setoid_rewrite (ind_iff_in).
    split; intros; preprocess; repeat eexists; eauto.
  Qed.

  Corollary in_bind_iff :
    forall `(f : A -> T B) (t : T A) (b : B),
      b ∈ bind T f t <-> exists (a : A), a ∈ t /\ b ∈ f a.
  Proof.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt _ _ _).
    intros. setoid_rewrite (ind_iff_in).
    setoid_rewrite (ind_bindd_iff).
    intuition.
    - preprocess. eexists; split; eauto.
    - preprocess. repeat eexists; eauto.
  Qed.

  Theorem in_mapd_iff :
    forall `(f : W * A -> B) (t : T A) (b : B),
      b ∈ mapd T f t <-> exists (w : W) (a : A), (w, a) ∈d t /\ f (w, a) = b.
  Proof.
    intros.
    change (@Traverse_Binddt T W _ _)
      with (@Derived.Traverse_Mapdt _ _ _).
    rewrite (ind_iff_in).
    setoid_rewrite (ind_mapd_iff T).
    reflexivity.
  Qed.

End section.

(** ** Respectfulness for <<bindd>> *)
(******************************************************************************)
Section bindd_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Theorem bindd_respectful :
    forall A B (t : T A) (f g : W * A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> bindd T f t = bindd T g t.
  Proof.
    unfold_ops @Tosetd_Kleisli.
    unfold foldMapd in *.
    introv hyp.
    rewrite (mapdt_constant_applicative2 T False B) in hyp.
    unfold mapdt, Mapdt_Binddt in hyp.
    rewrite (binddt_to_runBatch T) in hyp.
    do 2 rewrite (bindd_to_runBatch T).
    induction (toBatchdm T B t).
    - easy.
    - destruct x. do 2 rewrite runBatch_rw2.
      rewrite runBatch_rw2 in hyp.
      fequal.
      + apply IHb. intros. apply hyp.
        cbn. now left.
      + apply hyp. now right.
  Qed.

  (** *** For equalities with special cases *)
  (** Corollaries with conclusions of the form <<bindd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary bindd_respectful_bind :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> T B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> bindd T f t = bind T g t.
  Proof.
    introv hyp. rewrite bind_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_mapd :
    forall A B (t : T A) (f : W * A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T (g (w, a)))
      -> bindd T f t = mapd T g t.
  Proof.
    introv hyp. rewrite mapd_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_map :
    forall A B (t : T A) (f : W * A -> T B) (g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T (g a))
      -> bindd T f t = map T g t.
  Proof.
    introv hyp. rewrite map_to_bindd.
    apply bindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary bindd_respectful_id :
    forall A (t : T A) (f : W * A -> T A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = ret T a)
      -> bindd T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (kmond_bindd1 T).
    eapply bindd_respectful.
    unfold compose; cbn. auto.
  Qed.

End bindd_respectful.

(** ** Respectfulness for <<bind>> *)
(******************************************************************************)
Section bind_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma bind_respectful :
    forall A B (t : T A) (f g : A -> T B),
      (forall (a : A), a ∈ t -> f a = g a)
      -> bind T f t = bind T g t.
  Proof.
    introv hyp. rewrite bind_to_bindd.
    apply (bindd_respectful T). introv premise. apply (ind_implies_in T) in premise.
    unfold compose; cbn. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<bind t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary bind_respectful_mapd :
    forall A B (t : T A) (f : A -> T B) (g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = ret T (g (w, a)))
      -> bind T f t = mapd T g t.
  Proof.
    intros. rewrite mapd_to_bindd.
    symmetry. apply (bindd_respectful_bind T).
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary bind_respectful_map :
    forall A B (t : T A) (f : A -> T B) (g : A -> B),
      (forall (a : A), a ∈ t -> f a = ret T (g a))
      -> bind T f t = map T g t.
  Proof.
    intros. rewrite map_to_bind.
    symmetry. apply bind_respectful.
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary bind_respectful_id : forall A (t : T A) (f : A -> T A),
      (forall (a : A), a ∈ t -> f a = ret T a)
      -> bind T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (kmon_bind1 T).
    eapply bind_respectful.
    unfold compose; cbn. auto.
  Qed.

End bind_respectful.

(** ** Respectfulness for <<mapd>> *)
(******************************************************************************)
Section mapd_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma mapd_respectful :
    forall A B (t : T A) (f g : W * A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g (w, a))
      -> mapd T f t = mapd T g t.
  Proof.
    introv hyp. do 2 rewrite mapd_to_bindd.
    apply (bindd_respectful T). introv premise.
    unfold compose; cbn. fequal. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mapd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mapd_respectful_map :
    forall A (t : T A) (f : W * A -> A) (g : A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = g a)
      -> mapd T f t = map T g t.
  Proof.
    intros. rewrite map_to_mapd.
    apply (mapd_respectful). introv Hin.
    unfold compose; cbn; auto.
  Qed.

  Corollary mapd_respectful_id : forall A (t : T A) (f : W * A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f (w, a) = a)
      -> mapd T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (dfun_mapd1 W T).
    eapply (mapd_respectful).
    cbn. auto.
  Qed.

End mapd_respectful.

(** ** Respectfulness for <<map>> *)
(******************************************************************************)
Section map_respectful.

  Context
    (T : Type -> Type)
    `{Kleisli.DT.Monad.Monad W T}.

  Import Derived.

  #[local] Notation "x ∈d t" :=
    (tosetd _ t x) (at level 50) : tealeaves_scope.

  Lemma map_respectful :
    forall A B (t : T A) (f g : A -> B),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = g a)
      -> map T f t = map T g t.
  Proof.
    introv hyp. do 2 rewrite map_to_mapd.
    now apply (mapd_respectful T).
  Qed.

  Corollary map_respectful_id :
    forall A (t : T A) (f : A -> A),
      (forall (w : W) (a : A), (w, a) ∈d t -> f a = a)
      -> map T f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (fun_map_id T).
    eapply (map_respectful).
    auto.
  Qed.

End map_respectful.
