From Tealeaves Require Import
  Classes.Kleisli
  Functors.Writer
  Functors.Constant.

Import Product.Notations.
Import Monoid.Notations.
Import Kleisli.Notations.

#[local] Generalizable Variables G A B C.

Arguments incr {W}%type_scope {op} {A}%type_scope _ _.
Arguments preincr {W}%type_scope {op} {A B}%type_scope f%function_scope w _.

    (*
    d/t/m:
    000 0 map      no d or t or m
    001 1 bind     no context or effect
    010 2 traverse no context or subst
    011 3 binddt   no context
    100 4 mapd     no effect or subst
    101 5 bindd    no effect
    110 6 mapdt    no subst
    111 7 binddt   everything
     *)

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

  Section assume_dtm.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  (** ** Rewriting rules for special cases of <<kc7>> *)
  (******************************************************************************)
  Section kc7_special_cases.

    Context
      `{Applicative G1}
      `{Applicative G2}
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
      rewrite (fun_map_map G1).
      rewrite (kdtm_binddt0 W T G2 B C).
      unfold kc6.
      unfold_ops @Map_compose;
        do 2 reassociate <-;
          unfold_compose_in_compose.
      rewrite (fun_map_map G1).
      unfold compose; cbn.
      compose near (f (w, a)) on right.
      rewrite (fun_map_map G1).
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
      rewrite (fun_map_map G1).
      rewrite (kdtm_binddt0 W T G2).
      unfold_ops @Map_compose.
      unfold compose; cbn.
      compose near (f a) on right.
      rewrite (fun_map_map G1).
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
      rewrite (fun_map_map G1).
      rewrite (fun_map_map G1).
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
      rewrite (fun_map_map G1).
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
      rewrite (fun_map_map G1).
      rewrite (kdtm_binddt0 W T (fun A => A)).
      rewrite (preincr_ret W).
      reflexivity.
    Qed.

  End kc7_special_cases.

  #[local] Arguments binddt {M}%type_scope {T U}%function_scope {Binddt}   G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
  #[local] Arguments mapdt  {M}%type_scope {T}%function_scope   {Mapdt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
  #[local] Arguments bindd  {M}%type_scope {T U}%function_scope {Bindd}                               (A B)%type_scope _%function_scope _.
  #[local] Arguments mapd   {M}%type_scope {T}%function_scope   {Mapd}                                (A B)%type_scope _%function_scope _.
  #[local] Arguments bindt                 {T U}%function_scope {Bindt}    G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
  #[local] Arguments traverse              {T}%function_scope   {Traverse} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.
  #[local] Arguments bind                  {T U}%function_scope {Bind}                                (A B)%type_scope _%function_scope _.

  (** ** Composition laws *)
  (******************************************************************************)
  Lemma binddt_app_l :
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : W * A -> G (T B)),
      @binddt W T T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G) (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f = binddt G A B f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma binddt_app_r :
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : W * A -> G (T B)),
      @binddt W T T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A)) (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f = binddt G A B f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity1.
  Qed.

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
        map G1 (T B) (G2 (T C)) (mapdt G2 B C g) ∘ binddt G1 A B f =
          binddt (G1 ∘ G2) A C (fun '(w, a) => map G1 (T B) (G2 (T C)) (mapdt G2 B C (g ⦿ w)) (f (w, a))).
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
        map G1 (T B) (T C) (bindd B C g) ∘ binddt G1 A B f =
          binddt G1 A C (fun '(w, a) => map G1 (T B) (T C) (bindd B C (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 (fun A => A)).
      rewrite (binddt_app_r G1).
      (* rewrite kc7_57 *)
      reflexivity.
    Qed.

    (* composition_47 *)
    Lemma mapd_binddt: forall
        (g : W * B -> C)
        (f : W * A -> G1 (T B)),
        map G1 (T B) (T C) (mapd B C g) ∘ binddt G1 A B f =
          binddt G1 A C (fun '(w, a) => map G1 (T B) (T C) (mapd B C (g ⦿ w)) (f (w, a))).
    Proof.
      intros.
      rewrite mapd_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 (fun A => A) A B).
      rewrite (binddt_app_r G1).
      rewrite kc7_47.
      reflexivity.
    Qed.

    (* composition_37 *)
    Lemma bindt_binddt:
      forall (g : B -> G2 (T C))
        (f : W * A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (bindt G2 B C g) ∘ binddt G1 A B f =
          binddt (G1 ∘ G2) A C (map G1 (T B) (G2 (T C)) (bindt G2 B C g) ∘ f).
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
        map G1 (T B) (G2 (T C)) (traverse G2 B C g) ∘ binddt G1 A B f =
          binddt (G1 ∘ G2) A C (map G1 (T B) (G2 (T C)) (traverse G2 B C  g) ∘ f).
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
        map G1 (T B) (T C) (bind B C g) ∘ binddt G1 A B f =
          binddt G1 A C (map G1 (T B) (T C) (bind B C g) ∘ f).
    Proof.
      intros.
      rewrite bind_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 (fun A => A)).
      rewrite kc7_17.
      rewrite (binddt_app_r G1).
      reflexivity.
    Qed.

    (* composition_07 *)
    Lemma map_binddt:
      forall (g : B -> C)
        (f : W * A -> G1 (T B)),
        map G1 (T B) (T C) (map T B C g) ∘ binddt G1 A B f =
          binddt G1 A C (map G1 (T B) (T C) (map T B C g) ∘ f).
    Proof.
      intros.
      rewrite map_to_binddt at 1.
      rewrite (kdtm_binddt2 W T G1 (fun A => A)).
      rewrite kc7_07.
      rewrite (binddt_app_r G1).
      reflexivity.
    Qed.

    (** *** <<binddt>> on the left *)
    (******************************************************************************)
    (* composition_76 *)
    Lemma binddt_mapdt: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> G1 B),
        map G1 (T B) (G2 (T C)) (binddt G2 B C g) ∘ mapdt G1 A B f =
          binddt (G1 ∘ G2) A C (fun '(w, a) => map G1 B (G2 (T C)) (fun b => g (w, b)) (f (w, a))).
    Proof.
      intros.
      rewrite (mapdt_to_binddt).
      rewrite (kdtm_binddt2 W T G1 G2 A B C).
      rewrite (kc7_76).
      unfold kc6.
      fequal. ext [w a].
      unfold compose, strength; cbn.
      compose near (f (w, a)) on left.
      rewrite (fun_map_map G1).
      reflexivity.
    Qed.

    (* composition_75 *)
    Lemma binddt_bindd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> T B),
        binddt G2 B C g ∘ bindd A B f =
          binddt G2 A C (fun '(w, a) => binddt G2 B C (g ⦿ w) (f (w, a))).
    Proof.
      intros.
      rewrite bindd_to_binddt.
      change (binddt G2 B C g) with (map (fun A => A) (T B) (G2 (T C)) (binddt G2 B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) G2).
      rewrite (binddt_app_l G2).
      reflexivity.
    Qed.

    (* composition_74 *)
    Lemma binddt_mapd: forall
        (g : W * B -> G2 (T C))
        (f : W * A -> B),
        binddt G2 B C g ∘ mapd A B f =
          binddt G2 A C (g ⋆4 f).
    Proof.
      intros.
      rewrite (mapd_to_binddt) at 1.
      change (binddt G2 B C g) with (map (fun A => A) (T B) (G2 (T C)) (binddt G2 B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) G2 A B C).
      rewrite (kc7_74).
      rewrite (binddt_app_l G2).
      reflexivity.
    Qed.

    (* composition_73 *)
    Lemma binddt_bindt: forall
        (g : W * B -> G2 (T C))
        (f : A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (binddt G2 B C g) ∘ bindt G1 A B f =
          binddt (G1 ∘ G2) A C (fun '(w, a) => map G1 (T B) (G2 (T C)) (binddt G2 B C (g ⦿ w)) (f a)).
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
        map G1 (T B) (G2 (T C)) (binddt G2 B C g) ∘ traverse G1 A B f =
          binddt (G1 ∘ G2) A C (fun '(w, a) => map G1 B (G2 (T C)) (fun b => g (w, b)) (f a)).
    Proof.
      intros.
      rewrite (traverse_to_binddt).
      rewrite (kdtm_binddt2 W T G1 G2 A B C).
      rewrite (kc7_72).
      reflexivity.
    Qed.

    (* composition_71 *)
    Lemma binddt_bind: forall
        (g : W * B -> G2 (T C))
        (f : A -> T B),
        binddt G2 B C g ∘ bind A B f =
          binddt G2 A C (fun '(w, a) => binddt G2 B C (g ⦿ w) (f a)).
    Proof.
      intros.
      rewrite (bind_to_binddt).
      change (binddt G2 B C g) with (map (fun A => A) (T B) (G2 (T C)) (binddt G2 B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) G2 A B C).
      rewrite (binddt_app_l G2).
      rewrite (kc7_71).
      reflexivity.
    Qed.

    (* composition_70 *)
    Lemma binddt_map: forall
        (g : W * B -> G2 (T C))
        (f : A -> B),
        binddt G2 B C g ∘ map T A B f =
          binddt G2 A C (g ∘ map (W ×) A B f).
    Proof.
      intros.
      rewrite (map_to_binddt).
      change (binddt G2 B C g) with (map (fun A => A) _ _ (binddt G2 B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) G2 A B C).
      rewrite (binddt_app_l G2).
      rewrite (kc7_70).
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
        map G1 (T B) (G2 (T C)) (mapdt G2 B C g) ∘ mapdt G1 A B f =
          mapdt (T := T) (G1 ∘ G2) A C (g ⋆6 f).
    Proof.
      intros.
      do 2 rewrite (mapdt_to_binddt) at 1.
      rewrite (kdtm_binddt2 W T G1 G2).
      rewrite (kc7_66).
      reflexivity.
    Qed.

    (* composition_55 *)
    Lemma bindd_bindd : forall
        (g : W * B -> T C)
        (f : W * A -> T B),
        bindd B C g ∘ bindd A B f = bindd A C (g ⋆5 f).
    Proof.
      intros.
      do 2 rewrite (bindd_to_binddt).
      change (binddt ?X ?B ?C g) with (map (fun A => A) _ _ (binddt X B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) (fun A => A)).
      rewrite (binddt_app_l (fun A => A)).
      reflexivity.
    Qed.

    (* composition_33 *)
    Lemma bindt_bindt : forall
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (bindt G2 B C g) ∘ bindt G1 A B f = bindt (G1 ∘ G2) A C (g ⋆3 f).
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
        map G1 (T B) (T C) (bindd B C g) ∘ mapdt G1 A B f =
          binddt G1 A C (fun '(w, a) => map G1 B (T C) (g ∘ pair w) (f (w, a))).
    Proof.
      intros.
      rewrite (bindd_to_binddt).
      rewrite (binddt_mapdt G1 (fun A => A)).
      rewrite (binddt_app_r G1).
      reflexivity.
    Qed.

    (* composition_65 *)
    Lemma mapdt_bindd: forall
        (g : W * B -> G2 C)
        (f : W * A -> T B),
        mapdt G2 B C g ∘ bindd A B f =
          binddt G2 A C (fun '(w, a) => mapdt G2 B C (g ⦿ w) (f (w, a))).
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
        bindt G2 B C g ∘ bindd A B f =
          binddt G2 A C (bindt G2 B C g ∘ f).
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
        map G1 _ _ (bindd B C g) ∘ bindt G1 A B f =
          binddt G1 A C (fun '(w, a) => map G1 _ _ (bindd B C (g ⦿ w)) (f a)).
    Proof.
      intros.
      rewrite (bindd_to_binddt).
      rewrite (bindt_to_binddt).
      rewrite (kdtm_binddt2 W T G1 (fun A => A) A B C).
      rewrite (binddt_app_r G1).
      reflexivity.
    Qed.

    (* composition_63 *)
    Lemma mapdt_bindt: forall
        (g : W * B -> G2 C)
        (f : A -> G1 (T B)),
        map G1 _ _ (mapdt G2 B C g) ∘ bindt G1 A B f =
          binddt (G1 ∘ G2) A C (fun '(w, a) => map G1 _ _ (mapdt G2 B C (g ⦿ w)) (f a)).
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
        map G1 _ _ (bindt G2 _ _ g) ∘ mapdt G1 _ _ f =
          binddt (G1 ∘ G2) _ _ (map G1 B (G2 (T C)) g ∘ f).
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
        mapd B C g ∘ bindd A B f =
          bindd A C (fun '(w, a) => mapd B C (g ⦿ w) (f (w, a))).
    Proof.
      intros. rewrite (mapd_to_bindd W T).
      rewrite (bindd_bindd).
      reflexivity.
    Qed.

    (* composition_25 *)
    Lemma traverse_bindd: forall
        (g : B -> G2 C)
        (f : W * A -> T B),
        traverse G2 B C g ∘ bindd A B f =
          binddt G2 A C (fun '(w, a) => traverse G2 B C g (f (w, a))).
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
        bind B C g ∘ bindd A B f =
          bindd A C (bind B C g ∘ f).
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
        map T B C g ∘ bindd A B f =
          bindd A C (map T B C g ∘ f).
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
        bindd B C g ∘ mapd A B f =
          bindd A C (g ⋆4 f).
    Proof.
      intros. rewrite (mapd_to_bindd W T).
      rewrite (bindd_bindd).
      rewrite (kc5_54).
      reflexivity.
    Qed.

    (* composition_52 *)
    (* TODO bindd_traverse *)

    (* composition_51 *)
    Lemma bindd_bind: forall
        (g : W * B -> T C)
        (f : A -> T B),
        bindd B C g ∘ bind A B f =
          bindd A C (fun '(w, a) => bindd B C (g ⦿ w) (f a)).
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
        map G1 (T B) (T C) (mapd B C g) ∘ mapdt G1 A B f =
          mapdt G1 A C (map G1 (W * B) C g ∘ strength G1 ∘ cobind (W ×) A (G1 B) f).
    Proof.
      introv.
      rewrite (mapd_to_mapdt).
      rewrite (mapdt_mapdt G1 (fun A => A)).
      do 2 rewrite (mapdt_to_binddt).
      rewrite (binddt_app_r G1).
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
        mapdt G2 B C g ∘ mapd A B f = mapdt G2 A C (g ⋆4 f).
    Proof.
      introv.
      rewrite (mapd_to_mapdt).
      pose (mapdt_mapdt (fun A => A) G2 (A := A) (B := B) (C := C) g f) as lemma.
      change (map (fun A => A) ?A ?B ?f) with f in lemma.
      rewrite lemma; clear lemma.
      rewrite (mapdt_to_binddt).
      rewrite (binddt_app_l G2).
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
        map G1 (T B) (T C) (mapd B C g) ∘ bindt G1 A B f
        = binddt G1 A C (fun '(w, a) => map G1 (T B) (T C) (mapd B C (g ⦿ w)) (f a)).
    Proof.
      introv.
    Abort.

    (* composition_23 *)
    (* traverse_bindt *)

    (* composition_13 *)
    Lemma bind_bindt : forall (g : B -> T C) (f : A -> G1 (T B)),
        map G1 (T B) (T C) (bind B C g) ∘ bindt G1 A B f =
          bindt G1 A C (map G1 (T B) (T C) (bind B C g) ∘ f).
    Proof.
      introv.
      rewrite (bind_to_bindt).
      rewrite (bindt_bindt G1 (fun A => A)).
      rewrite (bindt_to_binddt).
      rewrite (binddt_app_r G1).
      reflexivity.
    Qed.

    (* composition_03 *)
    Lemma map_bindt : forall (g : B -> C) (f : A -> G1 (T B)),
        map G1 (T B) (T C) (map T B C g) ∘ bindt G1 A B f =
          bindt G1 A C (map G1 (T B) (T C) (map T B C g) ∘ f).
    Proof.
      intros.
      rewrite (map_to_bindt).
      rewrite (bindt_bindt G1 (fun A => A)).
      rewrite (bindt_to_binddt).
      rewrite (binddt_app_r G1).
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
        bindt G2 B C g ∘ bind A B f = bindt G2 A C (bindt G2 B C g ∘ f).
    Proof.
      intros.
      rewrite (bind_to_bindt).
      change (bindt ?X ?B ?C g) with (map (fun A => A) _ _ (bindt X B C g)).
      rewrite (bindt_bindt (fun A => A) G2).
      rewrite (bindt_to_binddt).
      rewrite (binddt_app_l G2).
      reflexivity.
    Qed.

    (* composition_30 *)
    Lemma bindt_map : forall `(g : B -> G2 (T C)) `(f : A -> B),
        bindt G2 B C g ∘ map T A B f = bindt G2 A C (g ∘ f).
    Proof.
      intros.
      rewrite (map_to_bindt).
      change (bindt ?X ?B ?C g) with (map (fun A => A) _ _ (bindt X B C g)).
      rewrite (bindt_bindt (fun A => A) G2).
      rewrite (bindt_to_binddt).
      rewrite (binddt_app_l G2).
      rewrite (kc3_30).
      reflexivity.
    Qed.

    (** *** <<traverse>> on the right *)
    (******************************************************************************)
    (* composition_42 *)
    (* TODO mapd_traverse *)

    (* composition_22 *)
    Lemma traverse_traverse : forall `(g : B -> G2 C) `(f : A -> G1 B),
        map G1 _ _ (traverse G2 B C g) ∘ traverse G1 A B f =
          traverse (G1 ∘ G2) _ _ (map G1 _ _ g ∘ f).
    Proof.
      intros.
      do 3 rewrite traverse_to_binddt.
      rewrite (kdtm_binddt2 W T G1 G2).
      rewrite (kc7_22).
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
        mapd B C g ∘ mapd A B f = mapd A C (g ∘ cobind (W ×) A B f).
    Proof.
      intros.
      do 3 rewrite (mapd_to_binddt).
      change (binddt ?X ?B ?C ?g) with (map (fun A => A) _ _ (binddt X B C g)) at 1.
      rewrite (kdtm_binddt2 W T (fun A => A) (fun A => A)).
      rewrite (binddt_app_l (fun A => A)).
      rewrite (kc7_44).
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
        bind B C g ∘ bind A B f = bind A C (g ⋆1 f).
    Proof.
      intros.
      do 3 rewrite (bind_to_binddt).
      change (binddt ?X ?B ?C ?g) with (map (fun A => A) _ _ (binddt X B C g)) at 1.
      rewrite (kdtm_binddt2 W T (fun A => A) (fun A => A)).
      rewrite (binddt_app_l (fun A => A)).
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
      change (binddt ?I B C ?g) with (map (fun A => A) _ _ (binddt I B C g)).
      rewrite (kdtm_binddt2 W T (fun A => A) (fun A => A)).
      rewrite (binddt_app_l (fun A => A)).
      rewrite (kc7_00).
      reflexivity.
    Qed.

  End composition_special_cases_bottom.

  (** ** Identity laws *)
  (******************************************************************************)
  Lemma bindd_id : forall A : Type,
      bindd A A (ret T A ∘ extract (prod W) A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma bindt_id : forall A : Type,
      bindt (fun A : Type => A) A A (ret T A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma mapdt_id : forall A : Type,
      mapdt (fun A => A) A A (extract (W ×) A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma mapd_id : forall A : Type,
      mapd A A (extract (W ×) A) = @id (T A).
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma traverse_id : forall A : Type,
      traverse (T := T) (fun A => A) A A (@id A) = id.
  Proof.
    apply (kdtm_binddt1 W T).
  Qed.

  Lemma bind_id : forall A : Type,
      bind A A (ret T A) = @id (T A).
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
      bindd A B f ∘ ret T A = f ∘ ret (prod W) A.
  Proof.
    intros.
    rewrite (bindd_to_binddt).
    rewrite (kdtm_binddt0 W T (fun A => A)).
    reflexivity.
  Qed.

  Lemma bindt_ret :
    forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G (T B)),
      bindt G A B f ∘ ret T A = f.
  Proof.
    intros.
    rewrite (bindt_to_binddt).
    rewrite (kdtm_binddt0 W T G).
    reflexivity.
  Qed.

  Lemma bind_ret :
    forall (A B : Type) (f : A -> T B),
      bind A B f ∘ ret T A = f.
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
        ϕ (T B) ∘ bindt G1 A B f = bindt G2 A B (ϕ (T B) ∘ f).
    Proof.
      intros.
      rewrite (bindt_to_binddt).
      rewrite (kdtm_morph W T G1 G2).
      reflexivity.
    Qed.

    Lemma mapdt_morph:
      forall (A B : Type) (f : W * A -> G1 B),
        mapdt G2 A B (ϕ B ∘ f) = ϕ (T B) ∘ mapdt G1 A B f.
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
        ϕ (T B) ∘ traverse G1 A B f = traverse G2 A B (ϕ B ∘ f).
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

Import DerivedInstances.

(** * Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}
    (M : Type)
    `{Monoid M}.

  Lemma binddt_constant_applicative1 {A B : Type}
    `(f : W * A -> const M (T B)) :
    binddt W T T (const M) A B f =
      binddt W T T (const M) A False f.
  Proof.
    change_right (map (const M) (T False) (T B) (map T False B exfalso)
                    ∘ (binddt W T T (const M) A False (f : W * A -> const M (T False)))).
    rewrite (map_binddt W T (const M)).
    reflexivity.
  Qed.

  Lemma binddt_constant_applicative2 (fake1 fake2 : Type)
    `(f : W * A -> const M (T B)) :
    binddt W T T (const M) A fake1 f
    = binddt W T T (const M) A fake2 f.
  Proof.
    intros.
    rewrite (binddt_constant_applicative1 (B := fake1)).
    rewrite (binddt_constant_applicative1 (B := fake2)).
    easy.
  Qed.

End lemmas.

From Tealeaves Require Import
  Functors.Batch.

Import Batch.Notations.

(** * Traversals as <<Batch>> coalgebras *)
(******************************************************************************)
Section traversals_coalgebras.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  Definition batch {A : Type} (B : Type) : A -> @Batch A B B :=
    fun a => (Done (@id B)) ⧆ a.

End traversals_coalgebras.

(** * Batch *)
(******************************************************************************)
Section with_functor.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Definition toBatch {A : Type} (B : Type) : T A -> @Batch (W * A) (T B) (T B) :=
    binddt W T T (Batch (W * A) (T B)) A B (batch (T B)).

End with_functor.

(** ** Basic lemmas for <<runBatch>> *)
(******************************************************************************)
Lemma runBatch_batch : forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G B),
    runBatch f ∘ batch B = f.
Proof.
  intros. ext a. cbn.
  now rewrite ap1.
Qed.

Lemma extract_to_runBatch : forall (A X : Type) (j : @Batch A A X),
    extract_Batch j = runBatch (@id A) j.
Proof.
  intros. induction j.
  - reflexivity.
  - cbn. now rewrite <- IHj.
Qed.

#[local] Arguments runBatch {A}%type_scope F%function_scope {B}%type_scope ϕ%function_scope
  {H H0 H1} {X}%type_scope j.

(** ** Expressing <<binddt>> with <<runBatch>> *)
(******************************************************************************)
Section with_monad.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

  Theorem binddt_to_runBatch :
    forall `{Applicative G} (A B : Type) (f : W * A -> G (T B)) (t : T A),
      binddt W T T G A B f t = runBatch G f (toBatch W T B t).
  Proof.
    intros.
    unfold toBatch.
    compose near t on right.
    rewrite (kdtm_morph W T (Batch (W * A) (T B)) G).
    now rewrite (runBatch_batch).
  Qed.

  Theorem bindd_to_runBatch :
    forall (A B : Type) (f : W * A -> T B) (t : T A),
      bindd W T T A B f t =
        runBatch (fun A => A) f (toBatch W T B t).
  Proof.
    intros.
    unfold toBatch.
    compose near t on right.
    rewrite (kdtm_morph W T (Batch (W * A) (T B)) (fun A => A)).
    rewrite (runBatch_batch (fun A => A) (W * A) (T B) f).
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

(** * Expressing lesser operations with <<runSchedule>> *)
(******************************************************************************)
Section derived_operations_composition.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}
    `{Applicative G1}
    `{Applicative G2}
    {A B C : Type}.

  Corollary bindd_to_runBatch :
    forall (t : T A)
      (f : W * A -> T B),
      bindd W T T A B f t = runBatch (fun A => A) f (toBatch W T B t).
  Proof.
    intros.
    rewrite bindd_to_binddt.
    now rewrite (binddt_to_runBatch T).
  Qed.

  Corollary bindt_to_runBatch :
    forall `{Applicative G} (A B : Type) (t : T A)
      (f : A -> G (T B)),
      bindt T G f t = runBatch T G (f ∘ extract (W ×)) (iterate T B t).
  Proof.
    intros. rewrite bindt_to_binddt. now rewrite (binddt_to_runBatch T).
  Qed.

  Corollary mapdt_to_runBatch  :
    forall `{Applicative G} (A B : Type) (t : T A)
      `(f : W * A -> G B),
      mapdt T G f t = runBatch T G (map G (ret T) ∘ f) (iterate T B t).
  Proof.
    intros. rewrite mapdt_to_binddt. now rewrite (binddt_to_runBatch T).
  Qed.

  Corollary bind_to_runBatch :
    forall (A B : Type) (t : T A)
      (f : A -> T B),
      bind T f t = runBatch T (fun A => A) (f ∘ extract (W ×)) (iterate T B t).
  Proof.
    intros. rewrite bind_to_binddt. now rewrite (binddt_to_runBatch T).
  Qed.

  Corollary mapd_to_runBatch `(f : W * A -> B) (t : T A) :
    mapd T f t = runBatch T (fun A => A) (ret T ∘ f) (iterate T B t).
  Proof.
    rewrite mapd_to_binddt. now rewrite (binddt_to_runBatch T).
  Qed.

  Corollary traverse_to_runBatch `{Applicative G} `(f : A -> G B) (t : T A) :
    traverse T G f t = runBatch T G (map G (ret T) ∘ f ∘ extract (W ×)) (iterate T B t).
  Proof.
    rewrite traverse_to_binddt. now rewrite (binddt_to_runBatch T).
  Qed.

  Corollary map_to_runBatch `(f : A -> B) (t : T A) :
    map T f t = runBatch T (fun A => A) (ret T ∘ f ∘ extract (W ×)) (iterate T B t).
  Proof.
    rewrite map_to_binddt. now rewrite (binddt_to_runBatch T).
  Qed.

End derived_operations_composition.






Section with_monad.

  Context
    (W : Type)
    (T : Type -> Type)
    `{DTM W T}.

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
        foldMapd T (fun '(w, a) => map G (foldMapd T (g ⦿ w)) (f (w, a))).
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
        foldMapd T (fun '(w, a) => foldMapd T (g ⦿ w) (f (w, a))).
  Proof.
    intros. change (foldMapd T g) with (map (fun A => A) (foldMapd T g)).
    now rewrite (foldMapd_binddt (G := fun A => A)).
  Qed.


  (** *** Composition with lessor operations *)
  (******************************************************************************)
  Lemma foldMapd_bindd `{Monoid M} : forall `(g : W * B -> M) `(f : W * A -> T B),
      foldMapd T g ∘ bindd T f =
        foldMapd T (fun '(w, a) => foldMapd T (g ⦿ w) (f (w, a))).
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
