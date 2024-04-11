
(** * Specialized <<Batch>> for DTMs *)
(******************************************************************************)

Module Batch_DTM.

  #[local] Unset Implicit Arguments.

  Section Batch_DTM.

    Context
      {T : Type -> Type}
      {W A B : Type}.

    Inductive Batch_DTM C : Type :=
    | Done : C -> Batch_DTM C
    | Step : Batch_DTM (T B -> C) -> W * A -> Batch_DTM C.

    Fixpoint map_Batch_DTM `{f : C -> D} `(c : Batch_DTM C) : Batch_DTM D :=
      match c with
      | Done _ c => Done D (f c)
      | Step _ rest (pair w a) =>
          Step D (@map_Batch_DTM (T B -> C) (T B -> D) (compose f) rest) (w, a)
      end.

    #[export] Instance Map_Batch_DTM : Map Batch_DTM := @map_Batch_DTM.

    Lemma map_id_Batch_DTM : forall (C : Type),
        map Batch_DTM id = @id (Batch_DTM C).
    Proof.
      intros. ext s. induction s.
      - easy.
      - unfold id in *. destruct p.
        now rewrite <- IHs at 2.
    Qed.

    Lemma map_map_Batch_DTM : forall (C D E : Type) (f : C -> D) (g : D -> E),
        map Batch_DTM g ∘ map Batch_DTM f = map Batch_DTM (g ∘ f).
    Proof.
      intros. unfold compose. ext s. generalize dependent E.
      generalize dependent D. induction s.
      - easy.
      - intros. destruct p. cbn. fequal.
        apply IHs.
    Qed.

    #[export] Instance Functor_Batch_DTM : Functor Batch_DTM :=
      {| fun_map_id := map_id_Batch_DTM;
        fun_map_map := map_map_Batch_DTM;
      |}.

    (** ** Applicative Instance *)
    (******************************************************************************)
    #[export] Instance Pure_Batch_DTM : Pure Batch_DTM :=
      fun (C : Type) (c : C) => Done C c.

    Fixpoint mult_Batch_DTM `(jc : Batch_DTM C) `(jd : Batch_DTM D) : Batch_DTM (C * D) :=
      match jd with
      | Done _ d => map Batch_DTM (fun (c : C) => (c, d)) jc
      | Step _ rest (pair w a) =>
          Step (C * D) (map Batch_DTM strength_arrow (mult_Batch_DTM jc rest)) (pair w a)
      end.

    #[export] Instance Mult_Batch_DTM : Mult Batch_DTM :=
      fun C D '(c, d) => mult_Batch_DTM c d.

    #[local] Infix "⧆2" := (Step _) (at level 51, left associativity) : tealeaves_scope.

    Lemma mult_Batch_DTM_rw1 : forall `(a : A) `(b : B),
        Done _ a ⊗ Done _ b = Done _ (a, b).
    Proof.
      easy.
    Qed.

    Lemma mult_Batch_DTM_rw2 : forall `(d : D) `(jc : Batch_DTM C),
        jc ⊗ Done D d = map Batch_DTM (pair_right d) jc.
    Proof.
      intros. induction jc; easy.
    Qed.

    Lemma mult_Batch_DTM_rw3 : forall `(d : D) `(jc : Batch_DTM C),
        Done D d ⊗ jc = map Batch_DTM (pair d) jc.
    Proof.
      induction jc.
      - easy.
      - destruct p. cbn; change (mult_Batch_DTM ?x ?y) with (x ⊗ y).
        fequal. rewrite IHjc. compose near jc on left.
        now rewrite (fun_map_map Batch_DTM).
    Qed.

    Lemma mult_Batch_DTM_rw4 : forall (w : W) (a : A) `(jc : @Batch_DTM (T B -> C)) `(d : D),
        (jc ⧆2 (w, a)) ⊗ Done D d = map Batch_DTM (costrength_arrow ∘ pair_right d) jc ⧆2 (w, a).
    Proof.
      easy.
    Qed.

    Lemma mult_Batch_DTM_rw5 : forall (w : W) (a : A) `(jc : @Batch_DTM (T B -> C)) `(d : D),
        Done D d ⊗ (jc ⧆2 (w, a)) = map Batch_DTM (strength_arrow ∘ pair d) jc ⧆2 (w, a).
    Proof.
      intros. cbn. change (mult_Batch_DTM ?x ?y) with (x ⊗ y) in *.
      fequal. rewrite (mult_Batch_DTM_rw3 d). compose near jc on left.
      now rewrite (fun_map_map Batch_DTM).
    Qed.

    Lemma mult_Batch_DTM_rw6 :
      forall (w1 w2 : W) (a1 a2 : A)
        `(jc : Batch_DTM (T B -> C)) `(jd : Batch_DTM (T B -> D)),
        (jc ⧆2 (w1, a1)) ⊗ (jd ⧆2 (w2, a2)) =
          map Batch_DTM strength_arrow ((jc ⧆2 (w1, a1)) ⊗ jd) ⧆2 (w2, a2).
    Proof.
      reflexivity.
    Qed.

    Lemma app_pure_natural_Batch_DTM : forall (C D : Type) (f : C -> D) (x : C),
        map Batch_DTM f (pure Batch_DTM x) = pure Batch_DTM (f x).
    Proof.
      easy.
    Qed.

    Lemma app_mult_natural_Batch_DTM1 : forall (C D E : Type) (f : C -> D) (x : Batch_DTM C) (y : Batch_DTM E),
        map Batch_DTM f x ⊗ y = map Batch_DTM (map_fst f) (x ⊗ y).
    Proof.
      intros. generalize dependent E. induction y.
      - intros; cbn. compose near x.
        now do 2 rewrite (fun_map_map Batch_DTM).
      - destruct p. cbn; change (mult_Batch_DTM ?x ?y) with (x ⊗ y).
        rewrite IHy. compose near (x ⊗ y).
        do 2 rewrite (fun_map_map Batch_DTM). do 2 fequal.
        now ext [? ?].
    Qed.

    Lemma app_mult_natural_Batch_DTM2 : forall (A B D : Type) (g : B -> D) (x : Batch_DTM A) (y : Batch_DTM B),
        x ⊗ map Batch_DTM g y = map Batch_DTM (map_snd g) (x ⊗ y).
    Proof.
      intros. generalize dependent D. induction y as [ANY any | ANY rest IH [w a]].
      - intros; cbn. compose near x on right. now rewrite (fun_map_map Batch_DTM).
      - intros; cbn. fequal.
        change (mult_Batch_DTM ?jx ?jy) with (jx ⊗ jy).
        rewrite IH. compose near (x ⊗ rest).
        do 2 rewrite (fun_map_map Batch_DTM). fequal.
        now ext [a' mk].
    Qed.

    Lemma app_mult_natural_Batch_DTM : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : Batch_DTM A) (y : Batch_DTM B),
        map Batch_DTM f x ⊗ map Batch_DTM g y = map Batch_DTM (map_tensor f g) (x ⊗ y).
    Proof.
      intros. rewrite app_mult_natural_Batch_DTM1, app_mult_natural_Batch_DTM2.
      compose near (x ⊗ y) on left. rewrite (fun_map_map Batch_DTM). fequal.
      now ext [a b].
    Qed.

    Lemma app_assoc_Batch_DTM : forall (A B C : Type) (x : Batch_DTM A) (y : Batch_DTM B) (z : Batch_DTM C),
        map Batch_DTM associator ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
    Proof.
      intros. induction z as [ANY any | ANY rest IH [w a]].
      - do 2 rewrite mult_Batch_DTM_rw2.
        rewrite (app_mult_natural_Batch_DTM2). compose near (x ⊗ y) on left.
        now rewrite (fun_map_map Batch_DTM).
      - cbn. repeat change (mult_Batch_DTM ?jx ?jy) with (jx ⊗ jy).
        fequal. rewrite (app_mult_natural_Batch_DTM2).
        rewrite <- IH. compose near (x ⊗ y ⊗ rest).
        do 2 rewrite (fun_map_map Batch_DTM).
        compose near (x ⊗ y ⊗ rest) on right.
        rewrite (fun_map_map Batch_DTM).
        fequal. now ext [[? ?] ?].
    Qed.

    Lemma app_unital_l_Batch_DTM : forall (A : Type) (x : Batch_DTM A),
        map Batch_DTM left_unitor (pure Batch_DTM tt ⊗ x) = x.
    Proof.
      intros. induction x as [ANY any | ANY rest IH [w a]].
      - easy.
      - cbn. change (mult_Batch_DTM ?jx ?jy) with (jx ⊗ jy).
        fequal. compose near (pure Batch_DTM tt ⊗ rest).
        rewrite (fun_map_map Batch_DTM).
        rewrite <- IH. repeat fequal. auto.
    Qed.

    Lemma app_unital_r_Batch_DTM : forall (A : Type) (x : Batch_DTM A),
        map Batch_DTM right_unitor (x ⊗ pure Batch_DTM tt) = x.
    Proof.
      intros. induction x as [ANY any | ANY rest IH [w a]].
      - easy.
      - cbn in *. fequal. rewrite <- IH at 2.
        compose near rest. now do 2 rewrite (fun_map_map Batch_DTM).
    Qed.

    Lemma app_mult_pure_Batch_DTM : forall (A B : Type) (a : A) (b : B),
        pure Batch_DTM a ⊗ pure Batch_DTM b = pure Batch_DTM (a, b).
    Proof.
      intros. easy.
    Qed.

    #[export, program] Instance App_Path : Applicative Batch_DTM.

    Next Obligation. apply app_mult_natural_Batch_DTM. Qed.
    Next Obligation. apply app_assoc_Batch_DTM. Qed.
    Next Obligation. apply app_unital_l_Batch_DTM. Qed.
    Next Obligation. apply app_unital_r_Batch_DTM. Qed.

  End Batch_DTM.

  Arguments Step {T}%function_scope {W A B}%type_scope [C]%type_scope _ _.

  (** ** Notations *)
  (******************************************************************************)
  Module Notations.

    Infix "⧆2" := Step (at level 51, left associativity) : tealeaves_scope.

  End Notations.

  Import Notations.

  (** *** Examples of operations *)
  (******************************************************************************)
  Section demo.

    Context
      (T : Type -> Type)
        (A B C A W : Type)
        (a1 a2 : A) (b1 b2 b3 : B)
        (w1 w2 w3 w4 : W)
        (c1 c2 c3 c4 : C)
        (mk1 : C -> X) (mk2 : C -> C -> X) (mk0 : X).

  (*
  Check Done a1 ⊗ Done a2 : @Batch_DTM _ T W False False (A * A).
  Compute Done a1 ⊗ Done a2.
  Compute Done a1 ⊗ (Done mk1 ⧆2 (w1, c1)).
  Compute (Done mk1 ⧆2 (w1, c1)) ⊗ (Done mk1 ⧆2 (w2, c2)).
  Compute (Done mk2 ⧆2 (w1, c1) ⧆2 (w2, c2)) ⊗ (Done mk1 ⧆2 (w3, c3)).
   *)

  End demo.

  (** ** Functoriality of [Batch_DTM] *)
  (******************************************************************************)
  Section functoriality_Batch_DTM.

    Context
      (T : Type -> Type).

    Fixpoint mapfst_Batch_DTM {A1 A2 B C} (f : A1 -> A2) `(j : @Batch_DTM T W A1 B C) : @Batch_DTM T W A2 B C :=
      match j with
      | Done _ a => Done _ a
      | Step rest p => Step (mapfst_Batch_DTM f rest) (map_snd f p)
      end.

  End functoriality_Batch_DTM.

  (** * The <<runBatch_DTM>> operation *)
  (******************************************************************************)
  Fixpoint runBatch_DTM
    (T : Type -> Type) {W A B : Type} (F : Type -> Type)
    `{Map F} `{Mult F} `{Pure F}
    (ϕ : W * A -> F (T B))
    `(j : @Batch_DTM T W A B C) : F C :=
    match j with
    | Done _ a => pure F a
    | @Step _ _ _ _ _ rest (pair w a) => runBatch_DTM T F ϕ rest <⋆> ϕ (w, a)
    end.

  Section runBatch_DTM_rw.

    Context
      (T : Type -> Type).

    Context
      (A B C W : Type)
        `{Applicative F}
        (f : W * A -> F (T B)).

    Lemma runBatch_DTM_rw1 (c : C) :
      runBatch_DTM T F f (Done _ c) = pure F c.
    Proof.
      reflexivity.
    Qed.

    Lemma runBatch_DTM_rw2 (w : W) (a : A) (rest : Batch_DTM (T B -> C)) :
      runBatch_DTM T F  f (rest ⧆2 (w, a)) = runBatch_DTM T F  f rest <⋆> f (w, a).
    Proof.
      reflexivity.
    Qed.

  End runBatch_DTM_rw.

  (** ** Naturality of of <<runBatch_DTM>> *)
  (******************************************************************************)
  Section runBatch_DTM_naturality.

    Context
      (T : Type -> Type)
        `{Applicative F}.

    Context
      (A B C D W : Type)
        `{Applicative F}
        (ϕ : W * A -> F (T B)).

    Lemma natural_runBatch_DTM (f : C -> D) (j : @Batch_DTM T W A B C) :
      map F f (runBatch_DTM T F  ϕ j) = runBatch_DTM T F  ϕ (map Batch_DTM f j).
    Proof.
      generalize dependent D. induction j; intros.
      - cbn. now rewrite (app_pure_natural F).
      - destruct p. cbn. rewrite map_ap. fequal.
        now rewrite IHj.
    Qed.

  End runBatch_DTM_naturality.

  (** ** <<runBatch_DTM>> is an applicative morphism **)
  (******************************************************************************)
  Section runBatch_DTM_morphism.

    Context
      (T : Type -> Type)
        (A B W : Type)
        `{Applicative F}
        (f : W * A -> F (T B)).

    Lemma appmor_pure_runBatch_DTM : forall (C : Type) (c : C),
        runBatch_DTM T F  f (pure Batch_DTM c) = pure F c.
    Proof.
      easy.
    Qed.

    Lemma appmor_mult_runBatch_DTM : forall (C D : Type) (x : Batch_DTM C) (y : Batch_DTM D),
        runBatch_DTM T F  f (x ⊗ y) = runBatch_DTM T F  f x ⊗ runBatch_DTM T F  f y.
    Proof.
      intros. generalize dependent x. induction y.
      - intros. rewrite mult_Batch_DTM_rw2.
        rewrite runBatch_DTM_rw1. rewrite triangle_4.
        rewrite natural_runBatch_DTM; auto.
      - intros. destruct p. rewrite runBatch_DTM_rw2.
        unfold ap. rewrite (app_mult_natural_r F).
        rewrite <- (app_assoc F).
        rewrite <- IHy. clear IHy.
        compose near (runBatch_DTM T F f (x ⊗ y) ⊗ f (w, a)).
        rewrite (fun_map_map F).
        cbn. unfold ap. change (mult_Batch_DTM ?jx ?jy) with (jx ⊗ jy).
        rewrite <- natural_runBatch_DTM; auto.
        rewrite (app_mult_natural_l F).
        compose near (runBatch_DTM T F f (x ⊗ y) ⊗ f (w, a)) on left.
        rewrite (fun_map_map F). fequal. now ext [[? ?] ?].
    Qed.

    #[export] Instance Morphism_store_fold: ApplicativeMorphism Batch_DTM F (@runBatch_DTM T W A B F _ _ _ f).
    Proof.
      constructor; try typeclasses eauto.
      - intros. now rewrite natural_runBatch_DTM.
      - intros. easy.
      - intros. apply appmor_mult_runBatch_DTM.
    Qed.

  End runBatch_DTM_morphism.

  (** ** <<runBatch_DTM>> commutes with applicative morphisms **)
  (******************************************************************************)
  Section runBatch_DTM_morphism.

    Context
      (T : Type -> Type)
      (W A B C : Type)
      `{Applicative F}
      `{Applicative G}
      `{! ApplicativeMorphism F G ψ}
      (f : W * A -> F (T B)).

    Lemma runBatch_DTM_morphism `(j : @Batch_DTM T W A B C) :
      @ψ C (runBatch_DTM T F f j) = runBatch_DTM T G (@ψ (T B) ∘ f) j.
    Proof.
      induction j.
      - cbn. now rewrite (appmor_pure F G).
      - destruct p. cbn. rewrite ap_morphism_1.
        now rewrite IHj.
    Qed.

  End runBatch_DTM_morphism.

End Batch_DTM.
