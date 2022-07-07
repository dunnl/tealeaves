From Tealeaves Require Export
     Classes.Monoid
     Classes.Applicative
     Functors.Constant.

From Tealeaves.Multisorted Require Export
     Classes.Functor
     Classes.DTM.

Import Monoid.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Set Implicit Arguments.

(* TODO Move me *)
Definition eval `(a : A) `(f : A -> B) := f a.
Definition costrength_arr `(p : (A -> B) * C) : A -> B * C := fun a => (fst p a, snd p).
Definition strength_arr `(p : A * (B -> C)) : B -> A * C := fun b => (fst p, snd p b).
Definition pair_right {A B} : B -> A -> A * B := fun b a => (a, b).

(** * The <<Schedule>> functor *)
(******************************************************************************)
Section Schedule.

  Context
    `{ix : Index}
    {T : K -> Type -> Type}
    {W A B : Type}.

  Inductive Schedule C : Type :=
  | Go : C -> Schedule C
  | Ap : forall (k : K), Schedule (T k B -> C) -> W * A -> Schedule C.

  Fixpoint fmap_Schedule `{f : C -> D} `(c : Schedule C) : Schedule D :=
    match c with
    | Go c => Go (f c)
    | @Ap _ k rest (pair w a) =>
      Ap (@fmap_Schedule (T k B -> C) (T k B -> D) (compose f) rest) (w, a)
    end.

  #[global] Instance Fmap_Schedule : Fmap Schedule := @fmap_Schedule.

  Lemma fmap_id_Schedule : forall (C : Type),
      fmap Schedule id = @id (Schedule C).
  Proof.
    intros. ext s. induction s.
    - easy.
    - unfold id in *. destruct p.
      now rewrite <- IHs at 2.
  Qed.

  Lemma fmap_fmap_Schedule : forall (C D E : Type) (f : C -> D) (g : D -> E),
      fmap Schedule g ∘ fmap Schedule f = fmap Schedule (g ∘ f).
  Proof.
    intros. unfold compose. ext s. generalize dependent E.
    generalize dependent D. induction s.
    - easy.
    - intros. destruct p. cbn. fequal.
      apply IHs.
  Qed.

  #[global, program] Instance Functor_Schedule : Functor Schedule :=
    {| fun_fmap_id := fmap_id_Schedule;
       fun_fmap_fmap := fmap_fmap_Schedule;
    |}.

  (** ** Applicative Instance *)
  (******************************************************************************)
  #[global] Instance Pure_Schedule : Pure Schedule :=
    fun (C : Type) (c : C) => Go c.

  Fixpoint mult_Schedule `(jc : Schedule C) `(jd : Schedule D) : Schedule (C * D) :=
    match jd with
    | Go d => fmap Schedule (fun (c : C) => (c, d)) jc
    | Ap rest (pair w a) =>
      Ap (fmap Schedule strength_arr (mult_Schedule jc rest)) (pair w a)
    end.

  #[global] Instance Mult_Schedule : Mult Schedule :=
    fun C D '(c, d) => mult_Schedule c d.

  #[local] Infix "⧆" := Ap (at level 51, left associativity) : tealeaves_scope.
  Lemma mult_Schedule_rw1 : forall `(a : A) `(b : B),
      Go a ⊗ Go b = Go (a, b).
  Proof.
    easy.
  Qed.

  Lemma mult_Schedule_rw2 : forall `(d : D) `(jc : Schedule C),
      jc ⊗ Go d = fmap Schedule (pair_right d) jc.
  Proof.
    intros. induction jc; easy.
  Qed.

  Lemma mult_Schedule_rw3 : forall `(d : D) `(jc : Schedule C),
      Go d ⊗ jc = fmap Schedule (pair d) jc.
  Proof.
    induction jc.
    - easy.
    - destruct p. cbn; change (mult_Schedule ?x ?y) with (x ⊗ y).
      fequal. rewrite IHjc. compose near jc on left.
      now rewrite (fun_fmap_fmap Schedule).
  Qed.

  Lemma mult_Schedule_rw4 : forall (w : W) (a : A) (k : K) `(jc : @Schedule (T k B -> C)) `(d : D),
      (jc ⧆ (w, a)) ⊗ Go d = fmap Schedule (costrength_arr ∘ pair_right d) jc ⧆ (w, a).
  Proof.
    easy.
  Qed.

  Lemma mult_Schedule_rw5 : forall (w : W) (a : A) (k : K) `(jc : @Schedule (T k B -> C)) `(d : D),
      Go d ⊗ (jc ⧆ (w, a)) = fmap Schedule (strength_arr ∘ pair d) jc ⧆ (w, a).
  Proof.
    intros. cbn. change (mult_Schedule ?x ?y) with (x ⊗ y) in *.
    fequal. rewrite (mult_Schedule_rw3 d). compose near jc on left.
    now rewrite (fun_fmap_fmap Schedule).
  Qed.

  Lemma mult_Schedule_rw6 :
    forall (w1 w2 : W) (a1 a2 : A) (k : K)
      `(jc : Schedule (T k B -> C)) `(jd : Schedule (T k B -> D)),
      (jc ⧆ (w1, a1)) ⊗ (jd ⧆ (w2, a2)) =
      fmap Schedule strength_arr ((jc ⧆ (w1, a1)) ⊗ jd) ⧆ (w2, a2).
  Proof.
    reflexivity.
  Qed.

  Lemma app_pure_natural_Schedule : forall (C D : Type) (f : C -> D) (x : C),
      fmap Schedule f (pure Schedule x) = pure Schedule (f x).
  Proof.
    easy.
  Qed.

  Lemma app_mult_natural_Schedule1 : forall (C D E : Type) (f : C -> D) (x : Schedule C) (y : Schedule E),
      fmap Schedule f x ⊗ y = fmap Schedule (map_fst f) (x ⊗ y).
  Proof.
    intros. generalize dependent E. induction y.
    - intros; cbn. compose near x.
      now do 2 rewrite (fun_fmap_fmap Schedule).
    - destruct p. cbn; change (mult_Schedule ?x ?y) with (x ⊗ y).
      rewrite IHy. compose near (x ⊗ y).
      do 2 rewrite (fun_fmap_fmap Schedule). do 2 fequal.
      now ext [? ?].
  Qed.

  Lemma app_mult_natural_Schedule2 : forall (A B D : Type) (g : B -> D) (x : Schedule A) (y : Schedule B),
      x ⊗ fmap Schedule g y = fmap Schedule (map_snd g) (x ⊗ y).
  Proof.
    intros. generalize dependent D. induction y as [ANY any | ANY k rest IH [w a]].
    - intros; cbn. compose near x on right. now rewrite (fun_fmap_fmap Schedule).
    - intros; cbn. fequal.
      change (mult_Schedule ?jx ?jy) with (jx ⊗ jy).
      rewrite IH. compose near (x ⊗ rest).
      do 2 rewrite (fun_fmap_fmap Schedule). fequal.
      now ext [a' mk].
  Qed.

  Lemma app_mult_natural_Schedule : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : Schedule A) (y : Schedule B),
      fmap Schedule f x ⊗ fmap Schedule g y = fmap Schedule (map_tensor f g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_Schedule1, app_mult_natural_Schedule2.
    compose near (x ⊗ y) on left. rewrite (fun_fmap_fmap Schedule). fequal.
    now ext [a b].
  Qed.

  Lemma app_assoc_Schedule : forall (A B C : Type) (x : Schedule A) (y : Schedule B) (z : Schedule C),
      fmap Schedule associator ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. induction z as [ANY any | ANY k rest IH [w a]].
    - do 2 rewrite mult_Schedule_rw2.
      rewrite (app_mult_natural_Schedule2). compose near (x ⊗ y) on left.
      now rewrite (fun_fmap_fmap Schedule).
    - cbn. repeat change (mult_Schedule ?jx ?jy) with (jx ⊗ jy).
      fequal. rewrite (app_mult_natural_Schedule2).
      rewrite <- IH. compose near (x ⊗ y ⊗ rest).
      do 2 rewrite (fun_fmap_fmap Schedule).
      compose near (x ⊗ y ⊗ rest) on right.
      rewrite (fun_fmap_fmap Schedule).
      fequal. now ext [[? ?] ?].
  Qed.

  Lemma app_unital_l_Schedule : forall (A : Type) (x : Schedule A),
      fmap Schedule left_unitor (pure Schedule tt ⊗ x) = x.
  Proof.
    intros. induction x as [ANY any | ANY k rest IH [w a]].
    - easy.
    - cbn. change (mult_Schedule ?jx ?jy) with (jx ⊗ jy).
      fequal. compose near (pure Schedule tt ⊗ rest).
      rewrite (fun_fmap_fmap Schedule).
      rewrite <- IH. repeat fequal. auto.
  Qed.

  Lemma app_unital_r_Schedule : forall (A : Type) (x : Schedule A),
      fmap Schedule right_unitor (x ⊗ pure Schedule tt) = x.
  Proof.
    intros. induction x as [ANY any | ANY k rest IH [w a]].
    - easy.
    - cbn in *. fequal. rewrite <- IH at 2.
      compose near rest. now do 2 rewrite (fun_fmap_fmap Schedule).
  Qed.

  Lemma app_mult_pure_Schedule : forall (A B : Type) (a : A) (b : B),
      pure Schedule a ⊗ pure Schedule b = pure Schedule (a, b).
  Proof.
    intros. easy.
  Qed.

  #[global, program] Instance App_Path : Applicative Schedule.

  Next Obligation. apply app_mult_natural_Schedule. Qed.
  Next Obligation. apply app_assoc_Schedule. Qed.
  Next Obligation. apply app_unital_l_Schedule. Qed.
  Next Obligation. apply app_unital_r_Schedule. Qed.

End Schedule.

Arguments Ap {ix} {T}%function_scope {W A B}%type_scope [C]%type_scope {k} _ _.

(** ** Notations *)
(******************************************************************************)
Module Notations.

  Infix "⧆" := Ap (at level 51, left associativity) : tealeaves_scope.
End Notations.

Import Notations.

(** *** Examples of operations *)
(******************************************************************************)
Section demo.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    (A B C X : Type)
    (a1 a2 : A) (b1 b2 b3 : B)
    (w1 w2 w3 w4 : W)
    (c1 c2 c3 c4 : C)
    (mk1 : C -> X) (mk2 : C -> C -> X) (mk0 : X).

  Check Go a1 ⊗ Go a2 : @Schedule _ T W False False (A * A).
  Compute Go a1 ⊗ Go a2.
  Compute Go a1 ⊗ (Go mk1 ⧆ (w1, c1)).
  Compute (Go mk1 ⧆ (w1, c1)) ⊗ (Go mk1 ⧆ (w2, c2)).
  Compute (Go mk2 ⧆ (w1, c1) ⧆ (w2, c2)) ⊗ (Go mk1 ⧆ (w3, c3)).
End demo.

(** ** Functoriality of [Schedule] *)
(******************************************************************************)
Section functoriality_Schedule.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Fixpoint mapfst_Schedule {A1 A2 B C} (f : A1 -> A2) `(j : @Schedule _ T W A1 B C) : @Schedule _ T W A2 B C :=
    match j with
    | Go a => Go a
    | Ap rest p => Ap (mapfst_Schedule f rest) (map_snd f p)
    end.

End functoriality_Schedule.

(** * The <<runSchedule>> operation *)
(******************************************************************************)
Fixpoint runSchedule
         {ix : Index} {T : K -> Type -> Type} {W A B : Type} {F : Type -> Type}
         `{Fmap F} `{Mult F} `{Pure F}
         (ϕ : forall (k : K), W * A -> F (T k B))
         `(j : @Schedule ix T W A B C) : F C :=
  match j with
  | Go a => pure F a
  | @Ap _ _ _ _ _ _ k rest (pair w a) => runSchedule ϕ rest <⋆> ϕ k (w, a)
  end.

Section runSchedule_rw.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Context
    (A B C : Type)
    `{Applicative F}
    (f : forall k, W * A -> F (T k B)).

  Lemma runSchedule_rw1 (c : C) :
    runSchedule f (Go c) = pure F c.
  Proof.
    reflexivity.
  Qed.

  Lemma runSchedule_rw2 (k : K) (w : W) (a : A) (rest : Schedule (T k B -> C)) :
    runSchedule f (rest ⧆ (w, a)) = runSchedule f rest <⋆> f k (w, a).
  Proof.
    reflexivity.
  Qed.

End runSchedule_rw.

(** ** Naturality of of <<runSchedule>> *)
(******************************************************************************)
Section runSchedule_naturality.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    `{Applicative F}.

  Context
    (A B C D : Type)
    `{Applicative F}
    (ϕ : forall k, W * A -> F (T k B)).

  Lemma natural_runSchedule (f : C -> D) (j : @Schedule _ T W A B C) :
    fmap F f (runSchedule ϕ j) = runSchedule ϕ (fmap Schedule f j).
  Proof.
    generalize dependent D. induction j; intros.
    - cbn. now rewrite (app_pure_natural F).
    - destruct p. cbn. rewrite ap6. fequal.
      now rewrite IHj.
  Qed.

End runSchedule_naturality.

(** ** <<runSchedule>> is an applicative morphism **)
(******************************************************************************)
Section runSchedule_morphism.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Context
    (A B : Type)
    `{Applicative F}
    (f : forall k, W * A -> F (T k B)).

  Lemma appmor_pure_runSchedule : forall (C : Type) (c : C),
      runSchedule f (pure Schedule c) = pure F c.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runSchedule : forall (C D : Type) (x : Schedule C) (y : Schedule D),
      runSchedule f (x ⊗ y) = runSchedule f x ⊗ runSchedule f y.
  Proof.
    intros. generalize dependent x. induction y.
    - intros. rewrite mult_Schedule_rw2.
      rewrite runSchedule_rw1. rewrite triangle_4.
      rewrite natural_runSchedule; auto.
    - intros. destruct p. rewrite runSchedule_rw2.
      unfold ap. rewrite (app_mult_natural_r F).
      rewrite <- (app_assoc F).
      rewrite <- IHy. clear IHy.
      compose near (runSchedule f (x ⊗ y) ⊗ f k (w, a)).
      rewrite (fun_fmap_fmap F).
      cbn. unfold ap. change (mult_Schedule ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runSchedule; auto.
      rewrite (app_mult_natural_l F).
      compose near (runSchedule f (x ⊗ y) ⊗ f k (w, a)) on left.
      rewrite (fun_fmap_fmap F). fequal. now ext [[? ?] ?].
  Qed.

  #[global] Instance Morphism_store_fold: ApplicativeMorphism Schedule F (@runSchedule _ T W A B F _ _ _ f).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runSchedule.
    - intros. easy.
    - intros. apply appmor_mult_runSchedule.
  Qed.

End runSchedule_morphism.

(** ** <<runSchedule>> commuts with applicative morphisms **)
(******************************************************************************)
Section runSchedule_morphism.


  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    (A B C : Type)
    `{Applicative F}
    `{Applicative G}
    `{! ApplicativeMorphism F G ψ}
    (f : forall k, W * A -> F (T k B)).

  Lemma runSchedule_morphism `(j : @Schedule _ T W A B C) :
    @ψ C (runSchedule f j) = runSchedule (fun k => @ψ (T k B) ∘ f k) j.
  Proof.
    induction j.
    - cbn. now rewrite (appmor_pure F G).
    - destruct p. cbn. rewrite ap_morphism_1.
      now rewrite IHj.
  Qed.

End runSchedule_morphism.
