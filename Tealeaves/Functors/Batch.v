From Tealeaves Require Export
     Classes.Monoid
     Classes.Applicative
     Functors.Store
     Functors.Constant
     Functors.Maybe.

Import Monoid.Notations.
Import Applicative.Notations.
#[local] Open Scope tealeaves_scope.

#[local] Set Implicit Arguments.

(** * The [Batch] idiom *)
(******************************************************************************)
Section fix_parameters.

  Context {X Y : Type}.

  Inductive Batch A : Type :=
  | Go : A -> Batch A
  | Ap : Batch (Y -> A) -> X -> Batch A.

  Fixpoint fmap_Batch `{f : A -> B} (c : Batch A) : Batch B :=
    match c with
    | Go a => Go (f a)
    | Ap rest i1 =>
      Ap (@fmap_Batch (Y -> A) (Y -> B) (compose f) rest) i1
    end.

  #[global] Instance Fmap_Batch : Fmap Batch := @fmap_Batch.

  #[global, program] Instance Functor_Batch : Functor Batch.

  Next Obligation.
    ext j. induction j. easy.
    cbn; unfold id; now fequal.
  Qed.

  Next Obligation.
    ext j. unfold compose. generalize dependent C.
    generalize dependent B. induction j.
    - easy.
    - intros. cbn. fequal. unfold compose.
      now rewrite  (@IHj (Y -> B) _ (Y -> C)).
  Qed.

End fix_parameters.

Module Notations.

  Infix "⧆" := Ap (at level 51, left associativity) : tealeaves_scope.
End Notations.

Import Notations.

(** ** Applicative Instance *)
(******************************************************************************)
Section Applicative_Batch.

  Context
    {X Y : Type}.

  #[global] Instance Pure_Batch : Pure (@Batch X Y) :=
    fun (A : Type) (a : A) => Go a.

  Fixpoint mult_Batch `(ja : Batch A) `(jb : Batch B) : @Batch X Y (A * B) :=
    match jb with
    | Go b => fmap Batch (fun (a : A) => (a, b)) ja
    | Ap rest x1 =>
      Ap (fmap Batch strength_arrow (mult_Batch ja rest)) x1
    end.

  #[global] Instance Mult_Batch : Mult (@Batch X Y) :=
    fun A B '(x, y) => mult_Batch x y.

  Lemma mult_Batch_rw1 : forall `(a : A) `(b : B),
      Go a ⊗ Go b = (Go (a, b) : @Batch X Y (A * B)).
  Proof.
    easy.
  Qed.

  Lemma mult_Batch_rw2 : forall `(b : B) `(ja : Batch A),
      ja ⊗ Go b = fmap Batch (pair_right b) ja.
  Proof.
    intros. induction ja; easy.
  Qed.

  Lemma mult_Batch_rw3 : forall `(jb : Batch B) `(a : A),
      Go a ⊗ jb = fmap Batch (pair a) jb.
  Proof.
    induction jb.
    - easy.
    - intros. cbn in *; change (mult_Batch ?x ?y) with (x ⊗ y) in *.
      fequal. cbn in IHjb; change (mult_Batch ?x ?y) with (x ⊗ y) in *.
      rewrite IHjb. compose near jb on left. now rewrite (fun_fmap_fmap Batch).
  Qed.

  Lemma mult_Batch_rw4 : forall (x : X) `(ja : @Batch X Y (Y -> A)) `(b : B),
      (ja ⧆ x) ⊗ Go b =
      fmap Batch (costrength_arrow ∘ pair_right b) ja ⧆ x.
  Proof.
    easy.
  Qed.

  Lemma mult_Batch_rw5 : forall `(jb : @Batch X Y (Y -> B)) `(a : A) (x : X),
      Go a ⊗ (jb ⧆ x) = fmap Batch (strength_arrow ∘ pair a) jb ⧆ x.
  Proof.
    cbn. change (mult_Batch ?x ?y) with (x ⊗ y) in *. intros.
    fequal. rewrite (mult_Batch_rw3). compose near jb on left.
    now rewrite (fun_fmap_fmap Batch).
  Qed.

  Lemma mult_Batch_rw6 : forall (x1 x2 : X) `(ja : Batch (Y -> A)) `(jb : Batch (Y -> B)),
      (ja ⧆ x1) ⊗ (jb ⧆ x2) =
      fmap Batch strength_arrow ((ja ⧆ x1) ⊗ jb) ⧆ x2.
  Proof.
    reflexivity.
  Qed.

  Lemma app_pure_natural_Batch : forall (A B : Type) (f : A -> B) (x : A),
      fmap Batch f (pure Batch x) = pure Batch (f x).
  Proof.
    easy.
  Qed.

  Lemma app_mult_natural_Batch1 : forall (A B C : Type) (f : A -> C) (x : Batch A) (y : Batch B),
      fmap Batch f x ⊗ y = fmap Batch (map_fst f) (x ⊗ y).
  Proof.
    intros. generalize dependent C. induction y.
    - intros; cbn. compose near x.
      now do 2 rewrite (fun_fmap_fmap Batch).
    - intros; cbn.
      change (mult_Batch ?x ?y) with (x ⊗ y) in *.
      rewrite IHy. compose near (x ⊗ y).
      do 2  rewrite (fun_fmap_fmap Batch). do 2 fequal.
      now ext [? ?].
  Qed.

  Lemma app_mult_natural_Batch2 : forall (A B D : Type) (g : B -> D) (x : Batch A) (y : Batch B),
      x ⊗ fmap Batch g y = fmap Batch (map_snd g) (x ⊗ y).
  Proof.
    intros. generalize dependent D. induction y as [ANY any | ANY rest IH x'].
    - intros; cbn. compose near x on right. now rewrite (fun_fmap_fmap Batch).
    - intros; cbn. fequal.
      change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite IH. compose near (x ⊗ rest).
      do 2 rewrite (fun_fmap_fmap Batch). fequal.
      now ext [a mk].
  Qed.

  Lemma app_mult_natural_Batch : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : Batch A) (y : Batch B),
      fmap Batch f x ⊗ fmap Batch g y = fmap Batch (map_tensor f g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_Batch1, app_mult_natural_Batch2.
    compose near (x ⊗ y) on left. rewrite (fun_fmap_fmap Batch). fequal.
    now ext [a b].
  Qed.

  Lemma app_assoc_Batch : forall (A B C : Type) (x : Batch A) (y : Batch B) (z : Batch C),
      fmap Batch associator ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. induction z.
    - do 2 rewrite mult_Batch_rw2.
      rewrite (app_mult_natural_Batch2). compose near (x ⊗ y) on left.
      now rewrite (fun_fmap_fmap Batch).
    - cbn. repeat change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      fequal.
      rewrite (app_mult_natural_Batch2).
      rewrite <- IHz. compose near (x ⊗ y ⊗ z).
      do 2 rewrite (fun_fmap_fmap Batch).
      compose near (x ⊗ y ⊗ z) on right.
      rewrite (fun_fmap_fmap Batch).
      fequal. now ext [[? ?] ?].
  Qed.

  Lemma app_unital_l_Batch : forall (A : Type) (x : Batch A),
      fmap Batch left_unitor (pure Batch tt ⊗ x) = x.
  Proof.
    intros. induction x.
    - easy.
    - cbn. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      fequal. compose near (pure Batch tt ⊗ x).
      rewrite (fun_fmap_fmap Batch).
      rewrite <- IHx. repeat fequal. auto.
  Qed.

  Lemma app_unital_r_Batch : forall (A : Type) (x : Batch A),
      fmap Batch right_unitor (x ⊗ pure Batch tt) = x.
  Proof.
    intros. induction x.
    - easy.
    - cbn in *. fequal. rewrite <- IHx at 2.
      compose near x. now do 2 rewrite (fun_fmap_fmap Batch).
  Qed.

  Lemma app_mult_pure_Batch : forall (A B : Type) (a : A) (b : B),
      pure Batch a ⊗ pure Batch b = pure Batch (a, b).
  Proof.
    intros. easy.
  Qed.

  #[global, program] Instance App_Path : Applicative Batch.

  Next Obligation. apply app_mult_natural_Batch. Qed.
  Next Obligation. apply app_assoc_Batch. Qed.
  Next Obligation. apply app_unital_l_Batch. Qed.
  Next Obligation. apply app_unital_r_Batch. Qed.

End Applicative_Batch.

(** *** Examples of operations *)
(******************************************************************************)
Section demo.

  Context
    (A B C X : Type)
    (a1 a2 : A) (b1 b2 b3 : B) (c1 c2 c3 c4 : C)
    (mk1 : C -> X) (mk2 : C -> C -> X) (mk0 : X).

  (*
  Check Go a1 ⊗ Go a2 : @Batch False False (A * A).
  Compute Go a1 ⊗ Go a2.
  Compute Go a1 ⊗ (Go mk1 ⧆ c1).
  Compute (Go mk1 ⧆ c1) ⊗ (Go mk1 ⧆ c2).
  Compute (Go mk2 ⧆ c1 ⧆ c2) ⊗ (Go mk1 ⧆ c3).
   *)

End demo.

(** ** Functoriality of [Batch] in all arguments *)
(******************************************************************************)
Section functoriality_Batch.

  Context
    {A B C : Type}.

  Fixpoint mapfst_Batch (f : A -> B) `(j : @Batch A C X) : @Batch B C X :=
    match j with
    | Go a => Go a
    | Ap rest a => Ap (mapfst_Batch f rest) (f a)
    end.

  Fixpoint mapsnd_Batch (f : A -> B) `(j : @Batch C B X) : @Batch C A X :=
    match j with
    | Go a => Go a
    | Ap rest c => Ap (fmap Batch (precompose f) (mapsnd_Batch f rest)) c
    end.

End functoriality_Batch.

Lemma mapfst_Batch1 {A B C X Y : Type} (f : A -> B) (g : X -> Y) (j : @Batch A C X) :
  mapfst_Batch f (fmap Batch g j) = fmap Batch g (mapfst_Batch f j).
Proof.
  generalize dependent Y.
  generalize dependent B.
  induction j.
  - easy.
  - intros. cbn. fequal. auto.
Qed.

Lemma mapsnd_Batch1 {A B C X Y : Type} (f : B -> C) (g : X -> Y) (j : @Batch A C X) :
  mapsnd_Batch f (fmap Batch g j) = fmap Batch g (mapsnd_Batch f j).
Proof.
  generalize dependent B.
  generalize dependent Y.
  induction j.
  - easy.
  - intros. cbn. fequal.
    rewrite IHj. compose near (mapsnd_Batch f j).
    do 2 rewrite (fun_fmap_fmap Batch).
    do 2 rewrite <- IHj.
    reflexivity.
Qed.

Lemma mapfst_mapsnd_Batch : forall {X} `(f : A -> B) `(g : O1 -> O2) `(j : @Batch A O2 X),
    mapfst_Batch f (mapsnd_Batch g j) = mapsnd_Batch g (mapfst_Batch f j).
Proof.
  intros. generalize dependent f. generalize dependent g.
  generalize dependent X. induction j.
  - reflexivity.
  - intros. cbn. fequal. rewrite mapfst_Batch1.
    now rewrite IHj.
Qed.

Lemma mapfst_Batch2 {A B C X Y : Type} (f : A -> B) (x : @Batch A C X) (y : @Batch A C Y) :
  mapfst_Batch f (x ⊗ y) = mapfst_Batch f x ⊗ mapfst_Batch f y.
Proof.
  generalize dependent x. induction y.
  - intros. cbn. now rewrite mapfst_Batch1.
  - cbn. fequal. change (mult_Batch ?x ?y) with (x ⊗ y) in *; intros.
    rewrite <- IHy. now rewrite mapfst_Batch1.
Qed.

Lemma mapfst_Batch3 {A B C X Y : Type} (f : A -> B) (x : @Batch A C (X -> Y)) (y : @Batch A C X) :
  mapfst_Batch f (x <⋆> y) = mapfst_Batch f x <⋆> mapfst_Batch f y.
Proof.
  unfold ap. rewrite mapfst_Batch1.
  now rewrite mapfst_Batch2.
Qed.

Lemma mapfst_Batch4 {A B X Y : Type} (f : A -> B) (t : X) :
  mapfst_Batch f (Go (Y := Y) t) = Go t.
Proof.
  reflexivity.
Qed.

Lemma mapfst_Batch5 {A B X : Type} (f : A -> B)  (a : A) (j : @Batch A B (B -> X)) :
  mapfst_Batch f (j ⧆ a) = mapfst_Batch f j ⧆ f a.
Proof.
  reflexivity.
Qed.

(** * <<Batch>> as a free applicative functor *)
(******************************************************************************)
Section free_alternate.

  Fixpoint runBatch `(ϕ : A -> F B) `{Fmap F}
           `{Mult F} `{Pure F}  {X : Type} (j : @Batch A B X) : F X :=
    match j with
    | Go a => pure F a
    | Ap rest i => runBatch ϕ rest <⋆> ϕ i
    end.

  Context
    `{Applicative F}
    `{A : Type, B : Type}
    (ϕ : A -> F B).

  Lemma runBatch_rw1 (X : Type) (x : X) :
    runBatch ϕ (Go x) = pure F x.
  Proof.
    reflexivity.
  Qed.

  Lemma runBatch_rw2 (a : A) (X : Type) (rest : @Batch A B (B -> X)) :
    runBatch ϕ (rest ⧆ a) = runBatch ϕ rest <⋆> ϕ a.
  Proof.
    reflexivity.
  Qed.

  Lemma natural_runBatch `(f : X -> Y) (j : @Batch A B X) :
    fmap F f (runBatch ϕ j) = runBatch ϕ (fmap Batch f j).
  Proof.
    generalize dependent Y. induction j; intros.
    - cbn. now rewrite (app_pure_natural F).
    - cbn. rewrite ap6. fequal. now rewrite IHj.
  Qed.

  #[global] Instance Natural_runBatch : Natural (@runBatch _ _ _ ϕ _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    introv. ext j. unfold compose. apply natural_runBatch.
  Qed.

  Lemma appmor_pure_runBatch : forall (A : Type) (a : A),
      runBatch ϕ (pure Batch a) = pure F a.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runBatch : forall {A B} (x : Batch A) (y : Batch B),
      runBatch ϕ (x ⊗ y) = runBatch ϕ x ⊗ runBatch ϕ y.
  Proof.
    intros. generalize dependent x. induction y as [ANY any | ANY rest IH x'].
    - intros. rewrite mult_Batch_rw2.
      rewrite runBatch_rw1. rewrite triangle_4.
      now rewrite natural_runBatch.
    - intros.  rewrite runBatch_rw2.
      unfold ap. rewrite (app_mult_natural_r F).
      rewrite <- (app_assoc F).
      rewrite <- IH. clear IH.
      compose near (runBatch ϕ (x ⊗ rest) ⊗ ϕ x').
      rewrite (fun_fmap_fmap F).
      cbn. unfold ap. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch. rewrite (app_mult_natural_l F).
      compose near (runBatch ϕ (x ⊗ rest) ⊗ ϕ x') on left.
      rewrite (fun_fmap_fmap F). fequal. now ext [[? ?] ?].
  Qed.

  #[global] Instance Morphism_store_fold: ApplicativeMorphism Batch F (@runBatch A F B ϕ _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatch.
    - intros. easy.
    - intros. apply appmor_mult_runBatch.
  Qed.

End free_alternate.

(** ** <<runBatch>> with monoidal values *)
(******************************************************************************)
Section runBatch_monoid.

  Context
    `{Monoid M}
    {A B : Type}
    (ϕ : A -> M).

  Fixpoint runBatch_monoid {C} (s : @Batch A B C) : M :=
    match s with
    | Go x => monoid_unit M
    | Ap rest i1 => runBatch_monoid rest ● ϕ i1
    end.

  Lemma runBatch_monoid1 : forall `(s : @Batch A B C),
      runBatch_monoid s = unconst (runBatch (mkConst (tag := B) ∘ ϕ) s).
  Proof.
    intros. induction s.
    - easy.
    - cbn. now rewrite IHs.
  Qed.

End runBatch_monoid.

(** * <<Batch>> as a parameterized comonad *)
(******************************************************************************)
Section parameterized.

  #[local] Unset Implicit Arguments.

  Fixpoint extract_Batch {A X : Type} (j : @Batch A A X) : X :=
    match j with
    | Go a => a
    | Ap rest x => extract_Batch rest x
    end.

  Fixpoint cojoin_Batch {A C X: Type} B (j : @Batch A C X) : @Batch A B (@Batch B C X) :=
    match j with
    | Go x => Go (Go x)
    | Ap rest a => Ap (fmap Batch (@Ap B C X) (cojoin_Batch B rest)) a
    end.

  (* TODO Finish rest of the parameterized comonad structure. *)
  Lemma extr_cojoin_Batch : `(extract_Batch ∘ cojoin_Batch A = @id (@Batch A C X)).
  Proof.
    intros. ext s. induction s.
    - reflexivity.
    - unfold compose. cbn.
  Abort.

End parameterized.

(*
(** ** Examples of <<cojoin>> *)
(******************************************************************************)
Section demo.

  Context
    (A B C X : Type)
    (a1 a2 : A) (b1 b2 b3 : B) (c1 c2 c3 c4 : C)
    (mk1 : C -> X) (mk2 : C -> C -> X) (mk0 : X).

  Check @Go A B X mk0.
  Compute cojoin_Batch B (@Go A B X mk0).
  Check Go mk1 ⧆ a1.
  Compute cojoin_Batch B (Go mk1 ⧆ a1).
  Check Go mk2 ⧆ a2 ⧆ a1.
  Compute cojoin_Batch B (Go mk2 ⧆ a2 ⧆ a1).

End demo.
*)
