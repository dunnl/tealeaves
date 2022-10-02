From Tealeaves Require Export
     Classes.Monoid
     Algebraic.Applicative
     Functors.Store
     Functors.Constant.

Import Monoid.Notations.
Import Applicative.Notations.

#[local] Set Implicit Arguments.
#[local] Generalizable Variables ψ ϕ F G M A B C X Y O.

(** * The [Batch] idiom *)
(******************************************************************************)
Section fix_parameters.

  Inductive Batch (X Y : Type) (A : Type) : Type :=
  | Go : A -> Batch X Y A
  | Ap : Batch X Y (Y -> A) -> X -> Batch X Y A.

  Fixpoint fmap_Batch {X Y : Type} `{f : A -> B} (c : Batch X Y A) : Batch X Y B :=
    match c with
    | Go _ _ a => Go _ _ (f a)
    | Ap rest i1 =>
      Ap (@fmap_Batch X Y (Y -> A) (Y -> B) (compose f) rest) i1
    end.

  #[export] Instance Fmap_Batch {X Y : Type} : Fmap (Batch X Y) := @fmap_Batch X Y.

  #[export, program] Instance Functor_Batch {X Y : Type} : Functor (Batch X Y).

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

#[global] Arguments Go {X Y}%type_scope [A]%type_scope _.

Module Notations.

  Infix "⧆" := Ap (at level 51, left associativity) : tealeaves_scope.

End Notations.

Import Notations.

(** ** Applicative Instance *)
(******************************************************************************)
(* TODO Move me *)
Definition eval `(a : A) `(f : A -> B) := f a.
Definition costrength_arr `(p : (A -> B) * C) : A -> B * C := fun a => (fst p a, snd p).
Definition strength_arr `(p : A * (B -> C)) : B -> A * C := fun b => (fst p, snd p b).
Definition pair_right {A B} : B -> A -> A * B := fun b a => (a, b).

Section Applicative_Batch.

  Context
    {X Y : Type}.

  #[export] Instance Pure_Batch : Pure (@Batch X Y) :=
    fun (A : Type) (a : A) => Go a.

  Fixpoint mult_Batch `(ja : Batch X Y A) `(jb : Batch X Y B) : @Batch X Y (A * B) :=
    match jb with
    | Go b => fmap (Batch X Y) (fun (a : A) => (a, b)) ja
    | Ap rest x1 =>
      Ap (fmap (Batch X Y) strength_arr (mult_Batch ja rest)) x1
    end.

  #[export] Instance Mult_Batch : Mult (@Batch X Y) :=
    fun A B '(x, y) => mult_Batch x y.

  Lemma mult_Batch_rw1 : forall `(a : A) `(b : B),
      Go a ⊗ Go b = (Go (a, b) : @Batch X Y (A * B)).
  Proof.
    easy.
  Qed.

  Lemma mult_Batch_rw2 : forall `(b : B) `(ja : Batch X Y A),
      ja ⊗ Go b = fmap (Batch X Y) (pair_right b) ja.
  Proof.
    intros. induction ja; easy.
  Qed.

  Lemma mult_Batch_rw3 : forall `(jb : Batch X Y B) `(a : A),
      Go a ⊗ jb = fmap (Batch X Y) (pair a) jb.
  Proof.
    induction jb.
    - easy.
    - intros. cbn; change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. rewrite IHjb. compose near jb on left.
      now rewrite (fun_fmap_fmap (Batch X Y)).
  Qed.

  Lemma mult_Batch_rw4 : forall (x : X) `(ja : @Batch X Y (Y -> A)) `(b : B),
      (ja ⧆ x) ⊗ Go b =
      fmap (Batch X Y) (costrength_arr ∘ pair_right b) ja ⧆ x.
  Proof.
    easy.
  Qed.

  Lemma mult_Batch_rw5 : forall `(jb : @Batch X Y (Y -> B)) `(a : A) (x : X),
      Go a ⊗ (jb ⧆ x) = fmap (Batch X Y) (strength_arr ∘ pair a) jb ⧆ x.
  Proof.
    cbn. change (mult_Batch ?x ?y) with (x ⊗ y) in *. intros.
    fequal. rewrite (mult_Batch_rw3). compose near jb on left.
    now rewrite (fun_fmap_fmap (Batch X Y)).
  Qed.

  Lemma mult_Batch_rw6 : forall (x1 x2 : X) `(ja : Batch X Y (Y -> A)) `(jb : Batch X Y (Y -> B)),
      (ja ⧆ x1) ⊗ (jb ⧆ x2) =
      fmap (Batch X Y) strength_arr ((ja ⧆ x1) ⊗ jb) ⧆ x2.
  Proof.
    reflexivity.
  Qed.

  Lemma app_pure_natural_Batch : forall (A B : Type) (f : A -> B) (x : A),
      fmap (Batch X Y) f (pure (Batch X Y) x) = pure (Batch X Y) (f x).
  Proof.
    easy.
  Qed.

  Lemma app_mult_natural_Batch1 : forall (A B C : Type) (f : A -> C) (x : Batch X Y A) (y : Batch X Y B),
      fmap (Batch X Y) f x ⊗ y = fmap (Batch X Y) (map_fst f) (x ⊗ y).
  Proof.
    intros. generalize dependent C. induction y.
    - intros; cbn. compose near x.
      now do 2 rewrite (fun_fmap_fmap (Batch X Y)).
    - intros; cbn.
      change (mult_Batch ?x ?y) with (x ⊗ y) in *.
      rewrite IHy. compose near (x ⊗ y).
      do 2  rewrite (fun_fmap_fmap (Batch X Y)). do 2 fequal.
      now ext [? ?].
  Qed.

  Lemma app_mult_natural_Batch2 : forall (A B D : Type) (g : B -> D) (x : Batch X Y A) (y : Batch X Y B),
      x ⊗ fmap (Batch X Y) g y = fmap (Batch X Y) (map_snd g) (x ⊗ y).
  Proof.
    intros. generalize dependent D. induction y as [ANY any | ANY rest IH x'].
    - intros; cbn. compose near x on right. now rewrite (fun_fmap_fmap (Batch X Y)).
    - intros; cbn. fequal.
      change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite IH. compose near (x ⊗ rest).
      do 2 rewrite (fun_fmap_fmap (Batch X Y)). fequal.
      now ext [a mk].
  Qed.

  Lemma app_mult_natural_Batch : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : Batch X Y A) (y : Batch X Y B),
      fmap (Batch X Y) f x ⊗ fmap (Batch X Y) g y = fmap (Batch X Y) (map_tensor f g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_Batch1, app_mult_natural_Batch2.
    compose near (x ⊗ y) on left. rewrite (fun_fmap_fmap (Batch X Y)). fequal.
    now ext [a b].
  Qed.

  Lemma app_assoc_Batch : forall (A B C : Type) (x : Batch X Y A) (y : Batch X Y B) (z : Batch X Y C),
      fmap (Batch X Y) associator ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. induction z.
    - do 2 rewrite mult_Batch_rw2.
      rewrite (app_mult_natural_Batch2). compose near (x ⊗ y) on left.
      now rewrite (fun_fmap_fmap (Batch X Y)).
    - cbn. repeat change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      fequal.
      rewrite (app_mult_natural_Batch2).
      rewrite <- IHz. compose near (x ⊗ y ⊗ z).
      do 2 rewrite (fun_fmap_fmap (Batch X Y)).
      compose near (x ⊗ y ⊗ z) on right.
      rewrite (fun_fmap_fmap (Batch X Y)).
      fequal. now ext [[? ?] ?].
  Qed.

  Lemma app_unital_l_Batch : forall (A : Type) (x : Batch X Y A),
      fmap (Batch X Y) left_unitor (pure (Batch X Y) tt ⊗ x) = x.
  Proof.
    intros. induction x.
    - easy.
    - cbn. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      fequal. compose near (pure (Batch X Y) tt ⊗ x).
      rewrite (fun_fmap_fmap (Batch X Y)).
      rewrite <- IHx. repeat fequal. auto.
  Qed.

  Lemma app_unital_r_Batch : forall (A : Type) (x : (Batch X Y) A),
      fmap (Batch X Y) right_unitor (x ⊗ pure (Batch X Y) tt) = x.
  Proof.
    intros. induction x.
    - easy.
    - cbn in *. fequal. rewrite <- IHx at 2.
      compose near x. now do 2 rewrite (fun_fmap_fmap (Batch X Y)).
  Qed.

  Lemma app_mult_pure_Batch : forall (A B : Type) (a : A) (b : B),
      pure (Batch X Y) a ⊗ pure (Batch X Y) b = pure (Batch X Y) (a, b).
  Proof.
    intros. easy.
  Qed.

  #[export, program] Instance App_Path : Applicative (Batch X Y).

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
    | Ap rest c => Ap (fmap (Batch C A) (precompose f) (mapsnd_Batch f rest)) c
    end.

End functoriality_Batch.

Lemma mapfst_Batch1 {A B C X Y : Type} (f : A -> B) (g : X -> Y) (j : @Batch A C X) :
  mapfst_Batch f (fmap (Batch A C) g j) = fmap (Batch B C) g (mapfst_Batch f j).
Proof.
  generalize dependent Y.
  generalize dependent B.
  induction j.
  - easy.
  - intros. cbn. fequal. auto.
Qed.

Lemma mapsnd_Batch1 {A B C X Y : Type} (f : B -> C) (g : X -> Y) (j : @Batch A C X) :
  mapsnd_Batch f (fmap (Batch A C) g j) = fmap (Batch A B) g (mapsnd_Batch f j).
Proof.
  generalize dependent B.
  generalize dependent Y.
  induction j.
  - easy.
  - intros. cbn. fequal.
    rewrite IHj. compose near (mapsnd_Batch f j).
    do 2 rewrite (fun_fmap_fmap (Batch A B)).
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

(** * <<Batch>> as a free applicative functor (<<runBatch>>) *)
(******************************************************************************)
Fixpoint runBatch `(ϕ : A -> F B) `{Fmap F}`{Mult F} `{Pure F}
         `(j : @Batch A B X) : F X :=
  match j with
  | Go a => pure F a
  | Ap rest i => runBatch ϕ rest <⋆> ϕ i
  end.

Lemma runBatch_rw1 `{Applicative F} `(ϕ : A -> F B) (X : Type) (x : X) :
  runBatch ϕ (Go x) = pure F x.
Proof.
  reflexivity.
Qed.

Lemma runBatch_rw2 `{Applicative F} `(ϕ : A -> F B)
      (a : A) (X : Type) (rest : @Batch A B (B -> X)) :
  runBatch ϕ (rest ⧆ a) = runBatch ϕ rest <⋆> ϕ a.
Proof.
  reflexivity.
Qed.

(** ** Naturality of of <<runBatch>> *)
(******************************************************************************)
Section runBatch_naturality.

  Context
    `{Applicative F}.

  Lemma natural_runBatch `(ϕ : A -> F B) `(f : X -> Y) (j : @Batch A B X) :
    fmap F f (runBatch ϕ j) = runBatch ϕ (fmap (Batch A B) f j).
  Proof.
    generalize dependent Y. induction j; intros.
    - cbn. now rewrite (app_pure_natural F).
    - cbn. rewrite ap6. fequal. now rewrite IHj.
  Qed.

  #[export] Instance Natural_runBatch `(ϕ : A -> F B) :
    Natural (@runBatch _ _ _ ϕ _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    introv. ext j. unfold compose. apply natural_runBatch.
  Qed.

  Lemma runBatch_mapfst : forall `(s : @Batch A1 B C) `(ϕ : A2 -> F B) (f : A1 -> A2),
      runBatch (ϕ ∘ f) s = runBatch ϕ (mapfst_Batch f s).
  Proof.
    intros; induction s.
    - easy.
    - cbn. now rewrite IHs.
  Qed.

  Lemma runBatch_mapsnd : forall `(s : @Batch A B2 C) `(ϕ : A -> F B1) (f : B1 -> B2),
      runBatch (fmap F f ∘ ϕ) s = runBatch ϕ (mapsnd_Batch f s).
  Proof.
    intros. induction s.
    - easy.
    - intros. cbn. unfold compose at 2.
      rewrite <- ap7. fequal.
      rewrite IHs.
      now rewrite natural_runBatch.
  Qed.

  Context
    `{ApplicativeMorphism F G ψ}.

  Lemma runBatch_morphism `(ϕ : A -> F B) `(j : @Batch A B X) :
    @ψ X (runBatch ϕ j) = runBatch (@ψ B ∘ ϕ) j.
  Proof.
    induction j.
    - cbn. now rewrite (appmor_pure F G).
    - cbn. rewrite ap_morphism_1.
      now rewrite IHj.
  Qed.

End runBatch_naturality.

(** ** <<runBatch>> is an applicative morphism **)
(******************************************************************************)
Section runBatch_morphism.

  Context
    `{Applicative F}
    `{ϕ : A -> F B}.

  Lemma appmor_pure_runBatch : forall (a : A),
      runBatch ϕ (pure (Batch A B) a) = pure F a.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runBatch : forall {C D} (x : Batch A B C) (y : Batch A B D),
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

  #[export] Instance Morphism_store_fold: ApplicativeMorphism (Batch A B) F (@runBatch A F B ϕ _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatch.
    - intros. easy.
    - intros. apply appmor_mult_runBatch.
  Qed.

End runBatch_morphism.

(** ** <<runBatch>> with monoidal values *)
(******************************************************************************)
Section runBatch_monoid.

  Context
    `{Monoid M}
    {A B : Type}.

  Fixpoint runBatch_monoid `(ϕ : A -> M) `(s : @Batch A B C) : M :=
    match s with
    | Go x => monoid_unit M
    | Ap rest i1 => runBatch_monoid (ϕ : A -> M) rest ● ϕ i1
    end.

  Lemma runBatch_monoid1 : forall (ϕ : A -> M) `(s : @Batch A B C),
      runBatch_monoid ϕ s = unconst (runBatch (mkConst (tag := B) ∘ ϕ) s).
  Proof.
    intros. induction s.
    - easy.
    - cbn. now rewrite IHs.
  Qed.

  Lemma runBatch_monoid2 : forall (ϕ : A -> M) `(s : @Batch A B C),
      runBatch_monoid ϕ s = runBatch (F := const M) (ϕ : A -> const M B) s.
  Proof.
    intros. induction s.
    - easy.
    - cbn. now rewrite IHs.
  Qed.

End runBatch_monoid.

(** ** Auxiliary lemmas for runBatch and constant applicative functors. *)
(******************************************************************************)
Section runBatch_aux.


End runBatch_aux.

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
    | Ap rest a => Ap (fmap (Batch A B) (@Ap B C X) (cojoin_Batch B rest)) a
    end.

    (*
  Context
    (A B C X : Type)
    (a1 a2 : A) (mk1 : C -> X) (mk2 : C -> C -> X) (mk0 : X).

  Check Go (X := A) (Y := C) mk0.
  Compute cojoin_Batch B (Go (X := A) (Y := C) mk0).
  Check Ap (Go mk1) a1.
  Compute cojoin_Batch B (Ap (Go mk1) a1).
  Check Ap (Ap (Go mk2) a2) a1.
  Compute cojoin_Batch B (Ap (Ap (Go mk2) a2) a1).
     *)

  (* TODO Finish rest of the parameterized comonad structure. *)
  Lemma extr_cojoin_Batch : `(extract_Batch ∘ cojoin_Batch A = @id (@Batch A C X)).
  Proof.
    intros. ext s. induction s.
    - reflexivity.
    - unfold compose. cbn.
  Abort.

End parameterized.
