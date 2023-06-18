From Tealeaves.Classes Require Export
  Monoid
  Applicative
  Traversable.Monad.
From Tealeaves.Functors Require Export
  Store
  Constant
  List.

Import Monoid.Notations.
Import Applicative.Notations.

#[local] Set Implicit Arguments.
#[local] Generalizable Variables ψ ϕ W F G M A B C D X Y O.

(** * The [Batch] idiom *)
(******************************************************************************)
Section fix_parameters.

  Inductive Batch (X Y : Type) (A : Type) : Type :=
  | Done : A -> Batch X Y A
  | Step : Batch X Y (Y -> A) -> X -> Batch X Y A.

  Fixpoint map_Batch {X Y : Type} `{f : A -> B} (c : Batch X Y A) : Batch X Y B :=
    match c with
    | Done _ _ a => Done _ _ (f a)
    | Step rest i1 =>
      Step (@map_Batch X Y (Y -> A) (Y -> B) (compose f) rest) i1
    end.

  #[export] Instance Map_Batch {X Y : Type} : Map (Batch X Y) := @map_Batch X Y.

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

#[global] Arguments Done {X Y}%type_scope [A]%type_scope _.

Module Notations.

  Infix "⧆" := Step (at level 51, left associativity) : tealeaves_scope.

End Notations.

Import Notations.

(** ** Applicative Instance *)
(******************************************************************************)

Section Applicative_Batch.

  Context
    {X Y : Type}.

  #[export] Instance Pure_Batch : Pure (@Batch X Y) :=
    fun (A : Type) (a : A) => Done a.

  Fixpoint mult_Batch `(ja : Batch X Y A) `(jb : Batch X Y B) : @Batch X Y (A * B) :=
    match jb with
    | Done b => map (Batch X Y) (fun (a : A) => (a, b)) ja
    | Step rest x1 =>
      Step (map (Batch X Y) strength_arrow (mult_Batch ja rest)) x1
    end.

  #[export] Instance Mult_Batch : Mult (@Batch X Y) :=
    fun A B '(x, y) => mult_Batch x y.

  Lemma mult_Batch_rw1 : forall `(a : A) `(b : B),
      Done a ⊗ Done b = (Done (a, b) : @Batch X Y (A * B)).
  Proof.
    easy.
  Qed.

  Lemma mult_Batch_rw2 : forall `(b : B) `(ja : Batch X Y A),
      ja ⊗ Done b = map (Batch X Y) (pair_right b) ja.
  Proof.
    intros. induction ja; easy.
  Qed.

  Lemma mult_Batch_rw3 : forall `(jb : Batch X Y B) `(a : A),
      Done a ⊗ jb = map (Batch X Y) (pair a) jb.
  Proof.
    induction jb.
    - easy.
    - intros. cbn; change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. rewrite IHjb. compose near jb on left.
      now rewrite (fun_map_map (Batch X Y)).
  Qed.

  Lemma mult_Batch_rw4 : forall (x : X) `(ja : @Batch X Y (Y -> A)) `(b : B),
      (ja ⧆ x) ⊗ Done b =
      map (Batch X Y) (costrength_arrow ∘ pair_right b) ja ⧆ x.
  Proof.
    easy.
  Qed.

  Lemma mult_Batch_rw5 : forall `(jb : @Batch X Y (Y -> B)) `(a : A) (x : X),
      Done a ⊗ (jb ⧆ x) = map (Batch X Y) (strength_arrow ∘ pair a) jb ⧆ x.
  Proof.
    cbn. change (mult_Batch ?x ?y) with (x ⊗ y) in *. intros.
    fequal. rewrite (mult_Batch_rw3). compose near jb on left.
    now rewrite (fun_map_map (Batch X Y)).
  Qed.

  Lemma mult_Batch_rw6 : forall (x1 x2 : X) `(ja : Batch X Y (Y -> A)) `(jb : Batch X Y (Y -> B)),
      (ja ⧆ x1) ⊗ (jb ⧆ x2) =
      map (Batch X Y) strength_arrow ((ja ⧆ x1) ⊗ jb) ⧆ x2.
  Proof.
    reflexivity.
  Qed.

  Lemma app_pure_natural_Batch : forall (A B : Type) (f : A -> B) (x : A),
      map (Batch X Y) f (pure (Batch X Y) x) = pure (Batch X Y) (f x).
  Proof.
    easy.
  Qed.

  Lemma app_mult_natural_Batch1 : forall (A B C : Type) (f : A -> C) (x : Batch X Y A) (y : Batch X Y B),
      map (Batch X Y) f x ⊗ y = map (Batch X Y) (map_fst f) (x ⊗ y).
  Proof.
    intros. generalize dependent C. induction y.
    - intros; cbn. compose near x.
      now do 2 rewrite (fun_map_map (Batch X Y)).
    - intros; cbn.
      change (mult_Batch ?x ?y) with (x ⊗ y) in *.
      rewrite IHy. compose near (x ⊗ y).
      do 2  rewrite (fun_map_map (Batch X Y)). do 2 fequal.
      now ext [? ?].
  Qed.

  Lemma app_mult_natural_Batch2 : forall (A B D : Type) (g : B -> D) (x : Batch X Y A) (y : Batch X Y B),
      x ⊗ map (Batch X Y) g y = map (Batch X Y) (map_snd g) (x ⊗ y).
  Proof.
    intros. generalize dependent D. induction y as [ANY any | ANY rest IH x'].
    - intros; cbn. compose near x on right. now rewrite (fun_map_map (Batch X Y)).
    - intros; cbn. fequal.
      change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite IH. compose near (x ⊗ rest).
      do 2 rewrite (fun_map_map (Batch X Y)). fequal.
      now ext [a mk].
  Qed.

  Lemma app_mult_natural_Batch : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : Batch X Y A) (y : Batch X Y B),
      map (Batch X Y) f x ⊗ map (Batch X Y) g y = map (Batch X Y) (map_tensor f g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_Batch1, app_mult_natural_Batch2.
    compose near (x ⊗ y) on left. rewrite (fun_map_map (Batch X Y)). fequal.
    now ext [a b].
  Qed.

  Lemma app_assoc_Batch : forall (A B C : Type) (x : Batch X Y A) (y : Batch X Y B) (z : Batch X Y C),
      map (Batch X Y) associator ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. induction z.
    - do 2 rewrite mult_Batch_rw2.
      rewrite (app_mult_natural_Batch2). compose near (x ⊗ y) on left.
      now rewrite (fun_map_map (Batch X Y)).
    - cbn. repeat change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      fequal.
      rewrite (app_mult_natural_Batch2).
      rewrite <- IHz. compose near (x ⊗ y ⊗ z).
      do 2 rewrite (fun_map_map (Batch X Y)).
      compose near (x ⊗ y ⊗ z) on right.
      rewrite (fun_map_map (Batch X Y)).
      fequal. now ext [[? ?] ?].
  Qed.

  Lemma app_unital_l_Batch : forall (A : Type) (x : Batch X Y A),
      map (Batch X Y) left_unitor (pure (Batch X Y) tt ⊗ x) = x.
  Proof.
    intros. induction x.
    - easy.
    - cbn. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      fequal. compose near (pure (Batch X Y) tt ⊗ x).
      rewrite (fun_map_map (Batch X Y)).
      rewrite <- IHx. repeat fequal. auto.
  Qed.

  Lemma app_unital_r_Batch : forall (A : Type) (x : (Batch X Y) A),
      map (Batch X Y) right_unitor (x ⊗ pure (Batch X Y) tt) = x.
  Proof.
    intros. induction x.
    - easy.
    - cbn in *. fequal. rewrite <- IHx at 2.
      compose near x. now do 2 rewrite (fun_map_map (Batch X Y)).
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
  Check Done a1 ⊗ Done a2 : @Batch False False (A * A).
  Compute Done a1 ⊗ Done a2.
  Compute Done a1 ⊗ (Done mk1 ⧆ c1).
  Compute (Done mk1 ⧆ c1) ⊗ (Done mk1 ⧆ c2).
  Compute (Done mk2 ⧆ c1 ⧆ c2) ⊗ (Done mk1 ⧆ c3).
   *)

End demo.

(** ** Functoriality of [Batch] in all arguments *)
(******************************************************************************)
Section functoriality_Batch.

  Context
    {A B C : Type}.

  Fixpoint mapfst_Batch (f : A -> B) `(j : @Batch A C X) : @Batch B C X :=
    match j with
    | Done a => Done a
    | Step rest a => Step (mapfst_Batch f rest) (f a)
    end.

  Fixpoint mapsnd_Batch (f : A -> B) `(j : @Batch C B X) : @Batch C A X :=
    match j with
    | Done a => Done a
    | Step rest c => Step (map (Batch C A) (precompose f) (mapsnd_Batch f rest)) c
    end.

End functoriality_Batch.

Lemma mapfst_Batch1 {A B C X Y : Type} (f : A -> B) (g : X -> Y) (j : @Batch A C X) :
  mapfst_Batch f (map (Batch A C) g j) = map (Batch B C) g (mapfst_Batch f j).
Proof.
  generalize dependent Y.
  generalize dependent B.
  induction j.
  - easy.
  - intros. cbn. fequal. auto.
Qed.

Lemma mapsnd_Batch1 {A B C X Y : Type} (f : B -> C) (g : X -> Y) (j : @Batch A C X) :
  mapsnd_Batch f (map (Batch A C) g j) = map (Batch A B) g (mapsnd_Batch f j).
Proof.
  generalize dependent B.
  generalize dependent Y.
  induction j.
  - easy.
  - intros. cbn. fequal.
    rewrite IHj. compose near (mapsnd_Batch f j).
    do 2 rewrite (fun_map_map (Batch A B)).
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
  mapfst_Batch f (Done (Y := Y) t) = Done t.
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
Fixpoint runBatch `(ϕ : A -> F B) `{Map F}`{Mult F} `{Pure F}
         `(j : @Batch A B X) : F X :=
  match j with
  | Done a => pure F a
  | Step rest i => runBatch ϕ rest <⋆> ϕ i
  end.

Lemma runBatch_rw1 `{Applicative F} `(ϕ : A -> F B) (X : Type) (x : X) :
  runBatch ϕ (Done x) = pure F x.
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
    map F f (runBatch ϕ j) = runBatch ϕ (map (Batch A B) f j).
  Proof.
    generalize dependent Y. induction j; intros.
    - cbn. now rewrite (app_pure_natural F).
    - cbn. rewrite map_ap. fequal. now rewrite IHj.
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
      runBatch (map F f ∘ ϕ) s = runBatch ϕ (mapsnd_Batch f s).
  Proof.
    intros. induction s.
    - easy.
    - intros. cbn. unfold compose at 2.
      rewrite <- ap_map. fequal.
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
      rewrite (fun_map_map F).
      cbn. unfold ap. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch. rewrite (app_mult_natural_l F).
      compose near (runBatch ϕ (x ⊗ rest) ⊗ ϕ x') on left.
      rewrite (fun_map_map F). fequal. now ext [[? ?] ?].
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
    | Done x => monoid_unit M
    | Step rest i1 => runBatch_monoid (ϕ : A -> M) rest ● ϕ i1
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

(** ** Length *)
(******************************************************************************)
Section length.

  Context (A B : Type).

  #[local] Unset Implicit Arguments.

  Fixpoint length_Batch (C : Type) (b : Batch A B C) : nat :=
    match b with
    | Done _ => 0
    | Step b' rest => S (length_Batch (B -> C) b')
    end.

 (* The length of a batch is the same as the length of the list we can extract from it *)
  Lemma batch_length1 : forall (C : Type) (b : Batch A B C),
      length_Batch C b =
        length (runBatch (F := const (list A)) (ret list A) b).
  Proof.
    intros C b.
    induction b as [C c | C b IHb a].
    - reflexivity.
    - cbn. rewrite IHb.
      unfold_ops @Monoid_op_list.
      rewrite List.app_length.
      cbn. lia.
  Qed.

End length.

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
    | Done a => a
    | Step rest x => extract_Batch rest x
    end.

  Fixpoint cojoin_Batch {A C X: Type} B (j : @Batch A C X) : @Batch A B (@Batch B C X) :=
    match j with
    | Done x => Done (Done x)
    | Step rest a => Step (map (Batch A B) (@Step B C X) (cojoin_Batch B rest)) a
    end.

    (*
  Context
    (A B C X : Type)
    (a1 a2 : A) (mk1 : C -> X) (mk2 : C -> C -> X) (mk0 : X).

  Check Done (X := A) (Y := C) mk0.
  Compute cojoin_Batch B (Done (X := A) (Y := C) mk0).
  Check Step (Done mk1) a1.
  Compute cojoin_Batch B (Step (Done mk1) a1).
  Check Step (Step (Done mk2) a2) a1.
  Compute cojoin_Batch B (Step (Step (Done mk2) a2) a1).
     *)

  (* TODO Finish rest of the parameterized comonad structure. *)
  Lemma extr_cojoin_Batch : `(extract_Batch ∘ cojoin_Batch A = @id (@Batch A C X)).
  Proof.
    intros. ext s. induction s.
    - reflexivity.
    - unfold compose. cbn.
  Abort.

End parameterized.

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
        (A B C X W : Type)
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
