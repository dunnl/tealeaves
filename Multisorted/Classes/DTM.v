From Multisorted Require Export
     Classes.Functor.

Import Product.Notations. (* for (W ×) *)
Import Monoid.Notations.
Import Multisorted.Theory.Category.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.
#[local] Open Scope list_scope.

(** * Multisorted DTM typeclass *)
(**************************************************************)
Section MultisortedDTM_typeclasses.

  Context
    `{ix : Index}.

  (** ** Operations *)
  (**************************************************************)
  Section operations.

    Context
      (W : Type)
      (T : K -> Type -> Type)
      (S : Type -> Type).

    Class MReturn :=
      mret : forall {A}, A ~k~> T A.

    Class MBind :=
      mbinddt : forall (F : Type -> Type) `{Fmap F} `{Pure F} `{Mult F} {A B : Type},
        (forall (k : K), W * A -> F (T k B)) -> (S A -> F (S B)).

  End operations.

  (** ** Typeclass *)
  (******************************************************************************)
  Section PreModule.

    Context
      (W : Type)
      (S : Type -> Type)
      (T : K -> Type -> Type)
      `{! MReturn T}
      `{! MBind W T S}
      `{! forall k, MBind W T (T k)}
      {mn_op : Monoid_op W}
      {mn_unit : Monoid_unit W}.

    Definition compose_dtm
               `{Fmap F} `{Mult F} `{Pure F}
               `{Fmap G} `{Mult G} `{Pure G}
               `{forall k, MBind W T (T k)}
               {A B C}
               `(g : forall k, W * B -> G (T k C))
               `(f : forall k, W * A -> F (T k B)) :
      forall k, W * A -> F (G (T k C)) :=
      fun k '(w, a) => fmap F (mbinddt W T (T k) G (g ◻ const (incr w))) (f k (w, a)).

    Infix "⋆dtm" := compose_dtm (at level 40) : tealeaves_scope.

    Class DTPreModule :=
      { dtp_monoid :> Monoid W;
        dtp_mbinddt_mret : forall A,
            mbinddt W T S (fun a => a) (fun k '(w, a) => mret T k a) = @id (S A);
        dtp_mbinddt_mbinddt : forall
            (F : Type -> Type)
            (G : Type -> Type)
            `{Applicative F}
            `{Applicative G}
            `(g : forall k, W * B -> G (T k C))
            `(f : forall k, W * A -> F (T k B)),
            fmap F (mbinddt W T S G g) ∘ mbinddt W T S F f =
            mbinddt W T S (F ∘ G) (g ⋆dtm f);
        dtp_mbinddt_morphism : forall
            (F : Type -> Type)
            (G : Type -> Type)
            `{ApplicativeMorphism F G ϕ}
            `(f : forall k, W * A -> F (T k B)),
            ϕ (S B) ∘ mbinddt W T S F f =
            mbinddt W T S G (fun k => ϕ (T k B) ∘ f k);
      }.

  End PreModule.

  Section DTM.

    Context
      (W : Type)
      (T : K -> Type -> Type)
      `{! MReturn T}
      `{! forall k, MBind W T (T k)}
      {mn_op : Monoid_op W}
      {mn_unit : Monoid_unit W}.

    Class DTM :=
      { dtm_pre :> forall k, DTPreModule W (T k) T;
        dtm_mbinddt_comp_mret :
          forall k F `{Applicative F}
            `(f : forall k, W * A -> F (T k B)),
            mbinddt W T (T k) F f ∘ mret T k = (fun a => f k (Ƶ, a));
      }.

  End DTM.

End MultisortedDTM_typeclasses.

Arguments mbinddt {ix} {W}%type_scope {T} S%function_scope {MBind} F%function_scope {H H0 H1} {A B}.
Arguments compose_dtm {ix} {W}%type_scope {T}%function_scope {mn_op} {F}%function_scope {H0 H1 H2}
          {G}%function_scope {H3 H4 H5} {H6}%function_scope {A B C}%type_scope (_ _)%function_scope _ _.

(** ** Notations **)
(******************************************************************************)
Module Notations.

  Infix "⋆dtm" := compose_dtm (at level 40) : tealeaves_scope.

End Notations.

(** ** Derived operations on DTMs *)
(******************************************************************************)
Section derived_operations.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}.

  Definition mbindt (F : Type -> Type) `{Fmap F} `{Mult F} `{Pure F}
             `(f : forall k, A -> F (T k B)) : S A -> F (S B) :=
    mbinddt S F (f ◻ const (extract (W ×))).

  Definition mfmapdt (F : Type -> Type) `{Fmap F} `{Mult F} `{Pure F}
             `(f : forall k, W * A -> F B) : S A -> F (S B) :=
    mbinddt S F (fun k '(w, a) => fmap F (mret T k) (f k (w, a))).

  Definition mbindd `(f : forall k, W * A -> T k B) : S A -> S B :=
    mbinddt S (fun x => x) f.

  Definition mfmapt (F : Type -> Type) `{Fmap F} `{Mult F} `{Pure F}
             `(f : forall k, A -> F B) : S A -> F (S B) :=
    mbindt F (fun k a => fmap F (mret T k) (f k a)).

  Definition mbind `(f : forall k, A -> T k B) : S A -> S B :=
    mbindd (f ◻ const (extract (W ×))).

  Definition mfmapd `(f : forall k, W * A -> B) : S A -> S B :=
    mfmapdt (fun x => x) f.

  Definition mfmap `(f : forall k, A -> B) : S A -> S B :=
    mfmapd (f ◻ const (extract (W ×))).

  Context
    {A B : Type}
    `{Fmap F} `{Mult F} `{Pure F}.

  Lemma mbindt_to_mbinddt :
    forall (f : forall k, A -> F (T k B)),
      mbindt F f = mbinddt S F (f ◻ const (extract (W ×))).
  Proof.
    reflexivity.
  Qed.

  Lemma mbindd_to_mbinddt :
    forall (f : forall k, W * A -> T k B),
      mbindd f = mbinddt S (fun A => A) f.
  Proof.
    reflexivity.
  Qed.

  Lemma mfmapdt_to_mbinddt :
    forall (f : K -> W * A -> F B),
      mfmapdt F f = mbinddt S F (fun k '(w, a) => fmap F (mret T k) (f k (w, a))).
  Proof.
    reflexivity.
  Qed.

  Lemma mbind_to_mbinddt :
    forall (f : forall k, A -> T k B),
      mbind f = mbinddt S (fun A => A) (f ◻ const (extract (W ×))).
  Proof.
    reflexivity.
  Qed.

  Lemma mfmapd_to_mbinddt :
    forall (f : K -> W * A -> B),
      mfmapd f = mbinddt S (fun A => A) (mret T ◻ f).
  Proof.
    intros. unfold mfmapd.
    unfold mfmapdt. fequal. now ext k [w a].
  Qed.

  Lemma mfmapt_to_mbinddt :
    forall (f : K -> A -> F B),
      mfmapt F f = mbinddt S F (fun k '(w, a) => fmap F (mret T k) (f k a)).
  Proof.
    intros. unfold mfmapt.
    unfold mbindt. fequal. now ext k [w a].
  Qed.

  Lemma mfmap_to_mbinddt :
    forall (f : K -> A -> B),
      mfmap f = mbinddt S (fun A => A) (mret T ◻ f ◻ const (extract (W ×))).
  Proof.
    intros. unfold mfmap. now rewrite mfmapd_to_mbinddt.
  Qed.

End derived_operations.

(** ** Purity law *)
(******************************************************************************)
Section DTM_laws.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Purity *)
  (******************************************************************************)
  Lemma mbinddt_pure : forall (A : Type) `{Applicative F},
      mbinddt S F (fun k '(w, a) => pure F (mret T k a)) = pure F (A := S A).
  Proof.
    intros. replace (fun (k : K) '((w, a) : W * A) => pure F (mret T k a))
              with (fun (k : K) => (pure F ∘ (mret T k ∘ extract (W ×) (A := A)))).
    2:{ ext k [w a]. easy. }
    rewrite <- (dtp_mbinddt_morphism W S T (fun x => x) F (ϕ := @pure F _)).
    replace (fun k : K => mret T k ∘ extract (prod W))
      with (fun (k : K) '((w, a) : W * A) => mret T k a).
    2: { ext k [w a]. easy. }
    now rewrite (dtp_mbinddt_mret W S T).
  Qed.

End DTM_laws.

(** * Derived structures on DTMs *)
(******************************************************************************)

(** ** Decorated monads (<<mbindd>>) *)
(******************************************************************************)
Section DecoratedMonad.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Definition compose_dm
             `(g : forall k, W * B -> T k C)
             `(f : forall k, W * A -> T k B) :
    forall k, W * A -> T k C :=
    fun k '(w, a) => mbindd (T k) (g ◻ const (incr w)) (f k (w, a)).

  Infix "⋆dm" := compose_dm (at level 40).

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem mbindd_id : forall A,
      mbindd S (mret T ◻ const (extract (W ×))) = @id (S A).
  Proof.
    intros. unfold mbindd.
    rewrite <- (dtp_mbinddt_mret W S T).
    fequal. now ext k [w a].
  Qed.

  Theorem mbindd_mbindd {A B C} : forall (g : W * B ~k~> T C) (f : W * A ~k~> T B),
      mbindd S g ∘ mbindd S f =
      mbindd S (fun (k : K) '(w, a) => mbindd (T k) (g ◻ const (incr w)) (f k (w, a))).
  Proof.
    intros. unfold mbindd.
    change_left (fmap (fun x => x) (mbinddt S (fun x : Type => x) g) ∘ (mbinddt S (fun x : Type => x) f)).
    rewrite (dtp_mbinddt_mbinddt W S T (fun x => x) (fun x => x)).
    fequal. now ext x y [z w].
  Qed.

  (** *** Right unit law for monads *)
  (******************************************************************************)
  Theorem mbindd_comp_mret {A B} : forall (k : K) (f : forall k, W * A -> T k B) (a : A),
      mbindd (T k) f (mret T k a) = f k (Ƶ, a).
  Proof.
    intros. unfold mbindd. compose near a.
    now rewrite (dtm_mbinddt_comp_mret W T k (fun A => A)).
  Qed.

  (** *** Composition with other operations *)
  (******************************************************************************)
  Lemma  mbinddt_mbindd {A B C} :
    forall `{Applicative G} (g : forall k, W * B -> G (T k C))
      (f : W * A ~k~> T B),
      mbinddt S G g ∘ mbindd S f =
      mbinddt S G (fun (k : K) '(w, a) => mbinddt (T k) G (g ◻ const (incr w)) (f k (w, a))).
  Proof.
    intros. unfold mbindd.
    change_left (fmap (fun x => x) (mbinddt S G g) ∘ mbinddt S (fun x : Type => x) f).
    rewrite (dtp_mbinddt_mbinddt W S T (fun x => x) G).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma mbind_to_mbindd {A B} (f : forall k, A -> T k B) :
    mbind S f = mbindd S (fun k => f k ∘ extract (W ×)).
  Proof.
    reflexivity.
  Qed.

  Lemma mfmapd_to_mbindd {A B} (f : W * A -k-> B) :
    mfmapd S f = mbindd S (fun k => mret T k ∘ f k).
  Proof.
    unfold mfmapd, mfmapdt, mbindd.
    fequal. now ext k [w a].
  Qed.

  Lemma mfmap_to_mbindd {A B} (f : A -k-> B) :
    mfmap S f = mbindd S (fun k => mret T k ∘ f k ∘ extract (W ×)).
  Proof.
    unfold mfmap, mfmapd, mfmapdt, mbindd.
    fequal. now ext k [w a].
  Qed.

End DecoratedMonad.

(** ** Decorated traversable functors (<<mfmapdt>>) *)
(******************************************************************************)
Section DecoratedTraversable.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem mfmapdt_id : forall A,
      mfmapdt S (fun x => x) (const (extract (W ×))) = @id (S A).
  Proof.
    intros. apply (dtp_mbinddt_mret W S T).
  Qed.

  Theorem mfmapdt_mfmapdt {A B C} :
    forall `{Applicative F} `{Applicative G}
      (g : forall k, W * B -> G C) (f : forall k, W * A -> F B),
      fmap F (mfmapdt S G g) ∘ mfmapdt S F f =
      mfmapdt S (F ∘ G) (fun (k : K) '(w, a) => fmap F (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros. unfold mfmapdt. rewrite (dtp_mbinddt_mbinddt W S T F G).
    fequal. unfold compose_dtm. ext k [w a]. unfold_ops @Fmap_compose.
    compose near (f k (w, a)).
    do 2 rewrite (fun_fmap_fmap F). rewrite (dtm_mbinddt_comp_mret W T k G).
    fequal. ext b. cbn. now simpl_monoid.
  Qed.

  (** *** Purity *)
  (******************************************************************************)
  Lemma mfmapdt_pure : forall (A B : Type) `{Applicative F},
      mfmapdt S F (fun k '(w, a) => pure F a) = pure F (A := S A).
  Proof.
    intros. unfold mfmapdt.
    replace (fun (k : K) '((w, a) : W * A) => fmap F (mret T k) (pure F a))
      with (fun (k : K) => (pure F ∘ (mret T k ∘ extract (W ×) (A := A)))).
    rewrite <- (dtp_mbinddt_morphism W S T (fun x => x) F (ϕ := @pure F _)).
    replace (fun k : K => mret T k ∘ extract (prod W))
      with (fun (k : K) '((w, a) : W * A) => mret T k a).
    2: { ext k [w a]. easy. }
    now rewrite (dtp_mbinddt_mret W S T).
    ext k [w a]. unfold compose; cbn.
    now rewrite (app_pure_natural F).
  Qed.

  (** *** Naturality w.r.t. <<mret>> *)
  (******************************************************************************)
  Lemma mfmapdt_comp_mret {A B} :
    forall `{Applicative F} (k : K) (f : forall k, W * A -> F B) (a : A),
      mfmapdt (T k) F f (mret T k a) = fmap F (mret T k) (f k (Ƶ, a)).
  Proof.
    intros. unfold mfmapdt. compose near a.
    now rewrite (dtm_mbinddt_comp_mret W T k F).
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma mfmapd_to_mfmapdt {A B} (f : K -> W * A -> B) :
    mfmapd S f = mfmapdt S (fun A => A) f.
  Proof.
    reflexivity.
  Qed.

  Lemma mfmap_to_mfmapdt {A B} (f : K -> A -> B) :
    mfmap S f = mfmapdt S (fun A => A) (fun k '(w, a) => f k a).
  Proof.
    reflexivity.
  Qed.

  Lemma mfmapt_to_mfmapdt {A B} `{Applicative F} (f : K -> A -> F B) :
    mfmapt S F f = mfmapdt S F (fun k '(w, a) => f k a).
  Proof.
    unfold mfmapt, mfmapdt. unfold mbindt.
    fequal. now ext k [w a].
  Qed.

End DecoratedTraversable.

(** ** Traversable monads (<<mbindt>>) *)
(******************************************************************************)
Section TraversableMonad.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem mbindt_id : forall A,
      mbindt S (fun x => x) (mret T) = @id (S A).
  Proof.
    intros. unfold mbindt.
    replace (mret T ◻ const (extract (prod W)))
      with (fun k '((w, a) : W * A) => mret T k a).
    now rewrite (dtp_mbinddt_mret W S T).
    now ext k [w a].
  Qed.

  Theorem mbindt_mbindt {A B C} :
    forall `{Applicative F} `{Applicative G}
      (g : forall k, B -> G (T k C)) (f : forall k, A -> F (T k B)),
      fmap F (mbindt S G g) ∘ mbindt S F f =
      mbindt S (F ∘ G) (fun (k : K) (a : A) => fmap F (mbindt (T k) G g) (f k a)).
  Proof.
    intros. unfold mbindt. rewrite (dtp_mbinddt_mbinddt W S T F G).
    fequal. ext k [w a]. unfold compose; cbn.
    repeat fequal. ext k2 [w2 b]. easy.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mbindt_comp_mret {A B} :
    forall `{Applicative F} (k : K) (f : forall k, A -> F (T k B)) (a : A),
      mbindt (T k) F f (mret T k a) = f k a.
  Proof.
    intros. unfold mbindt. compose near a on left.
    now rewrite (dtm_mbinddt_comp_mret W T k F).
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma mbind_to_mbindt {A B} (f : forall k, A -> T k B) :
    mbind S f = mbindt S (fun A => A) f.
  Proof.
    reflexivity.
  Qed.

  Lemma mfmapt_to_mbindt {A B} `{Applicative F} (f : K -> W * A -> F B) :
    mfmapt S F f = mbindt S F (fun k => fmap F (mret T k) ∘ f k).
  Proof.
    reflexivity.
  Qed.

  Lemma mfmap_to_mbindt {A B} (f : A -k-> B) :
    mfmap S f = mbindt S (fun A => A) (fun k => mret T k ∘ f k).
  Proof.
    rewrite mfmap_to_mbinddt.
    rewrite mbindt_to_mbinddt.
    reflexivity.
  Qed.

End TraversableMonad.

(** ** Decorated functors (<<mfmapd>>) *)
(******************************************************************************)
Section DecoratedFunctor.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Composition and identity law *)
  (******************************************************************************)
    Theorem mfmapd_id : forall A,
      mfmapd S (const (extract (W ×))) = @id (S A).
  Proof.
    intros. rewrite mfmapd_to_mfmapdt.
    now rewrite (mfmapdt_id S).
  Qed.

  Theorem mfmapd_mfmapd {A B C} :
    forall (g : K -> W * B -> C) (f : K -> W * A -> B),
      mfmapd S g ∘ mfmapd S f =
      mfmapd S (fun (k : K) '(w, a) => g k (w, f k (w, a))).
  Proof.
    intros. do 3 rewrite mfmapd_to_mfmapdt.
    change (mfmapdt S (fun A => A) g) with
        (fmap (fun A => A) (mfmapdt S (fun A => A) g)).
    rewrite (mfmapdt_mfmapdt S (G := fun A => A) (F := fun A => A)).
    unfold compose; cbn. fequal.
    now rewrite Mult_compose_identity1.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mfmapd_comp_mret {A B} :
    forall (k : K) (f : K -> W * A -> B) (a : A),
      mfmapd (T k) f (mret T k a) = mret T k (f k (Ƶ, a)).
  Proof.
    intros. rewrite mfmapd_to_mfmapdt. now rewrite mfmapdt_comp_mret.
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma mfmap_to_mfmapd {A B} (f : K -> A -> B) :
    mfmap S f = mfmapd S (fun k '(w, a) => f k a).
  Proof.
    reflexivity.
  Qed.

End DecoratedFunctor.

(** ** Traversable functors (<<mfmapt>>) *)
(******************************************************************************)
Section TraversableFunctor.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Composition and identity law *)
  (******************************************************************************)
    Theorem mfmapt_id : forall A,
      mfmapt S (fun A => A) (const (@id A)) = @id (S A).
  Proof.
    intros. unfold mfmapt.
    now rewrite <- (mbindt_id S).
  Qed.

  Theorem mfmapt_mfmapt {A B C} :
    forall `{Applicative G} `{Applicative F}
      (g : K -> B -> G C) (f : K -> A -> F B),
      fmap F (mfmapt S G g) ∘ mfmapt S F f =
      mfmapt S (F ∘ G) (fun (k : K) (a : A) => fmap F (g k) (f k a)).
  Proof.
    intros. rewrite (mfmapt_to_mfmapdt S (F := G)).
    rewrite (mfmapt_to_mfmapdt S (F := F)).
    rewrite (mfmapt_to_mfmapdt S (F := F ∘ G)).
    now rewrite (mfmapdt_mfmapdt S).
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mfmapt_comp_mret {A B} :
    forall  `{Applicative F} (k : K) (f : K -> A -> F B) (a : A),
      mfmapt (T k) F f (mret T k a) = fmap F (mret T k) (f k a).
  Proof.
    intros. rewrite (mfmapt_to_mfmapdt (T k)). now rewrite mfmapdt_comp_mret.
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma mfmap_to_mfmapt {A B} (f : K -> A -> B) :
    mfmap S f = mfmapt S (fun A => A) f.
  Proof.
    rewrite mfmap_to_mfmapdt.
    rewrite (mfmapt_to_mfmapdt S (F := fun A => A)).
    reflexivity.
  Qed.

End TraversableFunctor.

(** ** Monads (<<mbind>>) *)
(******************************************************************************)
Section Monad.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Composition and identity law *)
  (******************************************************************************)
    Theorem mbind_id : forall A,
      mbind S (fun k => mret T k) = @id (S A).
  Proof.
    intros. rewrite mbind_to_mbindd.
    now rewrite <- (mbindd_id S).
  Qed.

  Theorem mbind_mbind {A B C} :
    forall (g : forall (k : K), B -> T k C) (f : forall (k : K), A -> T k B),
      mbind S g ∘ mbind S f =
      mbind S (fun (k : K) (a : A) => mbind (T k) g (f k a)).
  Proof.
    intros. do 3 rewrite (mbind_to_mbindd S).
    rewrite (mbindd_mbindd S).
    unfold compose; cbn. fequal.
    ext k [w a].
    rewrite (mbind_to_mbindd (T k)).
    cbn. fequal. now ext j [w2 b].
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mbind_comp_mret {A B} :
    forall (k : K) (f : forall (k : K), A -> T k B) (a : A),
      mbind (T k) f (mret T k a) = f k a.
  Proof.
    intros. rewrite mbind_to_mbindd. now rewrite mbindd_comp_mret.
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma mfmap_to_mbind {A B} (f : K -> A -> B) :
    mfmap S f = mbind S (mret T ◻ f).
  Proof.
    rewrite mfmap_to_mbindd.
    rewrite mbind_to_mbindd.
    reflexivity.
  Qed.

End Monad.

(** ** Functors (<<mfmap>>) *)
(******************************************************************************)
Section Functor.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem mfmap_id : forall A,
      mfmap S (const (@id A)) = @id (S A).
  Proof.
    intros. apply (dtp_mbinddt_mret W S T).
  Qed.

  Theorem mfmap_mfmap {A B C} : forall
      (g : K -> B -> C) (f : K -> A -> B),
      mfmap S g ∘ mfmap S f = mfmap S (g ⊙ f).
  Proof.
    intros. do 2 rewrite mfmap_to_mfmapd.
    now rewrite (mfmapd_mfmapd S).
  Qed.

  (** *** Naturality w.r.t. <<mret>> *)
  (******************************************************************************)
  Lemma mfmap_comp_mret {A B} :
    forall (f : K -> A -> B) (a : A) (k : K),
      mfmap (T k) f (mret T k a) = mret T k (f k a).
  Proof.
    intros. rewrite mfmap_to_mfmapd.
    now rewrite mfmapd_comp_mret.
  Qed.

  (** *** Fusion of <<mfmap>> with <<mbinddt>> *)
  (******************************************************************************)
  Lemma mfmap_mbinddt {A B C} : forall
      `{Applicative F}
      (g : K -> B -> C) (f : forall (k : K), W * A -> F (T k B)),
      fmap F (mfmap S g) ∘ mbinddt S F f = mbinddt S F (fun k '(w, a) => fmap F (mfmap (T k) g) (f k (w, a))).
  Proof.
    intros. unfold mfmap, mfmapd, mfmapdt.
    rewrite (dtp_mbinddt_mbinddt W S T F (fun x => x)).
    fequal.
    - ext X Y [x y]. now rewrite Mult_compose_identity1.
    - ext k [w a]. cbn. repeat fequal. ext k2 [w2 b].
      cbn. easy.
  Qed.

End Functor.

(** * Targetted operations *)
(******************************************************************************)

(** ** Targetted substitution-building combinators: [btg] and [btgd] *)
(******************************************************************************)
(* TODO : Define a version that works for applicative effects. *)
(*
#[program] Definition btga `{ix : Index} `{Fmap F} `{Pure F} `{Mult F}
 {A W : Type} (T : K -> Type -> Type) `{! MReturn T}
 (j : K) (f : W * A -> F (T j A)) : forall (k : K), W * A -> F (T k A) :=
  fun k '(w, a) => if k == j then f (w, a) else pure F ∘ mret T k a.
*)

#[program] Definition tgtd `{ix : Index} {A W : Type} (T : K -> Type -> Type)
 (j : K) (f : W * A -> A) : K -> W * A -> A :=
  fun k '(w, a) => if k == j then f (w, a) else a.

#[program] Definition tgt `{ix : Index} {A : Type} (T : K -> Type -> Type)
 (j : K) (f : A -> A) : K -> A -> A :=
  fun k a => if k == j then f a else a.

#[program] Definition btgd `{ix : Index} {A W : Type} (T : K -> Type -> Type) `{! MReturn T}
 (j : K) (f : W * A -> T j A) : forall (k : K), W * A -> T k A :=
  fun k '(w, a) => if k == j then f (w, a) else mret T k a.

#[program] Definition btg `{ix : Index} {A : Type} (T : K -> Type -> Type) `{! MReturn T}
 (j : K) (f : A -> T j A) : forall (k : K), A -> T k A :=
  fun k => if k == j then f else mret T k.

Require Import Coq.Program.Equality.

(** ** Lemmas for [btgd], [btg] *)
(******************************************************************************)
Section btgd_lemmas.

  Context
    `{MReturn T}
    {W A : Type}.

  Lemma tgtd_eq : forall k (f : W * A -> A),
      tgtd T k f k = f.
  Proof.
    introv. unfold tgtd. ext [w a].
    compare values k and k.
  Qed.

  Lemma tgtd_neq : forall {k j} (f : W * A -> A),
      k <> j -> tgtd T j f k = extract (W ×).
  Proof.
    introv. unfold tgtd. intro hyp. ext [w a].
    compare values k and j.
  Qed.

  Lemma tgtd_id (j : K) :
    tgtd (A := A) T j (extract (W ×)) = const (extract (W ×)).
  Proof.
    unfold tgtd. ext k [w a]. compare values k and j.
  Qed.

  Lemma tgt_eq : forall k (f : A -> A),
      tgt T k f k = f.
  Proof.
    introv. unfold tgt. ext a.
    compare values k and k.
  Qed.

  Lemma tgt_neq : forall {k j} (f : A -> A),
      k <> j -> tgt T j f k = @id A.
  Proof.
    introv. unfold tgt. intro hyp. ext a.
    compare values k and j.
  Qed.

  Lemma tgt_id (j : K) :
    tgt (A := A) T j (@id A) = const (@id A).
  Proof.
    unfold tgt. ext k a. compare values k and j.
  Qed.

  Lemma btgd_eq : forall k (f : W * A -> T k A),
      btgd T k f k = f.
  Proof.
    introv. unfold btgd. ext [w a].
    compare values k and k.
    dependent destruction DESTR_EQ.
    cbn. reflexivity.
  Qed.

  Lemma btgd_neq : forall {k j} (f : W * A -> T j A),
      k <> j -> btgd T j f k = mret T k ∘ extract (W ×).
  Proof.
    introv. unfold btgd. intro hyp. ext [w a].
    compare values k and j.
  Qed.

  Lemma btgd_id (j : K) :
    btgd (A := A) T j (mret T j ∘ extract (W ×)) = mret T ◻ const (extract (W ×)).
  Proof.
    unfold btgd. ext k [w a]. compare values k and j.
  Qed.

  Lemma btg_eq : forall k (f : A -> T k A),
      btg T k f k = f.
  Proof.
    introv. unfold btg.
    compare values k and k.
    dependent destruction DESTR_EQ.
    cbn. reflexivity.
  Qed.

  Lemma btg_neq : forall {k j} (f : A -> T j A),
      k <> j -> btg T j f k = mret T k.
  Proof.
    introv. unfold btg. intro hyp.
    compare values k and j.
  Qed.

  Lemma btg_id (j : K) :
    btg (A := A) T j (mret T j) = mret T.
  Proof.
    unfold btg. ext k. compare values k and j.
  Qed.

End btgd_lemmas.

(** ** Rewrite Hint registration *)
(******************************************************************************)
Hint Rewrite @tgt_eq @tgtd_eq @tgt_id @tgtd_id : tea_tgt.
Hint Rewrite @btgd_eq @btg_eq @btg_id @btgd_id : tea_tgt.
Hint Rewrite @btgd_neq @btg_neq using auto : tea_tgt.

Hint Rewrite @tgt_eq @tgtd_eq @tgt_id @tgtd_id : tea_tgt_eq.
Hint Rewrite @btgd_eq @btg_eq @btg_id @btgd_id : tea_tgt_eq.
Hint Rewrite @tgtd_neq @tgt_neq using auto : tea_tgt_neq.
Hint Rewrite @btgd_neq @btg_neq using auto : tea_tgt_neq.

(** ** Derived targetted DTM operations *)
(******************************************************************************)
Section DTM_targetted.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    (j : K).

  Definition kbindd {A} `(f : W * A -> T j A) : S A -> S A
    := mbindd S (btgd T j f).

  Definition kbind `(f : A -> T j A) : S A -> S A
    := mbind S (btg T j f).

  Definition kfmapd `(f : W * A -> A) : S A -> S A :=
    mfmapd S (tgtd T j f).

  Definition kfmap `(f : A -> A) : S A -> S A :=
    mfmap S (tgt T j f).

End DTM_targetted.

(** ** Laws for decorated monads (<<kbindd>>) *)
(******************************************************************************)
Section DecoratedMonad.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    {j : K}
    {A : Type}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem kbindd_id :
      kbindd S j (mret T j ∘ (extract (W ×))) = @id (S A).
  Proof.
    intros. unfold kbindd. rewrite <- (mbindd_id S).
    fequal. ext k [w a]. cbn. compare values k and j.
  Qed.

  Theorem kbindd_kbindd_eq : forall (g : W * A -> T j A) (f : W * A -> T j A),
      kbindd S j g ∘ kbindd S j f =
      kbindd S j (fun '(w, a) => kbindd (T j) j (g ∘ incr w) (f (w, a))).
  Proof.
    intros. unfold kbindd. rewrite (mbindd_mbindd S).
    fequal. ext k [w a]. cbn. compare values k and j.
    - cbn. fequal. ext k [w' a']. compare values k and j.
    - rewrite mbindd_comp_mret. cbn. compare values k and j.
  Qed.

  Theorem kbindd_kbindd_neq :
    forall {i : K} (Hneq : j <> i)
      (g : W * A -> T i A) (f : W * A -> T j A),
      kbindd S i g ∘ kbindd S j f =
      mbindd S (compose_dm (btgd T i g) (btgd T j f)).
  Proof.
    intros. unfold kbindd. now rewrite (mbindd_mbindd S).
  Qed.

  (** *** Right unit law for monads *)
  (******************************************************************************)
  Theorem kbindd_comp_mret_eq : forall (f : W * A -> T j A) (a : A),
      kbindd (T j) j f (mret T j a) = f (Ƶ, a).
  Proof.
    intros. unfold kbindd. rewrite (mbindd_comp_mret).
    now autorewrite with tea_tgt_eq.
  Qed.

  Theorem kbindd_comp_mret_neq :
    forall (i : K) (Hneq : j <> i)
      (f : W * A -> T j A) (a : A),
      kbindd (T i) j f (mret T i a) = mret T i a.
  Proof.
    intros. unfold kbindd. rewrite (mbindd_comp_mret).
    now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma kbind_to_kbindd (f : A -> T j A) :
    kbind S j f = kbindd S j (f ∘ extract (W ×)).
  Proof.
    unfold kbind, kbindd. rewrite mbind_to_mbindd.
    fequal. ext k [w a]. unfold compose; cbn.
    compare values k and j.
    - autorewrite  with tea_tgt_eq. easy.
    - autorewrite  with tea_tgt_neq. easy.
  Qed.

  Lemma kfmapd_to_kbindd (f : W * A -> A) :
    kfmapd S j f = kbindd S j (mret T j ∘ f).
  Proof.
    unfold kfmapd, kbindd. rewrite mfmapd_to_mbindd.
    fequal. ext k [w a]. unfold compose. cbn. compare values k and j.
  Qed.

  Lemma kfmap_to_kbindd (f : A -> A) :
    kfmap S j f = kbindd S j (mret T j ∘ f ∘ extract (W ×)).
  Proof.
    unfold kfmap, kbindd. rewrite mfmap_to_mbindd.
    fequal. ext k [w a]. unfold compose. cbn.
    compare values k and j. cbn.
    now autorewrite with tea_tgt_eq.
    now autorewrite with tea_tgt_neq.
  Qed.

End DecoratedMonad.

(** ** Decorated functors (<<kfmapd>>) *)
(******************************************************************************)
Section DecoratedFunctor.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    {j : K}.

  (** *** Composition and identity law *)
  (******************************************************************************)
    Theorem kfmapd_id : forall A,
      kfmapd S j (extract (W ×)) = @id (S A).
  Proof.
    intros. unfold kfmapd.
    rewrite <- (mfmapd_id S).
    fequal. ext k. compare values j and k.
    - now autorewrite with tea_tgt.
    - now autorewrite with tea_tgt.
  Qed.

  Theorem kfmapd_kfmapd : forall A,
    forall (g : W * A -> A) (f : W * A -> A),
      kfmapd S j g ∘ kfmapd S j f =
      kfmapd S j (fun '(w, a) => g (w, f (w, a))).
  Proof.
    intros. unfold kfmapd.
    rewrite (mfmapd_mfmapd S). fequal.
    ext k [w a]. compare values j and k.
    - now autorewrite with tea_tgt.
    - now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma kfmapd_comp_mret_eq : forall A,
    forall (f : W * A -> A) (a : A),
      kfmapd (T j) j f (mret T j a) = mret T j (f (Ƶ, a)).
  Proof.
    intros. unfold kfmapd. rewrite mfmapd_comp_mret.
    now autorewrite with tea_tgt.
  Qed.

  Lemma kfmapd_comp_mret_neq : forall A,
    forall (k : K) (neq : k <> j) (f : W * A -> A) (a : A),
      kfmapd (T k) j f (mret T k a) = mret T k a.
  Proof.
    intros. unfold kfmapd. rewrite mfmapd_comp_mret.
    now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma kfmap_to_kfmapd {A} (f : A -> A) :
    kfmap S j f = kfmapd S j (fun '(w, a) => f a).
  Proof.
    reflexivity.
  Qed.

End DecoratedFunctor.

(** ** Monads (<<kbind>>) *)
(******************************************************************************)
Section Monad.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    {j : K}.

  (** *** Composition and identity law *)
  (******************************************************************************)
    Theorem kbind_id : forall A,
      kbind S j (mret T j) = @id (S A).
  Proof.
    intros. unfold kbind.
    rewrite <- (mbind_id S). fequal.
    ext k. compare values j and k.
    - now autorewrite with tea_tgt_eq.
    - now autorewrite with tea_tgt_neq.
  Qed.

  Theorem kbind_kbind : forall A,
      forall (g f : A -> T j A),
        kbind S j g ∘ kbind S j f =
        kbind S j (fun (a : A) => kbind (T j) j g (f a)).
  Proof.
    intros. unfold kbind.
    rewrite (mbind_mbind S). fequal.
    ext k a. compare values j and k.
    - now autorewrite with tea_tgt_eq.
    - autorewrite with tea_tgt_neq.
      rewrite (mbind_comp_mret k).
      now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma kbind_comp_mret_eq : forall A,
    forall (f : A -> T j A) (a : A),
      kbind (T j) j f (mret T j a) = f a.
  Proof.
    intros. unfold kbind. rewrite mbind_comp_mret.
    now autorewrite with tea_tgt_eq.
  Qed.

  Lemma kbind_comp_mret_neq : forall A,
    forall (i : K) (Hneq : j <> i) (f : A -> T j A) (a : A),
      kbind (T i) j f (mret T i a) = mret T i a.
  Proof.
    intros. unfold kbind. rewrite mbind_comp_mret.
    now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Lesser operations as special cases *)
  (******************************************************************************)
  Lemma kfmap_to_kbind {A} (f : A -> A) :
    kfmap S j f = kbind S j (mret T j ∘ f).
  Proof.
    unfold kfmap, kbind.
    rewrite mfmap_to_mbind.
    fequal. ext k. compare values j and k.
    now autorewrite with tea_tgt_eq.
    now autorewrite with tea_tgt_neq.
  Qed.

End Monad.

(** ** Functors (<<kfmap>>) *)
(******************************************************************************)
Section Functor.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    {j : K}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem kfmap_id : forall A,
      kfmap S j (@id A) = @id (S A).
  Proof.
    intros. unfold kfmap.
    rewrite <- (mfmap_id S).
    fequal. ext k. compare values k and j.
    now autorewrite with tea_tgt_eq.
    now autorewrite with tea_tgt_neq.
  Qed.

  Theorem kfmap_kfmap : forall (A : Type) (g f : A -> A),
      kfmap S j g ∘ kfmap S j f = kfmap S j (g ∘ f).
  Proof.
    intros. unfold kfmap.
    rewrite (mfmap_mfmap S). fequal.
    ext k. unfold Category.comp, kconst_comp.
    compare values j and k.
    - now autorewrite with tea_tgt_eq.
    - now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Naturality w.r.t. <<mret>> *)
  (******************************************************************************)
  Lemma kfmap_comp_kret_eq {A} :
    forall (f : A -> A) (a : A),
      kfmap (T j) j f (mret T j a) = mret T j (f a).
  Proof.
    intros. unfold kfmap. rewrite mfmap_comp_mret.
    now rewrite tgt_eq.
  Qed.

  Lemma kfmap_comp_kret_neq {A} :
    forall (i : K) (Hneq : j <> i) (f : A -> A) (a : A),
      kfmap (T i) j f (mret T i a) = mret T i a.
  Proof.
    intros. unfold kfmap. rewrite mfmap_comp_mret.
    rewrite tgt_neq; auto.
  Qed.

  (** *** Fusion of <<kfmap>> with <<kbindd>> *)
  (******************************************************************************)
  Lemma kfmap_kbindd {A} : forall
      (g : A -> A) (f : W * A -> T j A),
      kfmap S j g ∘ kbindd S j f = kbindd S j (fun '(w, a) => kfmap (T j) j g (f (w, a))).
  Proof.
    intros. unfold kfmap, kbindd. rewrite mfmap_to_mbindd.
    rewrite (mbindd_mbindd S). fequal. ext k [w a].
    compare values j and k.
    - autorewrite with tea_tgt_eq.
      rewrite mfmap_to_mbindd. fequal.
      ext k' [w' a']. unfold compose; cbn. reflexivity.
    - autorewrite with tea_tgt_neq. unfold compose; cbn.
      rewrite (mbindd_comp_mret). rewrite tgt_neq; auto.
  Qed.

End Functor.
