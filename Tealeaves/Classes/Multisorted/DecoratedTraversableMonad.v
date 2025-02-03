From Tealeaves Require Export
  Categories.TypeFamily
  Classes.Monoid
  Classes.Functor
  Classes.Categorical.Applicative
  Classes.Multisorted.Multifunctor
  Functors.Writer.

Import Categorical.Monad (Return, ret).

Import TypeFamily.Notations.
Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables A B C F G ϕ W T U.

(** * Multisorted DTMs *)
(**********************************************************************)
Section MultisortedDTM_typeclasses.

  Context
    `{ix: Index}.

  (** ** Operations *)
  (********************************************************************)
  Section operations.

    Context
      (W: Type)
      (T: K -> Type -> Type)
      (U: Type -> Type).

    Class MReturn :=
      mret: forall (A: Type) (k: K), A -> T k A.

    Class MBind :=
      mbinddt: forall (F: Type -> Type) `{Map F} `{Pure F} `{Mult F} {A B: Type},
          (forall (k: K), W * A -> F (T k B)) -> U A -> F (U B).

  End operations.

  (** ** Kleisli Composition *)
  (********************************************************************)
  Definition compose_dtm
    {W: Type}
    {T: K -> Type -> Type}
    `{mn_op: Monoid_op W}
    `{mn_unit: Monoid_unit W}
    `{Map F} `{Mult F} `{Pure F}
    `{Map G} `{Mult G} `{Pure G}
    `{forall k, MBind W T (T k)}
    {A B C: Type}
    (g: forall k, W * B -> G (T k C))
    (f: forall k, W * A -> F (T k B)): forall k, W * A -> F (G (T k C)) :=
    fun (k: K) '(w, a) =>
      map (F := F)
        (mbinddt W T (T k) G (g ◻ allK (incr w))) (f k (w, a)).

  Infix "⋆dtm" := compose_dtm (at level 40): tealeaves_scope.

  (** ** Typeclasses *)
  (********************************************************************)

  (** *** PreModules *)
  (********************************************************************)
  Section PreModule.

    Context
      (W: Type)
      (T: K -> Type -> Type)
      (U: Type -> Type)
      `{! MReturn T}
      `{! MBind W T U}
      `{! forall k, MBind W T (T k)}
      {mn_op: Monoid_op W}
      {mn_unit: Monoid_unit W}.

    Class MultiDecoratedTraversablePreModule :=
      { dtp_monoid :> Monoid W;
        dtp_mbinddt_mret: forall A,
          mbinddt W T U (fun a => a) (mret T A ◻ allK extract) = @id (U A);
        dtp_mbinddt_mbinddt: forall
          (F: Type -> Type)
          (G: Type -> Type)
          `{Applicative F}
          `{Applicative G}
          `(g: forall k, W * B -> G (T k C))
          `(f: forall k, W * A -> F (T k B)),
          map (F := F) (mbinddt W T U G g) ∘ mbinddt W T U F f =
            mbinddt W T U (F ∘ G) (g ⋆dtm f);
        dtp_mbinddt_morphism: forall
          (F: Type -> Type)
          (G: Type -> Type)
          `{ApplicativeMorphism F G ϕ}
          `(f: forall k, W * A -> F (T k B)),
          ϕ (U B) ∘ mbinddt W T U F f =
            mbinddt W T U G ((fun k => ϕ (T k B)) ◻ f);
      }.

  End PreModule.

  (** *** DTMs *)
  (********************************************************************)
  Section DTM.

    Context
      (W: Type)
      (T: K -> Type -> Type)
      `{! MReturn T}
      `{! forall k, MBind W T (T k)}
      {mn_op: Monoid_op W}
      {mn_unit: Monoid_unit W}.

    Class MultiDecoratedTraversableMonad :=
      { dtm_pre :> forall k, MultiDecoratedTraversablePreModule W T (T k);
        dtm_mbinddt_comp_mret:
        forall k F `{Applicative F}
          `(f: forall k, W * A -> F (T k B)),
          mbinddt W T (T k) F f ∘ mret T A k = f k ∘ pair Ƶ;
      }.

  End DTM.

End MultisortedDTM_typeclasses.

Arguments mret {ix} _%function_scope {MReturn} {A}%type_scope _ _.
Arguments mbinddt {ix} {W}%type_scope {T} (U)%function_scope {MBind} F%function_scope {H H0 H1} {A B}.

#[local] Infix "⋆dtm" := compose_dtm (at level 40): tealeaves_scope.

(** ** Operation <<mapMret>> *)
(********************************************************************)
Section mapMret.

  Context
  `{ix: Index}
  `{! MReturn T}.

  Definition mapMret
    `{Map F} {A:Type}:
    forall (k: K), F A -> F (T k A) :=
    vec_apply (fun k => map (A := A) (B := T k A)) (mret T).

  Lemma vec_compose_mret {W A B}:
    forall (f: K -> W * A -> B) (k:K),
      (mret T ◻ f) k =
        (mret T k ∘ f k).
  Proof.
    reflexivity.
  Qed.

  Lemma vec_compose_mapMret {W A B} `{Functor F}:
    forall (f: K -> W * A -> F B) (k:K),
      (mapMret (F := F) ◻ f) k =
        (map (F := F) (mret T k) ∘ f k).
  Proof.
    reflexivity.
  Qed.

End mapMret.

(** ** Lemmas for Kleisli Composition *)
(********************************************************************)
Section multisorted_dtm_kleisli_composition.

  Context
    `{ix: Index}
    {W: Type}
    {T: K -> Type -> Type}
    {U: Type -> Type}
    `{! MReturn T}
    `{! MBind W T U}
    `{! forall k, MBind W T (T k)}
    {mn_op: Monoid_op W}
    {mn_unit: Monoid_unit W}.

  Context
    `{Applicative G}
    `{Applicative F}
    `{! Monoid W}
    {A B C: Type}
    {g: forall k, W * B -> G (T k C)}.

  Lemma compose_dtm_incr
    {f: forall k, W * A -> F (T k B)}:
      forall (w: W),
        (fun (k: K) => (g ⋆dtm f) k ∘ incr w) =
          ((fun (k: K) => g k ∘ incr w) ⋆dtm (fun (k: K) => f k ∘ incr w)).
  Proof.
    intros. ext k [w' a].
    cbn. do 2 fequal.
    ext j [w'' b].
    unfold vec_compose, compose. cbn. fequal.
    now rewrite monoid_assoc.
  Qed.

  Lemma compose_dtm_incr_alt
    {f: forall k, W * A -> F (T k B)}:
    forall (w: W),
      vec_compose
        (C := fun (k: K) => F (G (T k C)))
        (g ⋆dtm f) (allK (incr w)) =
        (g ◻ allK (incr w)) ⋆dtm (f ◻ allK (incr w)).
  Proof.
    intros.
    ext k [w' a].
    cbn. do 2 fequal.
    ext j [w'' b].
    unfold vec_compose, compose.
    cbn. fequal.
    now rewrite monoid_assoc.
  Qed.

  Context
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma compose_dtm_lemma1
    {f: forall (k:K), W * A -> B}:
      g ⋆dtm (mret T ◻ f) =
        (fun (k: K) '(w, a) => g k (w, f k (w, a))).
  Proof.
    intros.
    unfold compose_dtm.
    ext k [w a].
    unfold_ops @Map_I.
    rewrite vec_compose_mret.
    unfold compose.
    compose near (f k (w, a)) on left.
    rewrite (dtm_mbinddt_comp_mret W T k); auto.
    rewrite vec_compose_k.
    reassociate -> on left.
    unfold allK, const.
    rewrite pair_incr_zero.
    reflexivity.
  Qed.

  Lemma compose_dtm_lemma2
    {f: forall (k:K), W * A -> F B}:
      g ⋆dtm (mapMret (F := F) ◻ f) =
        (fun (k: K) '(w, a) =>
           map (F := F) (g k ∘ pair w) (f k (w, a))).
  Proof.
    intros.
    unfold compose_dtm.
    ext k [w a].
    rewrite vec_compose_mapMret.
    unfold compose.
    compose near (f k (w, a)) on left.
    rewrite fun_map_map.
    rewrite (dtm_mbinddt_comp_mret W T k); auto.
    rewrite vec_compose_k.
    reassociate -> on left.
    unfold allK, const.
    rewrite pair_incr_zero.
    reflexivity.
  Qed.

End multisorted_dtm_kleisli_composition.

(** ** Purity Law *)
(**********************************************************************)
Section DTM_laws.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  Lemma mbinddt_pure: forall (A: Type) `{Applicative F},
      (let p := ((fun k => (@pure F _ (T k A))): forall k, T k A -> F (T k A)) in
       let r := (@mret ix T _ A) in
       let e := (allK extract): forall k, W * A -> A
       in mbinddt U F (p ◻ r ◻ e)) = pure (A := U A).
  Proof.
    intros.
    cbn zeta.
    rewrite vec_compose_assoc.
    rewrite <- (dtp_mbinddt_morphism W T U (fun x => x) F (ϕ := @pure F _)).
    rewrite (dtp_mbinddt_mret W T U).
    reflexivity.
  Qed.

End DTM_laws.

(** * Derived Instances *)
(**********************************************************************)
Section derived_operations.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}.

  (** ** Derived Multisorted Operations *)
  (********************************************************************)
  Section definitions.

    Context
      {A B: Type}
      (F: Type -> Type)
      `{Map F} `{Mult F} `{Pure F}.

    Definition mbindd (f: forall k, W * A -> T k B): U A -> U B :=
      mbinddt U (fun x => x) f.

    Definition mmapdt (f: forall (k: K), W * A -> F B): U A -> F (U B) :=
      mbinddt U F (mapMret (T := T) ◻ f).

    Definition mbindt (f: forall k, A -> F (T k B)): U A -> F (U B) :=
      mbinddt U F (f ◻ allK extract).

    Definition mbind (f: forall k, A -> T k B): U A -> U B :=
      mbindd (f ◻ allK extract).

    Definition mmapd (f: forall k, W * A -> B): U A -> U B :=
      mbindd (mret T ◻ f).

    Definition mmapt (f: forall k, A -> F B): U A -> F (U B) :=
      mmapdt (f ◻ allK extract).

    Definition mmap (f: forall k, A -> B): U A -> U B :=
      mmapd (f ◻ allK extract).

  End definitions.

  (** ** Rewriting Rules *)
  (********************************************************************)
  Section special_cases.

    Context
      {A B: Type}
      (F: Type -> Type)
      `{Map F} `{Mult F} `{Pure F}.

    (** *** Special cases of <<mbinddt>> *)
    (******************************************************************)
    Lemma mbindt_to_mbinddt (f: forall k, A -> F (T k B)):
      mbindt F f = mbinddt U F (f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    Lemma mbindd_to_mbinddt (f: forall k, W * A -> T k B):
      mbindd f = mbinddt U (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mmapdt_to_mbinddt (f: K -> W * A -> F B):
      mmapdt F f = mbinddt U F (mapMret (T := T) ◻ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mbind_to_mbinddt (f: forall k, A -> T k B):
      mbind f = mbinddt U (fun A => A) (f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    Lemma mmapd_to_mbinddt (f: K -> W * A -> B):
      mmapd f = mbinddt U (fun A => A) (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mmapt_to_mbinddt (f: K -> A -> F B):
      mmapt F f = mbinddt U F (mapMret (T := T)
                                 ◻ f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    Lemma mmap_to_mbinddt (f: K -> A -> B):
      mmap f = mbinddt U (fun A => A) (mret T ◻ f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    (** *** Special Cases of <<mbindt>> *)
    (******************************************************************)
    Lemma mbind_to_mbindt (f: forall k, A -> T k B):
      mbind f = mbindt (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mmapt_to_mbindt (f: K -> A -> F B):
      mmapt F f = mbindt F (mapMret (T := T) ◻ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mmap_to_mbindt (f: K -> A -> B):
      mmap f = mbindt (fun A => A) (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

    (** *** Special Cases of <<mbindd>> *)
    (******************************************************************)
    Lemma mbind_to_mbindd (f: forall k, A -> T k B):
      mbind f = mbindd (f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    Lemma mmapd_to_mbindd (f: W * A -k-> B):
      mmapd f = mbindd (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mmap_to_mbindd (f: A -k-> B):
      mmap f = mbindd (mret T ◻ f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    (** *** Special Cases of <<mbindd>> *)
    (******************************************************************)
    Lemma mmapd_to_mmapdt (f: K -> W * A -> B):
      mmapd f = mmapdt (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mmap_to_mmapdt (f: K -> A -> B):
      mmap f = mmapdt (fun A => A) (f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    Lemma mmapt_to_mmapdt (f: K -> A -> F B):
      mmapt F f = mmapdt F (f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    (** *** Special Cases of <<mmapt>> *)
    (******************************************************************)
    Lemma mmap_to_mmapt (f: K -> A -> B):
      mmap f = mmapt (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    (** *** Special Cases of <<mmapd>> *)
    (******************************************************************)
    Lemma mmap_to_mmapd (f: K -> A -> B):
      mmap f = mmapd (f ◻ allK extract).
    Proof.
      reflexivity.
    Qed.

    (** *** Special Cases of <<mbind>> *)
    (******************************************************************)
    Lemma mmap_to_mbind (f: K -> A -> B):
      mmap f = mbind (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

  End special_cases.

End derived_operations.

(** ** Composition Between <<mbinddt>> and Other Operations *)
(** Compositions laws for compositions of the form <<mbinddt ∘ xxx>> or
    <<xxx ∘ mbinddt>> *)
(**********************************************************************)
Section derived_operations_composition.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}
    `{Applicative F}
    `{Applicative G}
    {A B C: Type}.

  (** *** <<mbinddt>> on the right *)
  (********************************************************************)
  Lemma mbindd_mbinddt: forall
      (g: forall k, W * B -> T k C)
      (f: forall k, W * A -> F (T k B)),
      map (F := F) (mbindd U g) ∘ mbinddt U F f =
        mbinddt U F
          (fun k '(w, a) =>
             map (F := F)
               (mbindd (T k) (g ◻ allK (incr w))) (f k (w, a))).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F (fun A => A)).
    fequal. now erewrite Mult_compose_identity1.
  Qed.

  Lemma mmapdt_mbinddt: forall
      (g: K -> W * B -> G C)
      (f: forall k, W * A -> F (T k B)),
      map (F := F) (mmapdt U G g) ∘ mbinddt U F f =
        mbinddt U (F ∘ G)
          (fun k '(w, a) =>
             map (F := F)
               (mmapdt (T k) G (g ◻ allK (incr w))) (f k (w, a))).
  Proof.
    intros. rewrite mmapdt_to_mbinddt.
    now rewrite (dtp_mbinddt_mbinddt W T U F G).
  Qed.

  Lemma mbindt_mbinddt: forall
      (g: forall k, B -> G (T k C))
      (f: forall k, W * A -> F (T k B)),
      map (F := F) (mbindt U G g) ∘ mbinddt U F f =
        mbinddt U (F ∘ G)
          (fun k => map (F := F) (mbindt (T k) G g) ∘ f k).
  Proof.
    intros. rewrite mbindt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F G).
    fequal. ext k [w a]. unfold compose; cbn.
    fequal. rewrite mbindt_to_mbinddt.
    fequal. now ext j [w2 b].
  Qed.

  Lemma mbind_mbinddt: forall
      (g: forall k, B -> T k C)
      (f: forall k, W * A -> F (T k B)),
      map (F := F) (mbind U g) ∘ mbinddt U F f =
        mbinddt U F ((fun k => map (F := F) (mbind (T k) g)) ◻ f).
  Proof.
    intros. rewrite mbind_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F (fun A => A)).
    fequal.
    - now erewrite Mult_compose_identity1.
    - unfold vec_compose, compose, compose_dtm.
      ext k [w a].
      fequal. rewrite mbind_to_mbinddt. fequal.
      now ext j [w2 b].
  Qed.

  Lemma mmapd_mbinddt: forall
      (g: K -> W * B -> C)
      (f: forall k, W * A -> F (T k B)),
      map (F := F) (mmapd U g) ∘ mbinddt U F f =
        mbinddt U F
          (fun k '(w, a) =>
             map (F := F)
               (mmapd (T k) (g ◻ allK (incr w))) (f k (w, a))).
  Proof.
    intros. rewrite mmapd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F (fun A => A)).
    fequal. now erewrite Mult_compose_identity1.
  Qed.

  Lemma mmapt_mbinddt: forall
      (g: K -> B -> G C)
      (f: forall k, W * A -> F (T k B)),
      map (F := F) (mmapt U G g) ∘ mbinddt U F f =
        mbinddt U (F ∘ G)
          (fun k => map (F := F) (mmapt (T k) G g) ∘ f k).
  Proof.
    intros. rewrite mmapt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F G).
    fequal. ext k [w a]. unfold compose; cbn.
    fequal. rewrite mmapt_to_mbinddt.
    fequal. now ext j [w2 b].
  Qed.

  Lemma mmap_mbinddt: forall
      (g: K -> B -> C)
      (f: forall k, W * A -> F (T k B)),
      map (F := F) (mmap U g) ∘ mbinddt U F f =
        mbinddt U F (fun k => map (F := F) (mmap (T k) g) ∘ f k).
  Proof.
    intros. unfold mmap. rewrite mmapd_mbinddt.
    fequal. ext k [w a]. unfold compose; cbn.
    fequal. fequal. now ext j [w2 b].
  Qed.

  (** *** <<mbinddt>> on the left *)
  (********************************************************************)
  Lemma mbinddt_mbindd: forall
      (g: forall k, W * B -> G (T k C))
      (f: forall k, W * A -> T k B),
      mbinddt U G g ∘ mbindd U f =
        mbinddt U G
          (fun k '(w, a) =>
             mbinddt (T k) G (g ◻ allK (incr w)) (f k (w, a))).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    change (mbinddt U G g) with
      (map (F := (fun A => A)) (mbinddt U G g)).
    rewrite (dtp_mbinddt_mbinddt W T U (fun A => A) G).
    fequal. now rewrite (Mult_compose_identity2 G).
  Qed.


  Lemma mbinddt_mmapdt: forall
      (g: forall k, W * B -> G (T k C))
      (f: K -> W * A -> F B),
      map (F := F) (mbinddt U G g) ∘ mmapdt U F f =
        mbinddt U (F ∘ G)
          (fun k '(w, a) => map (F := F) (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F G).
    fequal.
    ext k [w a]. unfold compose; cbn.
    rewrite vec_compose_mapMret.
    unfold compose at 1.
    compose near (f k (w, a)) on left.
    rewrite fun_map_map.
    rewrite (dtm_mbinddt_comp_mret W T k G).
    rewrite vec_compose_allK2.
    reassociate -> on left.
    rewrite pair_incr_zero.
    reflexivity.
  Qed.

  Lemma mbinddt_mbindt: forall
      (g: forall k, W * B -> G (T k C))
      (f: forall k, A -> F (T k B)),
      map (F := F) (mbinddt U G g) ∘ mbindt U F f =
        mbinddt U (F ∘ G)
          (fun k '(w, a) =>
             map (F := F)
               (mbinddt (T k) G (g ◻ allK (incr w))) (f k a)).
  Proof.
    intros.
    rewrite mbindt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F G).
    reflexivity.
  Qed.

  Lemma mbinddt_mbind: forall
      (g: forall k, W * B -> G (T k C))
      (f: forall k, A -> T k B),
      mbinddt U G g ∘ mbind U f =
        mbinddt U G
          (fun k '(w, a) =>
             mbinddt (T k) G (g ◻ allK (incr w)) (f k a)).
  Proof.
    intros. rewrite mbind_to_mbinddt.
    change (mbinddt U G g) with (map (F := fun A => A) (mbinddt U G g)).
    rewrite (dtp_mbinddt_mbinddt W T U (fun A => A) G).
    fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma mbinddt_mmapd: forall
      (g: forall k, W * B -> G (T k C))
      (f: forall k, W * A -> B),
      mbinddt U G g ∘ mmapd U f =
        mbinddt U G (fun k '(w, a) => g k (w, f k (w, a))).
  Proof.
    intros.
    erewrite mmapd_to_mbinddt.
    change (mbinddt U G g) with (map (F := fun A => A) (mbinddt U G g)).
    rewrite (dtp_mbinddt_mbinddt W T U (fun A => A) G).
    fequal. now rewrite (Mult_compose_identity2 G).
    rewrite compose_dtm_lemma1.
    reflexivity.
  Qed.

  Lemma mbinddt_mmapt: forall
      (g: forall k, W * B -> G (T k C))
      (f: K -> A -> F B),
      map (F := F) (mbinddt U G g) ∘ mmapt U F f =
        mbinddt U (F ∘ G)
          (fun k '(w, a) => map (F := F) (fun b => g k (w, b)) (f k a)).
  Proof.
    intros.
    rewrite mmapt_to_mmapdt.
    rewrite mbinddt_mmapdt.
    reflexivity.
  Qed.

  Lemma mbinddt_mmap: forall
      (g: forall k, W * B -> G (T k C))
      (f: K -> A -> B),
      mbinddt U G g ∘ mmap U f =
        mbinddt U G (fun k '(w, a) => g k (w, f k a)).
  Proof.
    intros.
    rewrite mmap_to_mmapd.
    rewrite mbinddt_mmapd.
    reflexivity.
  Qed.

End derived_operations_composition.

(** ** Composition between Derived Operations *)
(** Composition laws involving one of <<mbindd>>/<<mmapdt>>/<<mbindt>>
    and another operation that is not a special cases. *)
(**********************************************************************)
Section mixed_composition_laws.

  Context
    (U: Type -> Type)
    (F G: Type -> Type)
    `{Applicative F}
    `{Applicative G}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} {A B C: Type}.

  (** *** <<mbindd>> *)
  (** Operations with traversals are not special cases of <<mbindd>>. *)
  (********************************************************************)
  Lemma mbindd_mmapdt: forall
      (g: forall k, W * B -> T k C)
      (f: forall k, W * A -> F B),
      map (F := F) (mbindd U g) ∘ mmapdt U F f =
        mbinddt U F (fun (k: K) '(w, a) =>
                       map (F := F) (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros. rewrite mmapdt_to_mbinddt.
    rewrite mbindd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F (fun x => x)).
    rewrite compose_dtm_lemma2.
    rewrite (Mult_compose_identity1 F).
    reflexivity.
  Qed.

  Lemma mbindd_mbindt: forall
      (g: forall k, W * B -> T k C)
      (f: forall k, A -> F (T k B)),
      map (F := F) (mbindd U g) ∘ mbindt U F f =
        mbinddt U F
          (fun (k: K) '(w, a) =>
             map (F := F) (mbindd (T k) (g ◻ allK (incr w))) (f k a)).
  Proof.
    intros.
    rewrite mbindd_to_mbinddt.
    rewrite mbindt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F (fun x => x)).
    rewrite (Mult_compose_identity1 F).
    reflexivity.
  Qed.

  Lemma mbindd_mmapt: forall
      (g: forall k, W * B -> T k C)
      (f: forall k, A -> F B),
      map (F := F) (mbindd U g) ∘ mmapt U F f =
        mbinddt U F
          (fun (k: K) '(w, a) =>
             map (F := F) (fun b => g k (w, b)) (f k a)).
  Proof.
    intros.
    rewrite mbindd_to_mbinddt.
    rewrite mmapt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W T U F (fun x => x)).
    rewrite vec_compose_assoc.
    rewrite compose_dtm_lemma2.
    rewrite (Mult_compose_identity1 F).
    reflexivity.
  Qed.

  (* TODO Also need to put <<mmapt_mbindd>> somewhere. *)

  (** *** <<mmapdt>> *)
  (** Operations with joins are not special cases of <<mmapdt>>. *)
  (********************************************************************)
  Lemma mmapdt_mbindd: forall
      (g: forall k, W * B -> G C)
      (f: forall k, W * A -> T k B),
      mmapdt U G g ∘ mbindd U f =
        mbinddt U G
          (fun (k: K) '(w, a) =>
             mmapdt (T k) G (g ◻ allK (incr w)) (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  Lemma mmapdt_mbindt: forall
      (g: forall k, W * B -> G C)
      (f: forall k, A -> F (T k B)),
      map (F := F) (mmapdt U G g) ∘ mbindt U F f =
        mbinddt U (F ∘ G)
          (fun (k: K) '(w, a) =>
             map (F := F) (mmapdt (T k) G (g ◻ allK (incr w))) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  Lemma mmapdt_mbind: forall
      (g: K -> W * B -> G C) (f: forall k, A -> T k B),
      mmapdt U G g ∘ mbind U f =
        mbinddt U G (fun k '(w, a) =>
                       mmapdt (T k) G (g ◻ allK (incr w)) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  (* TODO Also need to put <<mbind_mmapdt>> somewhere. *)

  (** *** <<mbindt>> *)
  (** Operations with decorations are not special cases of <<mbindt>>. *)
  (********************************************************************)
  Lemma mbindt_mbindd: forall
      (g: forall k, B -> G (T k C))
      (f: forall k, W * A -> T k B),
      mbindt U G g ∘ mbindd U f =
        mbinddt U G (fun (k: K) '(w, a) => mbindt (T k) G g (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  Lemma mbindt_mmapdt: forall
      (g: forall k, B -> G (T k C))
      (f: forall k, W * A -> F B),
      map (F := F) (mbindt U G g) ∘ mmapdt U F f =
        mbinddt U (F ∘ G)
          (fun (k: K) '(w, a) => map (F := F) (g k) (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  (* TODO <<mbindt_mmapd>> *)

  (* TODO Also need to put <<mmapd_mbindt>> somewhere. *)

End mixed_composition_laws.

(** ** Decorated Monad (<<mbindd>>) *)
(**********************************************************************)
Definition compose_dm
  `{ix: Index}
  {W: Type}
  {T: K -> Type -> Type}
  `{mn_op: Monoid_op W}
  `{mn_unit: Monoid_unit W}
  `{forall k, MBind W T (T k)}
  {A B C: Type}
  (g: forall k, W * B -> T k C)
  (f: forall k, W * A -> T k B): forall k, W * A -> T k C :=
  fun k '(w, a) => mbindd (T k) (g ◻ allK (incr w)) (f k (w, a)).

Infix "⋆dm" := compose_dm (at level 40).

Section DecoratedMonad.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} {A B C: Type}.

  (** *** Composition and identity law *)
  (********************************************************************)
  Theorem mbindd_id:
    mbindd U (mret T ◻ allK extract) = @id (U A).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    now rewrite <- (dtp_mbinddt_mret W T U).
  Qed.

  Theorem mbindd_mbindd: forall
      (g: W * B ~k~> T C)
      (f: W * A ~k~> T B),
      mbindd U g ∘ mbindd U f =
        mbindd U (fun (k: K) '(w, a) =>
                    mbindd (T k) (g ◻ allK (incr w)) (f k (w, a))).
  Proof.
    intros.
    rewrite 3mbindd_to_mbinddt.
    change_left (map (F := fun x => x)
                   (mbinddt U (fun x: Type => x) g) ∘
                   (mbinddt U (fun x: Type => x) f)).
    rewrite (dtp_mbinddt_mbinddt W T U (fun x => x) (fun x => x)).
    rewrite Mult_compose_identity2.
    reflexivity.
  Qed.

  (** *** Right unit law for monads *)
  (********************************************************************)
  Theorem mbindd_comp_mret: forall
      (k: K) (f: forall k, W * A -> T k B),
      mbindd (T k) f ∘ mret T k = f k ∘ ret (T := (W ×)).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    now rewrite (dtm_mbinddt_comp_mret W T k (fun A => A)).
  Qed.

  (** *** Composition with special cases on the right *)
  (** Composition with operations <<mbind>>/<<mmapd>>/<<mmap>> *)
  (********************************************************************)
  Lemma mbindd_mbind: forall
      (g: forall k, W * B -> T k C)
      (f: A ~k~> T B),
      mbindd U g ∘ mbind U f =
        mbindd U (fun (k: K) '(w, a) =>
                    mbindd (T k) (g ◻ allK (incr w)) (f k a)).
  Proof.
    intros. rewrite mbind_to_mbindd.
    now rewrite mbindd_mbindd.
  Qed.

  Lemma mbindd_mmapd: forall
      (g: forall k, W * B -> T k C)
      (f: forall k, W * A -> B),
      mbindd U g ∘ mmapd U f =
        mbindd U (fun (k: K) '(w, a) => g k (w, f k (w, a))).
  Proof.
    intros. rewrite mmapd_to_mbindd.
    rewrite (mbindd_mbindd).
    fequal. ext k [w a].
    unfold vec_compose, compose; cbn.
    compose near (f k (w, a)).
    rewrite mbindd_to_mbinddt.
    rewrite (dtm_mbinddt_comp_mret W T k (fun A => A)).
    unfold compose; cbn. now simpl_monoid.
  Qed.

  Lemma mbindd_mmap: forall
      (g: forall k, W * B -> T k C)
      (f: forall k, A -> B),
      mbindd U g ∘ mmap U f =
        mbindd U (fun (k: K) '(w, a) => g k (w, f k a)).
  Proof.
    intros. unfold mmap.
    now rewrite (mbindd_mmapd).
  Qed.

  (** *** Composition with special cases on the left *)
  (********************************************************************)
  Lemma mbind_mbindd: forall
      (g: forall k, B -> T k C)
      (f: forall k, W * A -> T k B),
      mbind U g ∘ mbindd U f =
        mbindd U (fun (k: K) => mbind (T k) g ∘ f k).
  Proof.
    intros.
    rewrite mbind_to_mbindd.
    rewrite mbindd_mbindd.
    fequal.
    ext k [w a].
    unfold mbind, compose.
    fequal.
    now ext j [w2 b].
  Qed.

  Lemma mmapd_mbindd: forall
      (g: forall k, W * B -> C)
      (f: forall k, W * A -> T k B),
      mmapd U g ∘ mbindd U f =
        mbindd U (fun (k: K) '(w, a) =>
                    mmapd (T k) (g ◻ allK (incr w)) (f k (w, a))).
  Proof.
    intros.
    rewrite mmapd_to_mbindd.
    rewrite mbindd_mbindd.
    reflexivity.
  Qed.

  Lemma mmap_mbindd: forall
      (g: forall k, B -> T k C)
      (f: forall k, W * A -> T k B),
      mbind U g ∘ mbindd U f =
        mbindd U (fun (k: K) => mbind (T k) g ∘ f k).
  Proof.
    intros.
    rewrite mbind_to_mbindd.
    rewrite mbindd_mbindd.
    fequal.
    ext k [w a]. unfold compose; cbn.
    rewrite mbind_to_mbindd. fequal.
    now ext j [w2 b].
  Qed.

End DecoratedMonad.

(** ** Decorated Traversable Functor (<<mmapdt>>) *)
(**********************************************************************)
Section DecoratedTraversable.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} {A B C: Type}
    `{Applicative F} `{Applicative G}.

  (** *** Composition and identity law *)
  (********************************************************************)
  Theorem mmapdt_id:
    mmapdt U (fun x => x) (allK extract) = @id (U A).
  Proof.
    intros.
    unfold mmapdt.
    rewrite <- (dtp_mbinddt_mret W T U).
    reflexivity.
  Qed.

  Theorem mmapdt_mmapdt: forall
      (g: forall k, W * B -> G C) (f: forall k, W * A -> F B),
      map (F := F) (mmapdt U G g) ∘ mmapdt U F f =
        mmapdt U (F ∘ G)
          (fun (k: K) '(w, a) =>
             map (F := F) (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros.
    unfold mmapdt.
    rewrite (dtp_mbinddt_mbinddt W T U F G).
    unfold compose_dtm.
    fequal. ext k [w a].
    unfold vec_compose, mapMret, vec_apply, compose, allK, const.
    compose near (f k (w, a)).
    rewrite (fun_map_map).
    unfold_ops @Map_compose.
    rewrite (fun_map_map).
    rewrite (dtm_mbinddt_comp_mret W T k G).
    fequal. ext b. unfold compose.
    compose near b.
    erewrite pair_incr_zero.
    now simpl_monoid.
  Qed.

  (** *** Composition with <<mret>> *)
  (********************************************************************)
  Lemma mmapdt_comp_mret: forall
      (k: K) (f: forall k, W * A -> F B),
      mmapdt (T k) F f ∘ mret T k = map (F := F) (mret T k) ∘ f k ∘ pair Ƶ.
  Proof.
    intros. unfold mmapdt.
    now rewrite (dtm_mbinddt_comp_mret W T k F).
  Qed.

  (** *** Purity *)
  (********************************************************************)
  Lemma mmapdt_pure:
    mmapdt U F (allK pure ◻ allK extract) = pure (A := U A).
  Proof.
    intros.
    unfold mmapdt.
    rewrite <- vec_compose_assoc.
    replace (mapMret (A := A) ◻ allK pure) with
      ((fun k => pure (F := F)) ◻ mret (A := A) T).
    { rewrite vec_compose_assoc.
      rewrite <- (dtp_mbinddt_morphism W T U (fun x => x) F (ϕ := @pure F _)).
      now rewrite (dtp_mbinddt_mret W T U). }
    { unfold vec_compose. ext k.
      unfold mapMret, allK, const.
      ext a. unfold compose.
      rewrite <- app_pure_natural.
      reflexivity. }
  Qed.

  (** *** Composition with special cases  on the right *)
  (********************************************************************)
  Lemma mmapdt_mmapt: forall
      (g: K -> W * B -> G C) (f: K -> A -> F B),
      map (F := F) (mmapdt U G g) ∘ mmapt U F f =
        mmapdt U (F ∘ G) (fun (k: K) '(w, a) => map (F := F) (fun b => g k (w, b)) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  Lemma mmapdt_mmapd: forall
      (g: K -> W * B -> G C) (f: K -> W * A -> B),
      mmapdt U G g ∘ mmapd U f = mmapdt U G (fun k '(w, a) => g k (w, f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  (* TODO <<mmapdt_mmap>> *)

  (** *** Composition with other operations on the left *)
  (********************************************************************)
  Lemma mmapd_mmapdt: forall
      (g: K -> W * B -> C) (f: K -> W * A -> F B),
      map (F := F) (mmapd U g) ∘ mmapdt U F f =
        mmapdt U F (fun k '(w, a) => map (F := F) (fun (b: B) => (g k (w, b))) (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  Lemma mmapt_mmapdt: forall
      (g: K -> B -> C) (f: K -> W * A -> F B),
      map (F := F) (mmap U g) ∘ mmapdt U F f = mmapdt U F (fun k => map (F := F) (g k) ∘ f k).
  Proof.
    (* TODO *)
  Abort.

  (* TODO <<mmap_mmapdt>> *)

End DecoratedTraversable.

(** ** Traversable Monad (<<mbindt>>) *)
(**********************************************************************)
Section TraversableMonad.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}
    {A B C: Type}
    (F G: Type -> Type)
    `{Applicative F} `{Applicative G}.

  (** *** Composition and identity law *)
  (********************************************************************)
  Theorem mbindt_id:
    mbindt U (fun x => x) (mret T) = @id (U A).
  Proof.
    intros. unfold mbindt.
    now rewrite (dtp_mbinddt_mret W T U).
  Qed.

  Theorem mbindt_mbindt:
    forall (g: forall k, B -> G (T k C))
      (f: forall k, A -> F (T k B)),
      map (F := F) (mbindt U G g) ∘ mbindt U F f =
        mbindt U (F ∘ G) (fun (k: K) (a: A) => map (F := F) (mbindt (T k) G g) (f k a)).
  Proof.
    intros. unfold mbindt. rewrite (dtp_mbinddt_mbinddt W T U F G).
    fequal. ext k [w a].
    unfold vec_compose, compose; cbn.
    repeat fequal. ext k2 [w2 b]. easy.
  Qed.

  (** *** Composition with <<mret>> *)
  (********************************************************************)
  Lemma mbindt_comp_mret:
    forall (k: K) (f: forall k, A -> F (T k B)),
      mbindt (T k) F f ∘ mret T k = f k.
  Proof.
    intros. unfold mbindt.
    now rewrite (dtm_mbinddt_comp_mret W T k F).
  Qed.

  (** *** Purity *)
  (********************************************************************)
  (* TODO *)

  (** *** Composition with special cases on the right *)
  (********************************************************************)
  (* TODO *)

  (** *** Composition with special cases on the left *)
  (********************************************************************)
  (* TODO *)

End TraversableMonad.

(** ** Heterogeneous Composition Laws *)
(** Composition laws between one of <<mbind>>/<<mmapd>>/<<mmapt>>
    and another operation, neither of which is a special case of the other. *)
(**********************************************************************)
Section mixed_composition_laws2.

  Context
    (U: Type -> Type)
    (F G: Type -> Type)
    `{Applicative F}
    `{Applicative G}
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T} {A B C: Type}.

  (** *** <<mbind>> on the left *)
  (********************************************************************)
  Lemma mbind_mmapd:
    forall (g: forall k, B -> T k C)
      (f: K -> W * A -> B),
      mbind U g ∘ mmapd U f =
        mbindd U (g ◻ f).
  Proof.
    intros.
    rewrite mmapd_to_mbindd.
    rewrite mbind_to_mbindd.
    rewrite (mbindd_mbindd U).
    fequal.
    ext k [w a].
    unfold vec_compose, compose; cbn.
    compose near (f k (w, a)) on left.
    now rewrite (mbindd_comp_mret (T := T)).
  Qed.

  Lemma mbind_mmapt:
    forall (g: forall k, B -> T k C)
      (f: K -> A -> F B),
      map (F := F) (mbind U g) ∘ mmapt U F f =
        mbindt U F (fun k => map (F := F) (g k) ∘ f k).
  Proof.
    intros.
    rewrite (mmapt_to_mbindt U F).
    rewrite mbind_to_mbindt.
    rewrite (mbindt_mbindt U F (fun A => A)).
    fequal.
    - now rewrite (Mult_compose_identity1 F).
    - ext k a. unfold vec_compose, mapMret, vec_apply, compose.
      compose near (f k a) on left.
      rewrite fun_map_map.
      fequal.
      change (mbindt (T k) (fun A0: Type => A0) g)
        with (mbind (T k) g).
      rewrite mbind_to_mbindd.
      rewrite mbindd_comp_mret.
      reflexivity.
  Qed.

  (** *** <<mmapd>> on the left *)
  (********************************************************************)
  Lemma mmapd_mbind:
    forall (g: K -> W * B -> C)
      (f: forall k, A -> T k B),
      mmapd U g ∘ mbind U f =
        mbindd U (fun k '(w, a) =>
                    mmapd (T k) (g ◻ allK (incr w)) (f k a)).
  Proof.
    intros. rewrite mmapd_to_mbindd. rewrite mbind_to_mbindd.
    now rewrite (mbindd_mbindd U).
  Qed.

  Lemma mmapd_mmapt:
    forall (g: K -> W * B -> C)
      (f: forall k, A -> F B),
      map (F := F) (mmapd U g) ∘ mmapt U F f =
        mmapdt U F (fun k '(w, a) =>
                      map (F := F) (fun b => g k (w, b)) (f k a)).
  Proof.
    intros. rewrite mmapd_to_mmapdt. rewrite mmapt_to_mmapdt.
    rewrite (mmapdt_mmapdt U (G := fun A => A)). fequal.
    now rewrite (Mult_compose_identity1 F).
  Qed.

  (** *** <<mmapt>> on the left *)
  (********************************************************************)
  Lemma mmapt_mbind:
    forall (g: K -> B -> G C)
      (f: forall k, A -> T k B),
      mmapt U G g ∘ mbind U f =
        mbindt U G (fun k => mmapt (T k) G g ∘ f k).
  Proof.
    intros.
    rewrite mmapt_to_mbindt.
    rewrite mbind_to_mbindt.
    unfold vec_compose, mapMret, vec_apply.
    change (mbindt U G (fun k: K => map (F := G) (mret T k) ∘ g k))
      with (map (F := fun A => A)
              (mbindt U G (fun k: K => map (F := G) (mret T k) ∘ g k))).
    rewrite (mbindt_mbindt U (fun A => A) G).
    fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

  Lemma mmapt_mmapd:
    forall (g: K -> B -> G C)
      (f: forall k, A -> T k B),
      mmapt U G g ∘ mbind U f =
        mbindt U G (fun k => mmapt (T k) G g ∘ f k).
  Proof.
    intros.
    rewrite mmapt_to_mbindt.
    rewrite mbind_to_mbindt.
    unfold vec_compose, mapMret, vec_apply.
    change (mbindt U G (fun k: K => map (F := G) (mret T k) ∘ g k))
      with (map (F := fun A => A)
              (mbindt U G (fun k: K => map (F := G) (mret T k) ∘ g k))).
    rewrite (mbindt_mbindt U (fun A => A) G).
    fequal. now rewrite (Mult_compose_identity2 G).
  Qed.

End mixed_composition_laws2.

(** ** Monad (<<mbind>>) *)
(**********************************************************************)
Section Monad.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  (** *** Composition and identity law *)
  (********************************************************************)
  Theorem mbind_id: forall A,
      mbind U (fun k => mret T k) = @id (U A).
  Proof.
    intros. rewrite mbind_to_mbindd.
    now rewrite <- (mbindd_id U).
  Qed.

  Theorem mbind_mbind {A B C}:
    forall (g: forall (k: K), B -> T k C) (f: forall (k: K), A -> T k B),
      mbind U g ∘ mbind U f =
        mbind U (fun (k: K) (a: A) => mbind (T k) g (f k a)).
  Proof.
    intros. do 3 rewrite (mbind_to_mbindd U).
    rewrite (mbindd_mbindd U).
    unfold vec_compose, compose; cbn. fequal.
    ext k [w a].
    rewrite (mbind_to_mbindd (T k)).
    cbn. fequal. now ext j [w2 b].
  Qed.

  (** *** Composition with <<mret>> *)
  (********************************************************************)
  Lemma mbind_comp_mret {A B}:
    forall (k: K) (f: forall (k: K), A -> T k B) (a: A),
      mbind (T k) f (mret T k a) = f k a.
  Proof.
    intros. rewrite mbind_to_mbindd.
    compose near a on left. now rewrite mbindd_comp_mret.
  Qed.

  (* TODO <<mbind_mmap>> *)

  (* TODO <<mmap_mbind>> *)

End Monad.

(** ** Decorated Functor (<<mmapd>>) *)
(**********************************************************************)
Section DecoratedFunctor.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  (** *** Composition and identity law *)
  (********************************************************************)
  Theorem mmapd_id: forall A,
      mmapd U (allK extract) = @id (U A).
  Proof.
    intros.
    rewrite mmapd_to_mmapdt.
    rewrite (mmapdt_id U).
    reflexivity.
  Qed.

  Theorem mmapd_mmapd {A B C}:
    forall (g: K -> W * B -> C) (f: K -> W * A -> B),
      mmapd U g ∘ mmapd U f =
        mmapd U (fun (k: K) '(w, a) => g k (w, f k (w, a))).
  Proof.
    intros. do 3 rewrite mmapd_to_mmapdt.
    change (mmapdt U (fun A => A) g) with
      (map (F := fun A => A) (mmapdt U (fun A => A) g)).
    rewrite (mmapdt_mmapdt U (G := fun A => A) (F := fun A => A)).
    unfold compose; cbn. fequal.
    now rewrite (Mult_compose_identity1 (fun A => A)).
  Qed.

  (** *** Composition with <<mret>> *)
  (********************************************************************)
  Lemma mmapd_comp_mret {A B}:
    forall (k: K) (f: K -> W * A -> B) (a: A),
      mmapd (T k) f (mret T k a) = mret T k (f k (Ƶ, a)).
  Proof.
    intros. rewrite mmapd_to_mmapdt. compose near a on left.
    now rewrite (mmapdt_comp_mret (F := fun A => A)).
  Qed.

  (* TODO <<mmapd_mmap>> *)

  (* TODO <<mmap_mmapd>> *)

End DecoratedFunctor.

(** ** Traversable Functor (<<mmapt>>) *)
(**********************************************************************)
Section TraversableFunctor.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  (** *** Composition and identity law *)
  (********************************************************************)
  Theorem mmapt_id: forall A,
      mmapt U (fun A => A) (allK (@id A)) = @id (U A).
  Proof.
    intros. unfold mmapt.
    now rewrite <- (mbindt_id U).
  Qed.

  Theorem mmapt_mmapt {A B C}:
    forall `{Applicative G} `{Applicative F}
      (g: K -> B -> G C) (f: K -> A -> F B),
      map (F := F) (mmapt U G g) ∘ mmapt U F f =
        mmapt U (F ∘ G) (fun (k: K) (a: A) => map (F := F) (g k) (f k a)).
  Proof.
    intros. rewrite (mmapt_to_mmapdt U G).
    rewrite (mmapt_to_mmapdt U F).
    rewrite (mmapt_to_mmapdt U (F ∘ G)).
    rewrite (mmapdt_mmapdt U).
    fequal. now ext k [w a].
  Qed.

  (** *** Composition with <<mret>> *)
  (********************************************************************)
  Lemma mmapt_comp_mret {A B}:
    forall  `{Applicative F} (k: K) (f: K -> A -> F B) (a: A),
      mmapt (T k) F f (mret T k a) = map (F := F) (mret T k) (f k a).
  Proof.
    intros. rewrite (mmapt_to_mmapdt (T k)). compose near a on left.
    now rewrite mmapdt_comp_mret.
  Qed.

  (* TODO <<mmapt_mmap>> *)

  (* TODO <<mmap_mmapt>> *)

End TraversableFunctor.

(** ** Functor (<<mmap>>) *)
(**********************************************************************)
Section Functor.

  Context
    (U: Type -> Type)
    `{MultiDecoratedTraversablePreModule W T U}
    `{! MultiDecoratedTraversableMonad W T}.

  (** *** Composition and identity law *)
  (********************************************************************)
  Theorem mmap_id: forall A,
      mmap U (allK (@id A)) = @id (U A).
  Proof.
    intros. apply (dtp_mbinddt_mret W T U).
  Qed.

  Theorem mmap_mmap {A B C}: forall
      (g: K -> B -> C) (f: K -> A -> B),
      mmap U g ∘ mmap U f = mmap U (g ◻ f).
  Proof.
    intros. do 3 rewrite mmap_to_mmapd.
    rewrite (mmapd_mmapd U).
    fequal. now ext k [w a].
  Qed.

  (** *** Composition with <<mret>> *)
  (********************************************************************)
  Lemma mmap_comp_mret {A B}:
    forall (f: K -> A -> B) (a: A) (k: K),
      mmap (T k) f (mret T k a) = mret T k (f k a).
  Proof.
    intros. rewrite mmap_to_mmapd.
    now rewrite mmapd_comp_mret.
  Qed.

End Functor.
