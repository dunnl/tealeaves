From Tealeaves Require Import
  Categories.TypeFamilies
  Classes.EqDec_eq
  Classes.Monoid
  Classes.Functor
  Classes.Applicative
  Definitions.Product
  Functors.Writer.

Import TypeFamilies.Notations.
Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables A B C F G ϕ W T.

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
      mret : forall (A : Type) (k : K), A -> T k A.

    Class MBind :=
      mbinddt : forall (F : Type -> Type) `{Map F} `{Pure F} `{Mult F} {A B : Type},
        (forall (k : K), W * A -> F (T k B)) -> S A -> F (S B).

  End operations.

  (** ** Definition of Kleisli composition *)
  (******************************************************************************)
  Definition compose_dtm
             {W : Type}
             {T : K -> Type -> Type}
             `{mn_op : Monoid_op W}
             `{mn_unit : Monoid_unit W}
             `{Map F} `{Mult F} `{Pure F}
             `{Map G} `{Mult G} `{Pure G}
             `{forall k, MBind W T (T k)}
             {A B C : Type}
             (g : forall k, W * B -> G (T k C))
             (f : forall k, W * A -> F (T k B)) : forall k, W * A -> F (G (T k C)) :=
    fun (k : K) '(w, a) => map F (mbinddt W T (T k) G (g ◻ const (incr W w))) (f k (w, a)).

  Infix "⋆dtm" := compose_dtm (at level 40) : tealeaves_scope.

  Section compose_dtm_lemmas.

    Context
      (W : Type)
      (S : Type -> Type)
      (T : K -> Type -> Type)
      `{! MReturn T}
      `{! MBind W T S}
      `{! forall k, MBind W T (T k)}
      {mn_op : Monoid_op W}
      {mn_unit : Monoid_unit W}.

    Context
      `{Applicative G}
      `{Applicative F}
      `{! Monoid W}
      {A B C : Type}
      (g : forall k, W * B -> G (T k C))
      (f : forall k, W * A -> F (T k B)).

    Lemma compose_dtm_incr : forall (w : W),
        (fun k => (g ⋆dtm f) k ∘ incr W w) =
          ((fun k => g k ∘ incr W w) ⋆dtm (fun k => f k ∘ incr W w)).
    Proof.
      intros. ext k [w' a].
      cbn. do 2 fequal.
      ext j [w'' b].
      unfold compose. cbn. fequal.
      now rewrite monoid_assoc.
    Qed.

  End compose_dtm_lemmas.

  (** ** Decorated traversable premodule typeclass *)
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

    Class DTPreModule :=
      { dtp_monoid :> Monoid W;
        dtp_mbinddt_mret : forall A,
            mbinddt W T S (fun a => a) (mret T A ◻ const (extract (W ×) A)) = @id (S A);
        dtp_mbinddt_mbinddt : forall
            (F : Type -> Type)
            (G : Type -> Type)
            `{Applicative F}
            `{Applicative G}
            `(g : forall k, W * B -> G (T k C))
            `(f : forall k, W * A -> F (T k B)),
            map F (mbinddt W T S G g) ∘ mbinddt W T S F f =
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

  (** ** Decorated traversable monad *)
  (******************************************************************************)
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
            mbinddt W T (T k) F f ∘ mret T A k = (fun a => f k (Ƶ, a));
      }.

  End DTM.

End MultisortedDTM_typeclasses.

Arguments mret {ix} _%function_scope {MReturn} {A}%type_scope _ _.
Arguments mbinddt {ix} {W}%type_scope {T} (S)%function_scope {MBind} F%function_scope {H H0 H1} {A B}.

(** ** Derived operations on DTMs *)
(******************************************************************************)
Section derived_operations.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}.

  (** *** Definitions *)
  (******************************************************************************)
  Section definitions.

    Context
      {A B : Type}
      (F : Type -> Type)
      `{Map F} `{Mult F} `{Pure F}.

    Definition mbindd (f : forall k, W * A -> T k B) : S A -> S B :=
      mbinddt S (fun x => x) f.

    Definition mfmapdt (f : forall k, W * A -> F B) : S A -> F (S B) :=
      mbinddt S F (fun k => map F (mret T k) ∘ f k).

    Definition mbindt (f : forall k, A -> F (T k B)) : S A -> F (S B) :=
      mbinddt S F (f ◻ const (extract (W ×) A)).

    Definition mbind (f : forall k, A -> T k B) : S A -> S B :=
      mbindd (f ◻ const (extract (W ×) A)).

    Definition mfmapd (f : forall k, W * A -> B) : S A -> S B :=
      mbindd (fun k => mret T k ∘ f k).

    Definition mfmapt (f : forall k, A -> F B) : S A -> F (S B) :=
      mbindt (fun k => map F (mret T k) ∘ f k).

    Definition mfmap (f : forall k, A -> B) : S A -> S B :=
      mfmapd (f ◻ const (extract (W ×) A)).

  End definitions.

  Section special_cases.

    Context
      {A B : Type}
      (F : Type -> Type)
      `{Map F} `{Mult F} `{Pure F}.

    (** *** Rewriting rules for special cases of <<mbinddt>> *)
    (******************************************************************************)
    Lemma mbindt_to_mbinddt (f : forall k, A -> F (T k B)):
        mbindt F f = mbinddt S F (f ◻ const (extract (W ×) A)).
    Proof.
      reflexivity.
    Qed.

    Lemma mbindd_to_mbinddt (f : forall k, W * A -> T k B):
        mbindd f = mbinddt S (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapdt_to_mbinddt (f : K -> W * A -> F B):
        mfmapdt F f = mbinddt S F (fun k => map F (mret T k) ∘ f k).
    Proof.
      reflexivity.
    Qed.

    Lemma mbind_to_mbinddt (f : forall k, A -> T k B):
        mbind f = mbinddt S (fun A => A) (f ◻ const (extract (W ×) A)).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapd_to_mbinddt (f : K -> W * A -> B):
        mfmapd f = mbinddt S (fun A => A) (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapt_to_mbinddt (f : K -> A -> F B):
      mfmapt F f = mbinddt S F (fun k => map F (mret T k) ∘ f k ∘ extract (W ×) A).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmap_to_mbinddt (f : K -> A -> B):
      mfmap f = mbinddt S (fun A => A) (mret T ◻ f ◻ const (extract (W ×) A)).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mbindt>> *)
    (******************************************************************************)
    Lemma mbind_to_mbindt (f : forall k, A -> T k B):
      mbind f = mbindt (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapt_to_mbindt (f : K -> A -> F B):
      mfmapt F f = mbindt F (fun k => map F (mret T k) ∘ f k).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmap_to_mbindt (f : K -> A -> B):
      mfmap f = mbindt (fun A => A) (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<mbindd>> *)
    (******************************************************************************)
    Lemma mbind_to_mbindd (f : forall k, A -> T k B):
      mbind f = mbindd (f ◻ const (extract (W ×) A)).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapd_to_mbindd (f : W * A -k-> B):
      mfmapd f = mbindd (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmap_to_mbindd (f : A -k-> B):
      mfmap f = mbindd (mret T ◻ f ◻ const (extract (W ×) A)).
    Proof.
      reflexivity.
    Qed.

    (** *** Special cases of <<mfmapdt>> *)
    (******************************************************************************)
    Lemma mfmapd_to_mfmapdt (f : K -> W * A -> B):
      mfmapd f = mfmapdt (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mfmap_to_mfmapdt (f : K -> A -> B):
      mfmap f = mfmapdt (fun A => A) (f ◻ const (extract (W ×) A)).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapt_to_mfmapdt (f : K -> A -> F B):
      mfmapt F f = mfmapdt F (f ◻ const (extract (W ×) A)).
    Proof.
      reflexivity.
    Qed.

    (** *** Special cases of <<mfmapt>> *)
    (******************************************************************************)
    Lemma mfmap_to_mfmapt (f : K -> A -> B):
      mfmap f = mfmapt (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    (** *** Special cases of <<mfmapd>> *)
    (******************************************************************************)
    Lemma mfmap_to_mfmapd (f : K -> A -> B):
      mfmap f = mfmapd (f ◻ const (extract (W ×) A)).
    Proof.
      reflexivity.
    Qed.

    (** *** Special cases of <<mbind>> *)
    (******************************************************************************)
    Lemma mfmap_to_mbind (f : K -> A -> B):
      mfmap f = mbind (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

  End special_cases.

End derived_operations.

(** ** Composition between <<mbinddt>> and special cases operations *)
(** Fusion laws for compositions of the form <<mbinddt ∘ xxx>> or <<xxx ∘ mbinddt>> *)
(******************************************************************************)
Section derived_operations_composition.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    `{Applicative F}
    `{Applicative G}
    {A B C : Type}.

  (** *** <<mbinddt>> on the right *)
  (******************************************************************************)
  Lemma mbindd_mbinddt: forall
      (g : forall k, W * B -> T k C)
      (f : forall k, W * A -> F (T k B)),
      map F (mbindd S g) ∘ mbinddt S F f =
      mbinddt S F (fun k '(w, a) => map F (mbindd (T k) (g ◻ const (incr W w))) (f k (w, a))).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F (fun A => A)).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma mfmapdt_mbinddt: forall
      (g : K -> W * B -> G C)
      (f : forall k, W * A -> F (T k B)),
      map F (mfmapdt S G g) ∘ mbinddt S F f =
      mbinddt S (F ∘ G) (fun k '(w, a) => map F (mfmapdt (T k) G (g ◻ const (incr W w))) (f k (w, a))).
  Proof.
    intros. rewrite mfmapdt_to_mbinddt.
    now rewrite (dtp_mbinddt_mbinddt W S T F G).
  Qed.

  Lemma mbindt_mbinddt: forall
      (g : forall k, B -> G (T k C))
      (f : forall k, W * A -> F (T k B)),
      map F (mbindt S G g) ∘ mbinddt S F f =
      mbinddt S (F ∘ G) (fun k => map F (mbindt (T k) G g) ∘ f k).
  Proof.
    intros. rewrite mbindt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F G).
    fequal. ext k [w a]. unfold compose; cbn.
    fequal. rewrite mbindt_to_mbinddt.
    fequal. now ext j [w2 b].
  Qed.

  Lemma mbind_mbinddt: forall
      (g : forall k, B -> T k C)
      (f : forall k, W * A -> F (T k B)),
      map F (mbind S g) ∘ mbinddt S F f =
      mbinddt S F (fun k => map F (mbind (T k) g) ∘ f k).
  Proof.
    intros. rewrite mbind_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F (fun A => A)).
    fequal.
    - now rewrite Mult_compose_identity1.
    - unfold compose, compose_dtm. ext k [w a].
      fequal. rewrite mbind_to_mbinddt. fequal.
      now ext j [w2 b].
  Qed.

  Lemma mfmapd_mbinddt: forall
      (g : K -> W * B -> C)
      (f : forall k, W * A -> F (T k B)),
      map F (mfmapd S g) ∘ mbinddt S F f =
      mbinddt S F (fun k '(w, a) => map F (mfmapd (T k) (g ◻ const (incr W w))) (f k (w, a))).
  Proof.
    intros. rewrite mfmapd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F (fun A => A)).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma mfmapt_mbinddt: forall
      (g : K -> B -> G C)
      (f : forall k, W * A -> F (T k B)),
      map F (mfmapt S G g) ∘ mbinddt S F f =
      mbinddt S (F ∘ G) (fun k => map F (mfmapt (T k) G g) ∘ f k).
  Proof.
    intros. rewrite mfmapt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F G).
    fequal. ext k [w a]. unfold compose; cbn.
    fequal. rewrite mfmapt_to_mbinddt.
    fequal. now ext j [w2 b].
  Qed.

  Lemma mfmap_mbinddt: forall
      (g : K -> B -> C)
      (f : forall k, W * A -> F (T k B)),
      map F (mfmap S g) ∘ mbinddt S F f =
      mbinddt S F (fun k => map F (mfmap (T k) g) ∘ f k).
  Proof.
    intros. unfold mfmap. rewrite mfmapd_mbinddt.
    fequal. ext k [w a]. unfold compose; cbn.
    fequal. fequal. now ext j [w2 b].
  Qed.

  (** *** <<mbinddt>> on the left *)
  (******************************************************************************)
  Lemma mbinddt_mbindd: forall
      (g : forall k, W * B -> G (T k C))
      (f : forall k, W * A -> T k B),
      mbinddt S G g ∘ mbindd S f =
      mbinddt S G (fun k '(w, a) => mbinddt (T k) G (g ◻ const (incr W w)) (f k (w, a))).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    change (mbinddt S G g) with (map (fun A => A) (mbinddt S G g)).
    rewrite (dtp_mbinddt_mbinddt W S T (fun A => A) G).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma mbinddt_mfmapdt: forall
      (g : forall k, W * B -> G (T k C))
      (f : K -> W * A -> F B),
      map F (mbinddt S G g) ∘ mfmapdt S F f =
      mbinddt S (F ∘ G) (fun k '(w, a) => map F (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros. rewrite mfmapdt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F G).
    fequal. ext k [w a]. unfold compose; cbn.
    compose near (f k (w, a)) on left.
    rewrite (fun_map_map F).
    fequal. ext b. unfold compose; cbn.
    compose near b on left.
    rewrite (dtm_mbinddt_comp_mret W T k G).
    cbn. now simpl_monoid.
  Qed.

  Lemma mbinddt_mbindt: forall
      (g : forall k, W * B -> G (T k C))
      (f : forall k, A -> F (T k B)),
      map F (mbinddt S G g) ∘ mbindt S F f =
      mbinddt S (F ∘ G) (fun k '(w, a) => map F (mbinddt (T k) G (g ◻ const (incr W w))) (f k a)).
  Proof.
    intros. rewrite mbindt_to_mbinddt.
    now rewrite (dtp_mbinddt_mbinddt W S T F G).
  Qed.

  Lemma mbinddt_mbind: forall
      (g : forall k, W * B -> G (T k C))
      (f : forall k, A -> T k B),
      mbinddt S G g ∘ mbind S f =
      mbinddt S G (fun k '(w, a) => mbinddt (T k) G (g ◻ const (incr W w)) (f k a)).
  Proof.
    intros. rewrite mbind_to_mbinddt.
    change (mbinddt S G g) with (map (fun A => A) (mbinddt S G g)).
    rewrite (dtp_mbinddt_mbinddt W S T (fun A => A) G).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma mbinddt_mfmapd: forall
      (g : forall k, W * B -> G (T k C))
      (f : forall k, W * A -> B),
      mbinddt S G g ∘ mfmapd S f =
      mbinddt S G (fun k '(w, a) => g k (w, f k (w, a))).
  Proof.
    intros. rewrite mfmapd_to_mbinddt.
    change (mbinddt S G g) with (map (fun A => A) (mbinddt S G g)).
    rewrite (dtp_mbinddt_mbinddt W S T (fun A => A) G).
    fequal. now rewrite Mult_compose_identity2.
    ext j [w2 b]. unfold compose; cbn.
    unfold_ops @Map_I. compose near (f j (w2, b)).
    rewrite (dtm_mbinddt_comp_mret W T j G).
    unfold compose; cbn.
    now simpl_monoid.
  Qed.

  Lemma mbinddt_mfmapt: forall
      (g : forall k, W * B -> G (T k C))
      (f : K -> A -> F B),
      map F (mbinddt S G g) ∘ mfmapt S F f =
      mbinddt S (F ∘ G) (fun k '(w, a) => map F (fun b => g k (w, b)) (f k a)).
  Proof.
    intros. unfold mfmapt. rewrite mbinddt_mbindt.
    fequal. ext k [w a]. unfold compose. compose near (f k a) on left.
    rewrite (fun_map_map F). fequal.
    rewrite (dtm_mbinddt_comp_mret W T k G).
    ext b. cbn. now simpl_monoid.
  Qed.

  Lemma mbinddt_mfmap: forall
      (g : forall k, W * B -> G (T k C))
      (f : K -> A -> B),
      mbinddt S G g ∘ mfmap S f =
      mbinddt S G (fun k '(w, a) => g k (w, f k a)).
  Proof.
    intros. unfold mfmap. now rewrite mbinddt_mfmapd.
  Qed.

End derived_operations_composition.

(** ** Purity law for <<mbinddt>> *)
(******************************************************************************)
Section DTM_laws.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Purity *)
  (******************************************************************************)
  Lemma mbinddt_pure: forall (A : Type) `{Applicative F},
      mbinddt S F (fun k => pure F ∘ mret T k ∘ extract (W ×) A) = pure F (A := S A).
  Proof.
    intros. replace (fun (k : K) => pure F ∘ mret T k ∘ extract (W ×) A)
              with (fun (k : K) => pure F ∘ (mret T k ∘ extract (W ×) A)).
    2:{ ext k [w a]. easy. }
    rewrite <- (dtp_mbinddt_morphism W S T (fun x => x) F (ϕ := @pure F _)).
    now rewrite (dtp_mbinddt_mret W S T).
  Qed.

End DTM_laws.

(** * Derived structures on DTMs *)
(******************************************************************************)

(** ** Some mixed structure composition laws *)
(** Composition laws involving one of <<mbindd>>/<<mfmapdt>>/<<mbindt>>
    and another operation that is not a special cases. *)
(******************************************************************************)
Section mixed_composition_laws.

  Context
    (S : Type -> Type)
    (F G : Type -> Type)
    `{Applicative F}
    `{Applicative G}
    `{DTPreModule W S T}
    `{! DTM W T} {A B C : Type}.

  (** *** <<mbindd>> *)
  (** Operations with traversals are not special cases of <<mbindd>>. *)
  (******************************************************************************)
  Lemma mbindd_mfmapdt: forall
      (g : forall k, W * B -> T k C)
      (f : forall k, W * A -> F B),
      map F (mbindd S g) ∘ mfmapdt S F f =
      mbinddt S F (fun (k : K) '(w, a) => map F (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros. rewrite mfmapdt_to_mbinddt.
    rewrite mbindd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F (fun x => x)).
    fequal.
    - now rewrite Mult_compose_identity1.
    - ext k [w a]. unfold compose; cbn.
      compose near (f k (w, a)) on left.
      rewrite (fun_map_map F). fequal.
      rewrite (dtm_mbinddt_comp_mret W T k (fun A =>A)).
      ext b. unfold compose; cbn. now simpl_monoid.
  Qed.

  Lemma mbindd_mbindt: forall
      (g : forall k, W * B -> T k C)
      (f : forall k, A -> F (T k B)),
      map F (mbindd S g) ∘ mbindt S F f =
      mbinddt S F (fun (k : K) '(w, a) => map F (mbindd (T k) (g ◻ const (incr W w))) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  Lemma mbindd_mfmapt: forall
      (g : forall k, W * B -> T k C)
      (f : forall k, A -> F B),
      map F (mbindd S g) ∘ mfmapt S F f =
      mbinddt S F (fun (k : K) '(w, a) => map F (fun b => g k (w, b)) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  (* TODO Also need to put <<mfmapt_mbindd>> somewhere. *)

  (** *** <<mfmapdt>> *)
  (** Operations with joins are not special cases of <<mfmapdt>>. *)
  (******************************************************************************)
  Lemma mfmapdt_mbindd: forall
      (g : forall k, W * B -> G C)
      (f : forall k, W * A -> T k B),
      mfmapdt S G g ∘ mbindd S f =
      mbinddt S G (fun (k : K) '(w, a) => mfmapdt (T k) G (g ◻ const (incr W w)) (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  Lemma mfmapdt_mbindt: forall
      (g : forall k, W * B -> G C)
      (f : forall k, A -> F (T k B)),
      map F (mfmapdt S G g) ∘ mbindt S F f =
      mbinddt S (F ∘ G) (fun (k : K) '(w, a) => map F (mfmapdt (T k) G (g ◻ const (incr W w))) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  Lemma mfmapdt_mbind: forall
      (g : K -> W * B -> G C) (f : forall k, A -> T k B),
      mfmapdt S G g ∘ mbind S f = mbinddt S G (fun k '(w, a) => mfmapdt (T k) G (g ◻ const (incr W w)) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  (* TODO Also need to put <<mbind_mfmapdt>> somewhere. *)

  (** *** <<mbindt>> *)
  (** Operations with decorations are not special cases of <<mbindt>>. *)
  (******************************************************************************)
  Lemma mbindt_mbindd: forall
      (g : forall k, B -> G (T k C))
      (f : forall k, W * A -> T k B),
      mbindt S G g ∘ mbindd S f =
      mbinddt S G (fun (k : K) '(w, a) => mbindt (T k) G g (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  Lemma mbindt_mfmapdt: forall
      (g : forall k, B -> G (T k C))
      (f : forall k, W * A -> F B),
      map F (mbindt S G g) ∘ mfmapdt S F f =
      mbinddt S (F ∘ G) (fun (k : K) '(w, a) => map F (g k) (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  (* TODO <<mbindt_mfmapd>> *)

  (* TODO Also need to put <<mfmapd_mbindt>> somewhere. *)

End mixed_composition_laws.

(** ** Decorated monads (<<mbindd>>) *)
(******************************************************************************)
Definition compose_dm
           `{ix : Index}
           {W : Type}
           {T : K -> Type -> Type}
           `{mn_op : Monoid_op W}
           `{mn_unit : Monoid_unit W}
           `{forall k, MBind W T (T k)}
           {A B C : Type}
           (g : forall k, W * B -> T k C)
           (f : forall k, W * A -> T k B) : forall k, W * A -> T k C :=
  fun k '(w, a) => mbindd (T k) (g ◻ const (incr W w)) (f k (w, a)).

Infix "⋆dm" := compose_dm (at level 40).

Section DecoratedMonad.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T} {A B C : Type}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem mbindd_id:
    mbindd S (mret T ◻ const (extract (W ×) A)) = @id (S A).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    now rewrite <- (dtp_mbinddt_mret W S T).
  Qed.

  Theorem mbindd_mbindd: forall
      (g : W * B ~k~> T C)
      (f : W * A ~k~> T B),
      mbindd S g ∘ mbindd S f =
      mbindd S (fun (k : K) '(w, a) => mbindd (T k) (g ◻ const (incr W w)) (f k (w, a))).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    change_left (map (fun x => x) (mbinddt S (fun x : Type => x) g) ∘ (mbinddt S (fun x : Type => x) f)).
    rewrite (dtp_mbinddt_mbinddt W S T (fun x => x) (fun x => x)).
    ext t.
    change (compose_dtm g f) with
        (fun (k : K) '(w, a) => mbinddt (T k) (fun x : Type => x) (g ◻ const (incr W w)) (f k (w, a))).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  (** *** Right unit law for monads *)
  (******************************************************************************)
  Theorem mbindd_comp_mret: forall
      (k : K) (f : forall k, W * A -> T k B),
      mbindd (T k) f ∘ mret T k = f k ∘ ret (W ×) A.
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    now rewrite (dtm_mbinddt_comp_mret W T k (fun A => A)).
  Qed.

  (** *** Composition with special cases on the right *)
  (** Composition with operations <<mbind>>/<<mfmapd>>/<<mfmap>> *)
  (******************************************************************************)
  Lemma mbindd_mbind: forall
      (g : forall k, W * B -> T k C)
      (f : A ~k~> T B),
      mbindd S g ∘ mbind S f =
      mbindd S (fun (k : K) '(w, a) => mbindd (T k) (g ◻ const (incr W w)) (f k a)).
  Proof.
    intros. rewrite mbind_to_mbindd.
    now rewrite mbindd_mbindd.
  Qed.

  Lemma mbindd_mfmapd: forall
      (g : forall k, W * B -> T k C)
      (f : forall k, W * A -> B),
      mbindd S g ∘ mfmapd S f =
      mbindd S (fun (k : K) '(w, a) => g k (w, f k (w, a))).
  Proof.
    intros. rewrite mfmapd_to_mbindd. rewrite (mbindd_mbindd).
    fequal. ext k [w a]. unfold compose; cbn.
    compose near (f k (w, a)).
    rewrite mbindd_to_mbinddt.
    rewrite (dtm_mbinddt_comp_mret W T k (fun A => A)).
    unfold compose; cbn. now simpl_monoid.
  Qed.

  Lemma mbindd_mfmap: forall
      (g : forall k, W * B -> T k C)
      (f : forall k, A -> B),
      mbindd S g ∘ mfmap S f =
      mbindd S (fun (k : K) '(w, a) => g k (w, f k a)).
  Proof.
    intros. unfold mfmap.
    now rewrite (mbindd_mfmapd).
  Qed.

  (** *** Composition with special cases on the left *)
  (******************************************************************************)
  Lemma mbind_mbindd: forall
      (g : forall k, B -> T k C)
      (f : forall k, W * A -> T k B),
      mbind S g ∘ mbindd S f =
      mbindd S (fun (k : K) => mbind (T k) g ∘ f k).
  Proof.
    intros. rewrite mbind_to_mbindd.
    rewrite (mbindd_mbindd). fequal.
    ext k [w a]. unfold compose; cbn.
    unfold mbind. fequal. now ext j [w2 b].
  Qed.

  Lemma mfmapd_mbindd: forall
      (g : forall k, W * B -> C)
      (f : forall k, W * A -> T k B),
      mfmapd S g ∘ mbindd S f =
      mbindd S (fun (k : K) '(w, a) => mfmapd (T k) (g ◻ const (incr W w)) (f k (w, a))).
  Proof.
    intros. rewrite mfmapd_to_mbindd.
    now rewrite (mbindd_mbindd).
  Qed.

  Lemma mfmap_mbindd: forall
      (g : forall k, B -> T k C)
      (f : forall k, W * A -> T k B),
      mbind S g ∘ mbindd S f =
      mbindd S (fun (k : K) => mbind (T k) g ∘ f k).
  Proof.
    intros. rewrite mbind_to_mbindd.
    rewrite (mbindd_mbindd). fequal.
    ext k [w a]. unfold compose; cbn.
    rewrite mbind_to_mbindd. fequal.
    now ext j [w2 b].
  Qed.

End DecoratedMonad.

(** ** Decorated traversable functors (<<mfmapdt>>) *)
(******************************************************************************)
Section DecoratedTraversable.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T} {A B C : Type}
    `{Applicative F} `{Applicative G}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem mfmapdt_id:
    mfmapdt S (fun x => x) (const (extract (W ×) A)) = @id (S A).
  Proof.
    intros. unfold mfmapdt. apply (dtp_mbinddt_mret W S T).
  Qed.

  Theorem mfmapdt_mfmapdt: forall
    (g : forall k, W * B -> G C) (f : forall k, W * A -> F B),
    map F (mfmapdt S G g) ∘ mfmapdt S F f =
    mfmapdt S (F ∘ G) (fun (k : K) '(w, a) => map F (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros. unfold mfmapdt. rewrite (dtp_mbinddt_mbinddt W S T F G).
    unfold compose_dtm. fequal. ext k [w a].
    unfold_ops @Map_compose.  unfold compose.
    compose near (f k (w, a)).
    do 2 rewrite (fun_map_map F). rewrite (dtm_mbinddt_comp_mret W T k G).
    fequal. ext b. cbn. now simpl_monoid.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mfmapdt_comp_mret: forall
      (k : K) (f : forall k, W * A -> F B),
      mfmapdt (T k) F f ∘ mret T k = map F (mret T k) ∘ f k ∘ pair Ƶ.
  Proof.
    intros. unfold mfmapdt.
    now rewrite (dtm_mbinddt_comp_mret W T k F).
  Qed.

  (** *** Purity *)
  (******************************************************************************)
  Lemma mfmapdt_pure:
      mfmapdt S F (fun k => pure F ∘ extract (W ×) A) = pure F (A := S A).
  Proof.
    intros. unfold mfmapdt.
    replace (fun k : K => map F (mret T k) ∘ (pure F ∘ extract (prod W) A))
      with (fun (k : K) => (pure F ∘ (mret T k ∘ extract (W ×) A))).
    rewrite <- (dtp_mbinddt_morphism W S T (fun x => x) F (ϕ := @pure F _)).
    now rewrite (dtp_mbinddt_mret W S T).
    ext k [w a]. unfold compose; cbn.
    now rewrite (app_pure_natural F).
  Qed.

  (** *** Composition with special cases  on the right *)
  (******************************************************************************)
  Lemma mfmapdt_mfmapt: forall
      (g : K -> W * B -> G C) (f : K -> A -> F B),
      map F (mfmapdt S G g) ∘ mfmapt S F f =
      mfmapdt S (F ∘ G) (fun (k : K) '(w, a) => map F (fun b => g k (w, b)) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  Lemma mfmapdt_mfmapd: forall
      (g : K -> W * B -> G C) (f : K -> W * A -> B),
      mfmapdt S G g ∘ mfmapd S f = mfmapdt S G (fun k '(w, a) => g k (w, f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  (* TODO <<mfmapdt_mfmap>> *)

  (** *** Composition with other operations on the left *)
  (******************************************************************************)
  Lemma mfmapd_mfmapdt: forall
      (g : K -> W * B -> C) (f : K -> W * A -> F B),
      map F (mfmapd S g) ∘ mfmapdt S F f =
      mfmapdt S F (fun k '(w, a) => map F (fun (b : B) => (g k (w, b))) (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  Lemma mfmapt_mfmapdt: forall
      (g : K -> B -> C) (f : K -> W * A -> F B),
      map F (mfmap S g) ∘ mfmapdt S F f = mfmapdt S F (fun k => map F (g k) ∘ f k).
  Proof.
    (* TODO *)
  Abort.

  (* TODO <<mfmap_mfmapdt>> *)

End DecoratedTraversable.

(** ** Traversable monads (<<mbindt>>) *)
(******************************************************************************)
Section TraversableMonad.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    {A B C : Type}
    (F G : Type -> Type)
    `{Applicative F} `{Applicative G}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem mbindt_id :
    mbindt S (fun x => x) (mret T) = @id (S A).
  Proof.
    intros. unfold mbindt.
    now rewrite (dtp_mbinddt_mret W S T).
  Qed.

  Theorem mbindt_mbindt :
    forall (g : forall k, B -> G (T k C))
      (f : forall k, A -> F (T k B)),
      map F (mbindt S G g) ∘ mbindt S F f =
      mbindt S (F ∘ G) (fun (k : K) (a : A) => map F (mbindt (T k) G g) (f k a)).
  Proof.
    intros. unfold mbindt. rewrite (dtp_mbinddt_mbinddt W S T F G).
    fequal. ext k [w a]. unfold compose; cbn.
    repeat fequal. ext k2 [w2 b]. easy.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mbindt_comp_mret :
    forall (k : K) (f : forall k, A -> F (T k B)),
      mbindt (T k) F f ∘ mret T k = f k.
  Proof.
    intros. unfold mbindt.
    now rewrite (dtm_mbinddt_comp_mret W T k F).
  Qed.

  (** *** Purity *)
  (******************************************************************************)
  (* TODO *)

  (** *** Composition with special cases on the right *)
  (******************************************************************************)
  (* TODO *)

  (** *** Composition with special cases on the left *)
  (******************************************************************************)
  (* TODO *)

End TraversableMonad.

(** ** Some more mixed structure composition laws *)
(** Composition laws between one of <<mbind>>/<<mfmapd>>/<<mfmapt>>
    and another operation, neither of which is a special case of the other. *)
(******************************************************************************)
Section mixed_composition_laws2.

  Context
    (S : Type -> Type)
    (F G : Type -> Type)
    `{Applicative F}
    `{Applicative G}
    `{DTPreModule W S T}
    `{! DTM W T} {A B C : Type}.

  (** *** <<mbind>> on the left *)
  (******************************************************************************)
  Lemma mbind_mfmapd :
    forall (g : forall k, B -> T k C)
      (f : K -> W * A -> B),
      mbind S g ∘ mfmapd S f =
      mbindd S (g ◻ f).
  Proof.
    intros. rewrite mfmapd_to_mbindd. rewrite mbind_to_mbindd.
    rewrite (mbindd_mbindd S). fequal.
    ext k [w a]. unfold compose; cbn.
    compose near (f k (w, a)) on left.
    now rewrite (mbindd_comp_mret (T := T)).
  Qed.

  Lemma mbind_mfmapt :
    forall (g : forall k, B -> T k C)
      (f : K -> A -> F B),
      map F (mbind S g) ∘ mfmapt S F f =
      mbindt S F (fun k => map F (g k) ∘ f k).
  Proof.
    intros. rewrite (mfmapt_to_mbindt S F).
    rewrite mbind_to_mbindt.
    rewrite (mbindt_mbindt S F (fun A => A)).
    fequal.
    - now rewrite Mult_compose_identity1.
    - ext k a. unfold compose. compose near (f k a) on left.
      rewrite (fun_map_map F). fequal.
      change (mbindt (T k) (fun A0 : Type => A0) g)
        with (mbind (T k) g).
      rewrite mbind_to_mbindd.
      now rewrite mbindd_comp_mret.
  Qed.

  (** *** <<mfmapd>> on the left *)
  (******************************************************************************)
  Lemma mfmapd_mbind :
    forall (g : K -> W * B -> C)
      (f : forall k, A -> T k B),
      mfmapd S g ∘ mbind S f =
      mbindd S (fun k '(w, a) => mfmapd (T k) (g ◻ const (incr W w)) (f k a)).
  Proof.
    intros. rewrite mfmapd_to_mbindd. rewrite mbind_to_mbindd.
    now rewrite (mbindd_mbindd S).
  Qed.

  Lemma mfmapd_mfmapt :
    forall (g : K -> W * B -> C)
      (f : forall k, A -> F B),
      map F (mfmapd S g) ∘ mfmapt S F f =
      mfmapdt S F (fun k '(w, a) => map F (fun b => g k (w, b)) (f k a)).
  Proof.
    intros. rewrite mfmapd_to_mfmapdt. rewrite mfmapt_to_mfmapdt.
    rewrite (mfmapdt_mfmapdt S (G := fun A => A)). fequal.
    now rewrite Mult_compose_identity1.
  Qed.

  (** *** <<mfmapt>> on the left *)
  (******************************************************************************)
  Lemma mfmapt_mbind :
    forall (g : K -> B -> G C)
      (f : forall k, A -> T k B),
      mfmapt S G g ∘ mbind S f =
      mbindt S G (fun k => mfmapt (T k) G g ∘ f k).
  Proof.
    intros. rewrite mfmapt_to_mbindt. rewrite mbind_to_mbindt.
    change (mbindt S G (fun k : K => map G (mret T k) ∘ g k))
      with (map (fun A => A) (mbindt S G (fun k : K => map G (mret T k) ∘ g k))).
    rewrite (mbindt_mbindt S (fun A => A) G).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma mfmapt_mfmapd :
    forall (g : K -> B -> G C)
      (f : forall k, A -> T k B),
      mfmapt S G g ∘ mbind S f =
      mbindt S G (fun k => mfmapt (T k) G g ∘ f k).
  Proof.
    intros. rewrite mfmapt_to_mbindt.
    rewrite mbind_to_mbindt.
    change (mbindt S G (fun k : K => map G (mret T k) ∘ g k))
      with (map (fun A => A) (mbindt S G (fun k : K => map G (mret T k) ∘ g k))).
    rewrite (mbindt_mbindt S (fun A => A) G).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

End mixed_composition_laws2.

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
    intros. rewrite mbind_to_mbindd.
    compose near a on left. now rewrite mbindd_comp_mret.
  Qed.

  (* TODO <<mbind_mfmap>> *)

  (* TODO <<mfmap_mbind>> *)

End Monad.

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
      mfmapd S (const (extract (W ×) A)) = @id (S A).
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
        (map (fun A => A) (mfmapdt S (fun A => A) g)).
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
    intros. rewrite mfmapd_to_mfmapdt. compose near a on left.
    now rewrite (mfmapdt_comp_mret (F := fun A => A)).
  Qed.

  (* TODO <<mfmapd_mfmap>> *)

  (* TODO <<mfmap_mfmapd>> *)

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
      map F (mfmapt S G g) ∘ mfmapt S F f =
      mfmapt S (F ∘ G) (fun (k : K) (a : A) => map F (g k) (f k a)).
  Proof.
    intros. rewrite (mfmapt_to_mfmapdt S G).
    rewrite (mfmapt_to_mfmapdt S F).
    rewrite (mfmapt_to_mfmapdt S (F ∘ G)).
    rewrite (mfmapdt_mfmapdt S).
    fequal. now ext k [w a].
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mfmapt_comp_mret {A B} :
    forall  `{Applicative F} (k : K) (f : K -> A -> F B) (a : A),
      mfmapt (T k) F f (mret T k a) = map F (mret T k) (f k a).
  Proof.
    intros. rewrite (mfmapt_to_mfmapdt (T k)). compose near a on left.
    now rewrite mfmapdt_comp_mret.
  Qed.

  (* TODO <<mfmapt_mfmap>> *)

  (* TODO <<mfmap_mfmapt>> *)

End TraversableFunctor.

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
    intros. do 3 rewrite mfmap_to_mfmapd.
    rewrite (mfmapd_mfmapd S).
    fequal. now ext k [w a].
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mfmap_comp_mret {A B} :
    forall (f : K -> A -> B) (a : A) (k : K),
      mfmap (T k) f (mret T k a) = mret T k (f k a).
  Proof.
    intros. rewrite mfmap_to_mfmapd.
    now rewrite mfmapd_comp_mret.
  Qed.

End Functor.

(** * Targeted operations *)
(** In this section we ignore operations involving traversals simply
    because they are not necessary for System F. *)
(******************************************************************************)

(** ** Targeted substitution-building combinators: [btg] and [btgd] *)
(******************************************************************************)

(* TODO : Define a version that works for applicative effects. *)
(*
#[program] Definition btga `{ix : Index} `{Map F} `{Pure F} `{Mult F}
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
      k <> j -> tgtd T j f k = extract (W ×) A.
  Proof.
    introv. unfold tgtd. intro hyp. ext [w a].
    compare values k and j.
  Qed.

  Lemma tgtd_id (j : K) :
    tgtd (A := A) T j (extract (W ×) A) = const (extract (W ×) A).
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
      k <> j -> btgd T j f k = mret T k ∘ extract (W ×) A.
  Proof.
    introv. unfold btgd. intro hyp. ext [w a].
    compare values k and j.
  Qed.

  Lemma btgd_id (j : K) :
    btgd (A := A) T j (mret T j ∘ extract (W ×) A) = mret T ◻ const (extract (W ×) A).
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
#[export] Hint Rewrite @tgt_eq @tgtd_eq @tgt_id @tgtd_id : tea_tgt.
#[export] Hint Rewrite @btgd_eq @btg_eq @btg_id @btgd_id : tea_tgt.
#[export] Hint Rewrite @btgd_neq @btg_neq using auto : tea_tgt.

#[export] Hint Rewrite @tgt_eq @tgtd_eq @tgt_id @tgtd_id : tea_tgt_eq.
#[export] Hint Rewrite @btgd_eq @btg_eq @btg_id @btgd_id : tea_tgt_eq.
#[export] Hint Rewrite @tgtd_neq @tgt_neq using auto : tea_tgt_neq.
#[export] Hint Rewrite @btgd_neq @btg_neq using auto : tea_tgt_neq.

(** ** Derived targeted DTM operations *)
(******************************************************************************)
Section DTM_targeted.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    (j : K).

  (** *** Definitions *)
  (* For now we ignore traversals because we don't need them for System F. *)
  (******************************************************************************)
  Definition kbindd {A} `(f : W * A -> T j A) : S A -> S A
    := mbindd S (btgd T j f).

  Definition kbind `(f : A -> T j A) : S A -> S A
    := mbind S (btg T j f).

  Definition kfmapd `(f : W * A -> A) : S A -> S A :=
    mfmapd S (tgtd T j f).

  Definition kfmap `(f : A -> A) : S A -> S A :=
    mfmap S (tgt T j f).

  Section special_cases.

    Context
      {A : Type}.

    (** *** Rewriting rules for special cases of <<kbindd>> *)
    (******************************************************************************)
    Lemma kbind_to_kbindd (f : A -> T j A) :
      kbind f = kbindd (f ∘ extract (W ×) A).
    Proof.
      unfold kbind, kbindd. rewrite mbind_to_mbindd.
      fequal. ext k [w a]. unfold compose; cbn.
      compare values k and j.
      - autorewrite  with tea_tgt_eq. easy.
      - autorewrite  with tea_tgt_neq. easy.
    Qed.

    Lemma kfmapd_to_kbindd (f : W * A -> A) :
      kfmapd f = kbindd (mret T j ∘ f).
    Proof.
      unfold kfmapd, kbindd. rewrite mfmapd_to_mbindd.
      fequal. ext k [w a]. unfold compose. cbn. compare values k and j.
    Qed.

    Lemma kfmap_to_kbindd (f : A -> A) :
      kfmap f = kbindd (mret T j ∘ f ∘ extract (W ×) A).
    Proof.
      unfold kfmap, kbindd. rewrite mfmap_to_mbindd.
      fequal. ext k [w a]. unfold compose. cbn.
      compare values k and j. cbn.
      now autorewrite with tea_tgt_eq.
      now autorewrite with tea_tgt_neq.
    Qed.

    (** *** Rewriting rules for special cases of <<kfmapd>> *)
    (******************************************************************************)
    Lemma kfmap_to_kfmapd (f : A -> A) :
      kfmap f = kfmapd (f ∘ extract (W ×) A).
    Proof.
      unfold kfmap, kbind.
      unfold kfmapd. rewrite mfmap_to_mfmapd.
      fequal. ext k. compare values j and k.
      now autorewrite with tea_tgt_eq.
      now autorewrite with tea_tgt_neq.
    Qed.

    (** *** Rewriting rules for special cases of <<kbind>> *)
    (******************************************************************************)
    Lemma kfmap_to_kbind (f : A -> A) :
      kfmap f = kbind (mret T j ∘ f).
    Proof.
      unfold kfmap, kbind.
      rewrite mfmap_to_mbind.
      fequal. ext k. compare values j and k.
      now autorewrite with tea_tgt_eq.
      now autorewrite with tea_tgt_neq.
    Qed.

  End special_cases.

End DTM_targeted.

(** ** Decorated monad (<<kbindd>>) *)
(******************************************************************************)

Definition compose_kdm
           `{ix : Index}
           {W : Type}
           {T : K -> Type -> Type}
           `{mn_op : Monoid_op W}
           `{mn_unit : Monoid_unit W}
           `{forall k, MBind W T (T k)}
           `{! MReturn T}
           {j : K}
           {A : Type}
           (g : W * A -> T j A)
           (f : W * A -> T j A) : W * A -> T j A :=
  fun '(w, a) => kbindd (T j) j (g ∘ incr W w) (f (w, a)).

Infix "⋆kdm" := compose_kdm (at level 40).

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
    kbindd S j (mret T j ∘ (extract (W ×) A)) = @id (S A).
  Proof.
    intros. unfold kbindd. rewrite <- (mbindd_id S).
    fequal. ext k [w a]. cbn. compare values k and j.
  Qed.

  Theorem kbindd_kbindd_eq : forall (g : W * A -> T j A) (f : W * A -> T j A),
      kbindd S j g ∘ kbindd S j f =
      kbindd S j (g ⋆kdm f).
  Proof.
    intros. unfold kbindd. rewrite (mbindd_mbindd S).
    fequal. ext k [w a]. cbn. compare values k and j.
    - cbn. unfold kbindd. fequal. ext k [w' a'].
      compare values k and j.
    - compose near a on left. rewrite mbindd_comp_mret.
      cbn. compare values k and j.
  Qed.

  Theorem kbindd_kbindd_neq :
    forall {i : K} (Hneq : j <> i)
      (g : W * A -> T i A) (f : W * A -> T j A),
      kbindd S i g ∘ kbindd S j f =
      mbindd S (btgd T i g ⋆dm btgd T j f).
  Proof.
    intros. unfold kbindd. now rewrite (mbindd_mbindd S).
  Qed.

  (** *** Right unit law for monads *)
  (******************************************************************************)
  Theorem kbindd_comp_mret_eq : forall (f : W * A -> T j A) (a : A),
      kbindd (T j) j f (mret T j a) = f (Ƶ, a).
  Proof.
    intros. unfold kbindd. compose near a on left.
    rewrite (mbindd_comp_mret).
    now autorewrite with tea_tgt_eq.
  Qed.

  Theorem kbindd_comp_mret_neq :
    forall (i : K) (Hneq : j <> i)
      (f : W * A -> T j A) (a : A),
      kbindd (T i) j f (mret T i a) = mret T i a.
  Proof.
    intros. unfold kbindd. compose near a on left.
    rewrite (mbindd_comp_mret).
    now autorewrite with tea_tgt_neq.
  Qed.

  (** *** Composition with special cases *)
  (******************************************************************************)
  Lemma kfmapd_kbindd : forall
      (g : W * A -> A) (f : W * A -> T j A),
      kfmapd S j g ∘ kbindd S j f = kbindd S j (fun '(w, a) => kfmapd (T j) j (g ∘ incr W w) (f (w, a))).
  Proof.
    intros. rewrite kfmapd_to_kbindd.
    rewrite kbindd_kbindd_eq. fequal.
    unfold compose_kdm. ext [w a].
    now rewrite kfmapd_to_kbindd.
  Qed.

  Lemma kbind_kbindd : forall
      (g : A -> T j A) (f : W * A -> T j A),
      kbind S j g ∘ kbindd S j f = kbindd S j (kbind (T j) j g ∘ f).
  Proof.
    intros. rewrite kbind_to_kbindd. rewrite kbindd_kbindd_eq.
    fequal. unfold compose_kdm. ext [w a].
    reassociate ->. rewrite extract_incr. now rewrite kbind_to_kbindd.
  Qed.

  Lemma kfmap_kbindd : forall
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
      compose near a on left.
      rewrite (mbindd_comp_mret). rewrite tgt_neq; auto.
  Qed.

  Lemma kbindd_kfmapd : forall
      (g : W * A -> T j A) (f : W * A -> A),
      kbindd S j g ∘ kfmapd S j f = kbindd S j (fun '(w, a) => g (w, f (w, a))).
  Proof.
    intros. rewrite kfmapd_to_kbindd.
    rewrite kbindd_kbindd_eq. fequal.
    ext (w, a). unfold compose; cbn.
    rewrite kbindd_comp_mret_eq. unfold compose; cbn.
    now simpl_monoid.
  Qed.

  Lemma kbindd_kbind : forall
      (g : W * A -> T j A) (f : A -> T j A),
      kbindd S j g ∘ kbind S j f = kbindd S j (fun '(w, a) => kbindd (T j) j (g ∘ incr W w) (f a)).
  Proof.
    intros. rewrite kbind_to_kbindd. now rewrite kbindd_kbindd_eq.
  Qed.

  (* TODO <<kbindd_kfmap>> *)

End DecoratedMonad.

(** ** Mixed structure composition laws *)
(** Composition laws involving <<kbind>> and <<kfmapd>> *)
(******************************************************************************)

(* TODO <<kbind_kfmapd>> *)

(* TODO <<kfmapd_kbind>> *)

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
      kfmapd S j (extract (W ×) A) = @id (S A).
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

  (* TODO <<kfmap_kfmapd>> *)

  (* TODO <<kfmapd_kfmap>> *)

End DecoratedFunctor.

(** ** Monads (<<kbind>>) *)
(******************************************************************************)
Definition compose_km
           `{ix : Index}
           {W : Type}
           {T : K -> Type -> Type}
           `{forall k, MBind W T (T k)}
           `{! MReturn T}
           {j : K}
           {A : Type}
           (g : A -> T j A)
           (f : A -> T j A) : A -> T j A :=
  (kbind (T j) j g ∘ f).

Infix "⋆km" := compose_km (at level 40).

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
        kbind S j (g ⋆km f).
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

  (* TODO <<kfmap_kbind>> *)

  (* TODO <<kbind_kfmap>> *)

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

End Functor.

(** ** Notations **)
(******************************************************************************)
Module Notations.

  Infix "⋆dtm" := compose_dtm (at level 40) : tealeaves_scope.

  Infix "⋆kdm" := compose_kdm (at level 40) : tealeaves_scope.

  Infix "⋆km" := compose_km (at level 40) : tealeaves_scope.

End Notations.

From Tealeaves Require Import
  Functors.Constant
  Functors.List
  Classes.Applicative.

Import Categories.TypeFamilies.Notations.
Import Definitions.Sets.Notations.
Import Product.Notations.
Import Monoid.Notations.
Import List.ListNotations.

(** * Sorted lists with context *)
(******************************************************************************)
Section list.

  Context
    `{ix : Index}
    `{Monoid W}.

  Instance: MReturn (fun k A => list (W * (K * A))) :=
    fun A (k : K) (a : A) =>
      [(Ƶ, (k, a))].

  (** This operation is a context- and tag-sensitive substitution operation
   on lists of annotated values. It is used internally to reason about the
   interaction between <<mbinddt>> and <<tomlistd>>. *)
  Fixpoint mbinddt_list
           `(f : forall (k : K), W * A -> list (W * (K * B)))
           (l : list (W * (K * A))) : list (W * (K * B)) :=
    match l with
    | nil => nil
    | cons (w, (k, a)) rest =>
      map list (incr W w) (f k (w, a)) ++ mbinddt_list f rest
    end.

  Lemma mbinddt_list_nil : forall
      `(f : forall (k : K), W * A -> list (W * (K * B))),
      mbinddt_list f nil = nil.
  Proof.
    intros. easy.
  Qed.

  Lemma mbinddt_list_ret : forall
      `(f : forall (k : K), W * A -> list (W * (K * B))) (k : K) (a : A),
      mbinddt_list f (mret (fun k A => list (W * (K * A))) k a) = f k (Ƶ, a).
  Proof.
    intros. cbn. List.simpl_list.
    replace (incr W Ƶ) with (@id (W * (K * B))).
    - now rewrite (fun_map_id list).
    - ext [w [k2 b]]. cbn. now simpl_monoid.
  Qed.

  Lemma mbinddt_list_cons : forall
      `(f : forall (k : K), W * A -> list (W * (K * B)))
      (w : W) (k : K) (a : A)
      (l : list (W * (K * A))),
      mbinddt_list f ((w, (k, a)) :: l) = map list (incr W w) (f k (w, a)) ++ mbinddt_list f l.
  Proof.
    intros. easy.
  Qed.

  Lemma mbinddt_list_app : forall
      `(f : forall (k : K), W * A -> list (W * (K * B)))
      (l1 l2 : list (W * (K * A))),
      mbinddt_list f (l1 ++ l2) = mbinddt_list f l1 ++ mbinddt_list f l2.
  Proof.
    intros. induction l1.
    - easy.
    - destruct a as [w [k a]].
      cbn. rewrite IHl1.
      now rewrite List.app_assoc.
  Qed.

  #[global] Instance : forall `(f : forall (k : K), W * A -> list (W * (K * B))),
      ApplicativeMorphism (const (list (W * (K * A))))
                          (const (list (W * (K * B))))
                          (const (mbinddt_list f)).
  Proof.
    intros. eapply ApplicativeMorphism_monoid_morphism.
    Unshelve. constructor; try typeclasses eauto.
    - easy.
    - intros. apply mbinddt_list_app.
  Qed.

End list.

(** * The <<Batch>> idiom *)
(* This is not the true Batch functor, it has been specialized for its use case with DTMs.
 TODO: Generalize this so it can live in its own file. *)
(******************************************************************************)
Import Applicative.Notations.

Section Batch.

  #[local] Generalizable Variables D.
  #[local] Set Implicit Arguments.

  Context
    `{ix : Index}
    {T : K -> Type -> Type}
    {W A B : Type}.

  Inductive Batch C : Type :=
  | Go : C -> Batch C
  | Ap : forall (k : K), Batch (T k B -> C) -> W * A -> Batch C.

  Fixpoint map_Batch `{f : C -> D} `(c : Batch C) : Batch D :=
    match c with
    | Go c => Go (f c)
    | @Ap _ k rest (pair w a) =>
      Ap (@map_Batch (T k B -> C) (T k B -> D) (compose f) rest) (w, a)
    end.

  #[global] Instance Map_Batch : Map Batch := @map_Batch.

  Lemma map_id_Batch : forall (C : Type),
      map Batch id = @id (Batch C).
  Proof.
    intros. ext s. induction s.
    - easy.
    - unfold id in *. destruct p.
      now rewrite <- IHs at 2.
  Qed.

  Lemma map_map_Batch : forall (C D E : Type) (f : C -> D) (g : D -> E),
      map Batch g ∘ map Batch f = map Batch (g ∘ f).
  Proof.
    intros. unfold compose. ext s. generalize dependent E.
    generalize dependent D. induction s.
    - easy.
    - intros. destruct p. cbn. fequal.
      apply IHs.
  Qed.

  #[global, program] Instance Functor_Batch : Functor Batch :=
    {| fun_map_id := map_id_Batch;
       fun_map_map := map_map_Batch;
    |}.

  (** ** Applicative Instance *)
  (******************************************************************************)
  #[global] Instance Pure_Batch : Pure Batch :=
    fun (C : Type) (c : C) => Go c.

  Fixpoint mult_Batch `(jc : Batch C) `(jd : Batch D) : Batch (C * D) :=
    match jd with
    | Go d => map Batch (fun (c : C) => (c, d)) jc
    | Ap rest (pair w a) =>
      Ap (map Batch strength_arrow (mult_Batch jc rest)) (pair w a)
    end.

  #[global] Instance Mult_Batch : Mult Batch :=
    fun C D '(c, d) => mult_Batch c d.

  #[local] Infix "⧆" := Ap (at level 51, left associativity) : tealeaves_scope.
  Lemma mult_Batch_rw1 : forall `(a : A) `(b : B),
      Go a ⊗ Go b = Go (a, b).
  Proof.
    easy.
  Qed.

  Lemma mult_Batch_rw2 : forall `(d : D) `(jc : Batch C),
      jc ⊗ Go d = map Batch (pair_right d) jc.
  Proof.
    intros. induction jc; easy.
  Qed.

  Lemma mult_Batch_rw3 : forall `(d : D) `(jc : Batch C),
      Go d ⊗ jc = map Batch (pair d) jc.
  Proof.
    induction jc.
    - easy.
    - destruct p. cbn; change (mult_Batch ?x ?y) with (x ⊗ y).
      fequal. rewrite IHjc. compose near jc on left.
      now rewrite (fun_map_map Batch).
  Qed.

  Lemma mult_Batch_rw4 : forall (w : W) (a : A) (k : K) `(jc : @Batch (T k B -> C)) `(d : D),
      (jc ⧆ (w, a)) ⊗ Go d = map Batch (costrength_arrow ∘ pair_right d) jc ⧆ (w, a).
  Proof.
    easy.
  Qed.

  Lemma mult_Batch_rw5 : forall (w : W) (a : A) (k : K) `(jc : @Batch (T k B -> C)) `(d : D),
      Go d ⊗ (jc ⧆ (w, a)) = map Batch (strength_arrow ∘ pair d) jc ⧆ (w, a).
  Proof.
    intros. cbn. change (mult_Batch ?x ?y) with (x ⊗ y) in *.
    fequal. rewrite (mult_Batch_rw3 d). compose near jc on left.
    now rewrite (fun_map_map Batch).
  Qed.

  Lemma mult_Batch_rw6 :
    forall (w1 w2 : W) (a1 a2 : A) (k : K)
      `(jc : Batch (T k B -> C)) `(jd : Batch (T k B -> D)),
      (jc ⧆ (w1, a1)) ⊗ (jd ⧆ (w2, a2)) =
      map Batch strength_arrow ((jc ⧆ (w1, a1)) ⊗ jd) ⧆ (w2, a2).
  Proof.
    reflexivity.
  Qed.

  Lemma app_pure_natural_Batch : forall (C D : Type) (f : C -> D) (x : C),
      map Batch f (pure Batch x) = pure Batch (f x).
  Proof.
    easy.
  Qed.

  Lemma app_mult_natural_Batch1 : forall (C D E : Type) (f : C -> D) (x : Batch C) (y : Batch E),
      map Batch f x ⊗ y = map Batch (map_fst f) (x ⊗ y).
  Proof.
    intros. generalize dependent E. induction y.
    - intros; cbn. compose near x.
      now do 2 rewrite (fun_map_map Batch).
    - destruct p. cbn; change (mult_Batch ?x ?y) with (x ⊗ y).
      rewrite IHy. compose near (x ⊗ y).
      do 2 rewrite (fun_map_map Batch). do 2 fequal.
      now ext [? ?].
  Qed.

  Lemma app_mult_natural_Batch2 : forall (A B D : Type) (g : B -> D) (x : Batch A) (y : Batch B),
      x ⊗ map Batch g y = map Batch (map_snd g) (x ⊗ y).
  Proof.
    intros. generalize dependent D. induction y as [ANY any | ANY k rest IH [w a]].
    - intros; cbn. compose near x on right. now rewrite (fun_map_map Batch).
    - intros; cbn. fequal.
      change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite IH. compose near (x ⊗ rest).
      do 2 rewrite (fun_map_map Batch). fequal.
      now ext [a' mk].
  Qed.

  Lemma app_mult_natural_Batch : forall (A B C D : Type) (f : A -> C) (g : B -> D) (x : Batch A) (y : Batch B),
      map Batch f x ⊗ map Batch g y = map Batch (map_tensor f g) (x ⊗ y).
  Proof.
    intros. rewrite app_mult_natural_Batch1, app_mult_natural_Batch2.
    compose near (x ⊗ y) on left. rewrite (fun_map_map Batch). fequal.
    now ext [a b].
  Qed.

  Lemma app_assoc_Batch : forall (A B C : Type) (x : Batch A) (y : Batch B) (z : Batch C),
      map Batch associator ((x ⊗ y) ⊗ z) = x ⊗ (y ⊗ z).
  Proof.
    intros. induction z as [ANY any | ANY k rest IH [w a]].
    - do 2 rewrite mult_Batch_rw2.
      rewrite (app_mult_natural_Batch2). compose near (x ⊗ y) on left.
      now rewrite (fun_map_map Batch).
    - cbn. repeat change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      fequal. rewrite (app_mult_natural_Batch2).
      rewrite <- IH. compose near (x ⊗ y ⊗ rest).
      do 2 rewrite (fun_map_map Batch).
      compose near (x ⊗ y ⊗ rest) on right.
      rewrite (fun_map_map Batch).
      fequal. now ext [[? ?] ?].
  Qed.

  Lemma app_unital_l_Batch : forall (A : Type) (x : Batch A),
      map Batch left_unitor (pure Batch tt ⊗ x) = x.
  Proof.
    intros. induction x as [ANY any | ANY k rest IH [w a]].
    - easy.
    - cbn. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      fequal. compose near (pure Batch tt ⊗ rest).
      rewrite (fun_map_map Batch).
      rewrite <- IH. repeat fequal. auto.
  Qed.

  Lemma app_unital_r_Batch : forall (A : Type) (x : Batch A),
      map Batch right_unitor (x ⊗ pure Batch tt) = x.
  Proof.
    intros. induction x as [ANY any | ANY k rest IH [w a]].
    - easy.
    - cbn in *. fequal. rewrite <- IH at 2.
      compose near rest. now do 2 rewrite (fun_map_map Batch).
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

End Batch.

Arguments Ap {ix} {T}%function_scope {W A B}%type_scope [C]%type_scope {k} _ _.

(** ** Notations *)
(******************************************************************************)
Module Notations2.

  Infix "⧆" := Ap (at level 51, left associativity) : tealeaves_scope.

End Notations2.

Import Notations2.

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

  (*
  Check Go a1 ⊗ Go a2 : @Batch _ T W False False (A * A).
  Compute Go a1 ⊗ Go a2.
  Compute Go a1 ⊗ (Go mk1 ⧆ (w1, c1)).
  Compute (Go mk1 ⧆ (w1, c1)) ⊗ (Go mk1 ⧆ (w2, c2)).
  Compute (Go mk2 ⧆ (w1, c1) ⧆ (w2, c2)) ⊗ (Go mk1 ⧆ (w3, c3)).
   *)

End demo.

(** ** Functoriality of [Batch] *)
(******************************************************************************)
Section functoriality_Batch.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Fixpoint mapfst_Batch {A1 A2 B C} (f : A1 -> A2) `(j : @Batch _ T W A1 B C) : @Batch _ T W A2 B C :=
    match j with
    | Go a => Go a
    | Ap rest p => Ap (mapfst_Batch f rest) (map_snd f p)
    end.

End functoriality_Batch.

(** * The <<runBatch>> operation *)
(******************************************************************************)
Fixpoint runBatch
         {ix : Index} {T : K -> Type -> Type} {W A B : Type} {F : Type -> Type}
         `{Map F} `{Mult F} `{Pure F}
         (ϕ : forall (k : K), W * A -> F (T k B))
         `(j : @Batch ix T W A B C) : F C :=
  match j with
  | Go a => pure F a
  | @Ap _ _ _ _ _ _ k rest (pair w a) => runBatch ϕ rest <⋆> ϕ k (w, a)
  end.

Section runBatch_rw.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Context
    (A B C : Type)
    `{Applicative F}
    (f : forall k, W * A -> F (T k B)).

  Lemma runBatch_rw1 (c : C) :
    runBatch f (Go c) = pure F c.
  Proof.
    reflexivity.
  Qed.

  Lemma runBatch_rw2 (k : K) (w : W) (a : A) (rest : Batch (T k B -> C)) :
    runBatch f (rest ⧆ (w, a)) = runBatch f rest <⋆> f k (w, a).
  Proof.
    reflexivity.
  Qed.

End runBatch_rw.

(** ** Naturality of of <<runBatch>> *)
(******************************************************************************)
Section runBatch_naturality.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    `{Applicative F}.

  Context
    (A B C D : Type)
    `{Applicative F}
    (ϕ : forall k, W * A -> F (T k B)).

  Lemma natural_runBatch (f : C -> D) (j : @Batch _ T W A B C) :
    map F f (runBatch ϕ j) = runBatch ϕ (map Batch f j).
  Proof.
    generalize dependent D. induction j; intros.
    - cbn. now rewrite (app_pure_natural F).
    - destruct p. cbn. rewrite map_ap. fequal.
      now rewrite IHj.
  Qed.

End runBatch_naturality.

(** ** <<runBatch>> is an applicative morphism **)
(******************************************************************************)
Section runBatch_morphism.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Context
    (A B : Type)
    `{Applicative F}
    (f : forall k, W * A -> F (T k B)).

  Lemma appmor_pure_runBatch : forall (C : Type) (c : C),
      runBatch f (pure Batch c) = pure F c.
  Proof.
    easy.
  Qed.

  Lemma appmor_mult_runBatch : forall (C D : Type) (x : Batch C) (y : Batch D),
      runBatch f (x ⊗ y) = runBatch f x ⊗ runBatch f y.
  Proof.
    intros. generalize dependent x. induction y.
    - intros. rewrite mult_Batch_rw2.
      rewrite runBatch_rw1. rewrite triangle_4.
      rewrite natural_runBatch; auto.
    - intros. destruct p. rewrite runBatch_rw2.
      unfold ap. rewrite (app_mult_natural_r F).
      rewrite <- (app_assoc F).
      rewrite <- IHy. clear IHy.
      compose near (runBatch f (x ⊗ y) ⊗ f k (w, a)).
      rewrite (fun_map_map F).
      cbn. unfold ap. change (mult_Batch ?jx ?jy) with (jx ⊗ jy).
      rewrite <- natural_runBatch; auto.
      rewrite (app_mult_natural_l F).
      compose near (runBatch f (x ⊗ y) ⊗ f k (w, a)) on left.
      rewrite (fun_map_map F). fequal. now ext [[? ?] ?].
  Qed.

  #[global] Instance Morphism_store_fold: ApplicativeMorphism Batch F (@runBatch _ T W A B F _ _ _ f).
  Proof.
    constructor; try typeclasses eauto.
    - intros. now rewrite natural_runBatch.
    - intros. easy.
    - intros. apply appmor_mult_runBatch.
  Qed.

End runBatch_morphism.

(** ** <<runBatch>> commutes with applicative morphisms **)
(******************************************************************************)
Section runBatch_morphism.


  #[local] Generalizable All Variables.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}
    {A B C : Type}
    `{Applicative F}
    `{Applicative G}
    `{! ApplicativeMorphism F G ψ}
    (f : forall k, W * A -> F (T k B)).

  Lemma runBatch_morphism `(j : @Batch _ T W A B C) :
    @ψ C (runBatch f j) = runBatch (fun k => @ψ (T k B) ∘ f k) j.
  Proof.
    induction j.
    - cbn. now rewrite (appmor_pure F G).
    - destruct p. cbn. rewrite ap_morphism_1.
      now rewrite IHj.
  Qed.

End runBatch_morphism.

(** * Shape and contents *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Section shape_and_contents.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Definition shape {A} : S A -> S unit :=
    mfmap S (const (const tt)).

  Definition tomlistd_gen {A} (fake : Type) : S A -> list (W * (K * A)) :=
    mfmapdt (B := fake) S (const (list (W * (K * A)))) (fun k '(w, a) => [(w, (k, a))]).

  Definition tomlistd {A} : S A -> list (W * (K * A)) :=
    tomlistd_gen False.

  Definition tomsetd {A} : S A -> W * (K * A) -> Prop :=
    toset list ∘ tomlistd.

  Definition tomlist {A} : S A -> list (K * A) :=
    map list (extract (W ×) A) ∘ tomlistd.

  Definition tomset {A} : S A -> K * A -> Prop :=
    toset list ∘ tomlist.

  Fixpoint filterk {A} (k : K) (l : list (W * (K * A))) : list (W * A) :=
    match l with
    | nil => nil
    | cons (w, (j, a)) ts =>
      if k == j then (w, a) :: filterk k ts else filterk k ts
    end.

  Definition toklistd {A} (k : K) : S A -> list (W * A) :=
    filterk k ∘ tomlistd.

  Definition toksetd {A} (k : K) : S A -> W * A -> Prop :=
    toset list ∘ toklistd k.

  Definition toklist {A} (k : K) : S A -> list A :=
    map list (extract (W ×) A) ∘ @toklistd A k.

End shape_and_contents.

(** ** Notations *)
(******************************************************************************)
Module Notations3.

  Notation "x ∈md t" :=
    (tomsetd _ t x) (at level 50) : tealeaves_multi_scope.

  Notation "x ∈m t" :=
    (tomset _ t x) (at level 50) : tealeaves_multi_scope.

End Notations3.

Import Notations3.

(** ** Rewriting rules for <<filterk>> *)
(******************************************************************************)
Section rw_filterk.

  Context
    `{ix : Index} {W A : Type} (k : K).

  Implicit Types (l : list (W * (K * A))) (w : W) (a : A).

  Lemma filterk_nil : filterk k (nil : list (W * (K * A))) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filterk_cons_eq : forall l w a, filterk k (cons (w, (k, a)) l) = (w, a) :: filterk k l.
  Proof.
    intros. cbn. compare values k and k.
  Qed.

  Lemma filterk_cons_neq : forall l w a j, j <> k -> filterk k (cons (w, (j, a)) l) = filterk k l.
  Proof.
    intros. cbn. compare values k and j.
  Qed.

  Lemma filterk_app : forall l1 l2, filterk k (l1 ++ l2) = filterk k l1 ++ filterk k l2.
  Proof.
    intros. induction l1.
    - reflexivity.
    - destruct a as [w [i a]].
      compare values i and k.
      + rewrite <- (List.app_comm_cons l1).
        rewrite filterk_cons_eq.
        rewrite filterk_cons_eq.
        rewrite <- (List.app_comm_cons (filterk k l1)).
        now rewrite <- IHl1.
      + rewrite <- (List.app_comm_cons l1).
        rewrite filterk_cons_neq; auto.
        rewrite filterk_cons_neq; auto.
  Qed.

End rw_filterk.

#[export] Hint Rewrite @filterk_nil @filterk_cons_eq @filterk_cons_neq @filterk_app : tea_list.

(** ** Auxiliary lemmas for constant applicative functors *)
(******************************************************************************)
Section lemmas.

  #[local] Generalizable Variable M.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mbinddt_constant_applicative1
        `{Monoid M} {B : Type}
        `(f : forall (k : K), W * A -> const M (T k B)) :
    mbinddt (B := B) S (const M) f =
    mbinddt (B := False) S (const M) (f : forall (k : K), W * A -> const M (T k False)).
  Proof.
    change_right (map (B := S B) (const M) (mfmap S (const exfalso))
                       ∘ (mbinddt (B := False) S (const M) (f : forall (k : K), W * A -> const M (T k False)))).
    rewrite (mfmap_mbinddt S (F := const M)).
    reflexivity.
  Qed.

  Lemma mbinddt_constant_applicative2 (fake1 fake2 : Type) `{Monoid M}
        `(f : forall (k : K), W * A -> const M (T k B)) :
    mbinddt (B := fake1) S (const M)
            (f : forall (k : K), W * A -> const M (T k fake1))
    = mbinddt (B := fake2) S (const M)
              (f : forall (k : K), W * A -> const M (T k fake2)).
  Proof.
    intros. rewrite (mbinddt_constant_applicative1 (B := fake1)).
    rewrite (mbinddt_constant_applicative1 (B := fake2)). easy.
  Qed.

  Lemma tomlistd_equiv1 : forall (fake : Type) (A : Type),
      tomlistd_gen S (A := A) False = tomlistd_gen S fake.
  Proof.
    intros. unfold tomlistd_gen at 2, mfmapdt.
    now rewrite (mbinddt_constant_applicative2 fake False).
  Qed.

  Lemma tomlistd_equiv : forall (fake1 fake2 : Type) (A : Type),
      tomlistd_gen S (A := A) fake1 = tomlistd_gen S fake2.
  Proof.
    intros. rewrite <- tomlistd_equiv1.
    rewrite <- (tomlistd_equiv1 fake2).
    easy.
  Qed.

End lemmas.

(** ** Relating <<∈m>> and <<∈md>> *)
(******************************************************************************)
Section DTM_membership_lemmas.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma ind_iff_in : forall (k : K) (A : Type) (a : A) (t : S A),
      (k, a) ∈m t <-> exists w, (w, (k, a)) ∈md t.
  Proof.
    intros. unfold tomset, tomsetd, tomlist, compose.
    induction (tomlistd S t).
    - cbv; split; intros []; easy.
    - rewrite map_list_cons, in_list_cons. rewrite IHl.
      setoid_rewrite in_list_cons.
      split; [ intros [Hfst|[w Hrest]] | intros [w [rest1|rest2]]].
      + destruct a0 as [w [k' a']]. exists w. left.
        rewrite Hfst. easy.
      + exists w. now right.
      + left. now rewrite <- rest1.
      + right. rewrite <- IHl.
        rewrite (in_map_iff list). now exists (w, (k, a)).
  Qed.

  Corollary ind_implies_in : forall (k : K) (A : Type) (a : A) (w : W) (t : S A),
      (w, (k, a)) ∈md t -> (k, a) ∈m t.
  Proof.
    intros. rewrite ind_iff_in. eauto.
  Qed.

End DTM_membership_lemmas.

(** ** Characterizing membership in list operations *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma in_filterk_iff : forall (A : Type) (l : list (W * (K * A))) (k : K) (a : A) (w : W),
      (w, a) ∈ filterk k l <-> (w, (k, a)) ∈ l.
  Proof.
    intros. induction l.
    - cbn. easy.
    - destruct a0 as [w' [j a']]. cbn. compare values k and j.
      + cbn. rewrite IHl. clear. split.
        { intros [hyp1 | hyp2].
          - inverts hyp1. now left.
          - now right.
        }
        { intros [hyp1 | hyp2].
          - inverts hyp1. now left.
          - now right. }
      + rewrite <- IHl. split.
        { intro hyp. now right. }
        { intros [hyp1 | hyp2].
          - inverts hyp1. contradiction.
          - auto. }
  Qed.

  Lemma ind_iff_in_tomlistd : forall (A : Type) (k : K) (a : A) (w : W) (t : S A),
      (w, (k, a)) ∈md t <-> (w, (k, a)) ∈ tomlistd S t.
  Proof.
    reflexivity.
  Qed.

  Lemma in_iff_in_tomlistd : forall (A : Type) (k : K) (a : A) (t : S A),
      (k, a) ∈m t <-> (k, a) ∈ tomlist S t.
  Proof.
    reflexivity.
  Qed.

  Lemma ind_iff_in_toklistd : forall (A : Type) (k : K) (a : A) (w : W) (t : S A),
      (w, (k, a)) ∈md t <-> (w, a) ∈ toklistd S k t.
  Proof.
    intros. unfold toklistd. unfold compose.
    rewrite in_filterk_iff. reflexivity.
  Qed.

  Lemma in_iff_in_toklist : forall (A : Type) (k : K) (a : A) (t : S A),
      (k, a) ∈m t <-> a ∈ toklist S k t.
  Proof.
    intros. unfold toklist. unfold compose.
    rewrite (in_map_iff list). split.
    - intro hyp. rewrite ind_iff_in in hyp.
      destruct hyp as [w' hyp].
      exists (w', a). rewrite ind_iff_in_toklistd in hyp.
      auto.
    - intros [[w' a'] [hyp1 hyp2]]. rewrite ind_iff_in.
      exists w'. rewrite <- ind_iff_in_toklistd in hyp1. cbn in hyp2.
      now subst.
  Qed.

End DTM_tolist.

(** ** Interaction between <<tomlistd>> and <<mret>>/<<mbindd>> *)
(******************************************************************************)
Section DTM_tolist.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma tomlistd_gen_mret : forall (A B : Type) (a : A) (k : K),
      tomlistd_gen (T k) B (mret T k a) = [ (Ƶ, (k, a)) ].
  Proof.
    intros. unfold tomlistd_gen.
    compose near a on left.
    now rewrite mfmapdt_comp_mret.
  Qed.

  Corollary tomlistd_mret : forall (A : Type) (a : A) (k : K),
      tomlistd (T k) (mret T k a) = [ (Ƶ, (k, a)) ].
  Proof.
    intros. unfold tomlistd. apply tomlistd_gen_mret.
  Qed.

  Corollary tomsetd_mret : forall (A : Type) (a : A) (k : K),
      tomsetd (T k) (mret T k a) = {{ (Ƶ, (k, a)) }}.
  Proof.
    intros. unfold tomsetd, compose. rewrite tomlistd_mret.
    solve_basic_set.
  Qed.

  Corollary tomlist_mret : forall (A : Type) (a : A) (k : K),
      tomlist (T k) (mret T k a) = [ (k, a) ].
  Proof.
    intros. unfold tomlist, compose.
    rewrite tomlistd_mret. easy.
  Qed.

  Corollary tomset_mret : forall (A : Type) (a : A) (k : K),
      tomset (T k) (mret T k a) = {{ (k, a) }}.
  Proof.
    intros. unfold tomset, compose.
    rewrite tomlist_mret. solve_basic_set.
  Qed.

  Lemma tomlistd_gen_mbindd :
    forall (fake : Type)
      `(f : forall k, W * A -> T k B) (t : S A),
      tomlistd_gen S fake (mbindd S f t) =
      mbinddt_list (fun k '(w, a) => tomlistd_gen (T k) fake (f k (w, a))) (tomlistd_gen S fake t).
  Proof.
    intros. unfold tomlistd_gen, mfmapdt.
    compose near t on left.
    rewrite (mbinddt_mbindd S).
    compose near t on right.
    change (mbinddt_list ?f) with (const (mbinddt_list f) (S fake)).
    #[local] Set Keyed Unification. (* TODO figure out why this is here. *)
    rewrite (dtp_mbinddt_morphism W S T
                                  (const (list (W * (K * A))))
                                  (const (list (W * (K * B))))
                                  (A := A) (B := fake)).
    #[local] Unset Keyed Unification.
    fequal. ext k [w a].
    cbn.
    change (map list ?f) with (const (map list f) (S B)).
    List.simpl_list.
    compose near (f k (w, a)) on right.
    (* for some reason I can't rewrite without posing first. *)
    pose (rw := dtp_mbinddt_morphism
                  W (T k) T
                  (const (list (W * (K * B))))
                  (const (list (W * (K * B))))
                  (ϕ := (const (map list (incr W w))))
                  (A := B) (B := fake)).
    rewrite rw. fequal. now ext k2 [w2 b].
  Qed.

  Corollary tomlistd_mbindd : forall
      `(f : forall k, W * A -> T k B) (t : S A),
      tomlistd S (mbindd S f t) =
      mbinddt_list (fun k '(w, a) => tomlistd (T k) (f k (w, a))) (tomlistd S t).
  Proof.
    intros. unfold tomlistd. apply tomlistd_gen_mbindd.
  Qed.

End DTM_tolist.

(** ** Characterizing occurrences post-operation *)
(******************************************************************************)
Section DTM_membership.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  (** *** Occurrences in <<mret>> *)
  (******************************************************************************)
  Lemma ind_mret_iff : forall (A : Type) (a1 a2 : A) (k1 k2 : K) (w : W),
      (w, (k2, a2)) ∈md mret T k1 a1 <-> w = Ƶ /\ k1 = k2 /\ a1 = a2.
  Proof.
    intros. rewrite (tomsetd_mret (T k1)).
    simpl_set. split.
    - inversion 1; now subst.
    - introv [? [? ?]]. now subst.
  Qed.

  Corollary in_mret_iff : forall (A : Type) (a1 a2 : A) (k1 k2 : K),
      (k2, a2) ∈m mret T k1 a1 <-> k1 = k2 /\ a1 = a2.
  Proof.
    intros. rewrite ind_iff_in. setoid_rewrite ind_mret_iff.
    firstorder.
  Qed.

  Lemma ind_mret_eq_iff : forall (A : Type) (a1 a2 : A) (k : K) (w : W),
      (w, (k, a2)) ∈md mret T k a1 <-> w = Ƶ /\ a1 = a2.
  Proof.
    intros. rewrite ind_mret_iff. clear. firstorder.
  Qed.

  Lemma ind_mret_neq_iff : forall (A : Type) (a1 a2 : A) (k j : K) (w : W),
      k <> j ->
      (w, (j, a2)) ∈md mret T k a1 <-> False.
  Proof.
    intros. rewrite ind_mret_iff. firstorder.
  Qed.

  Corollary in_mret_eq_iff : forall (A : Type) (a1 a2 : A) (k : K),
      (k, a2) ∈m mret T k a1 <-> a1 = a2.
  Proof.
    intros. rewrite in_mret_iff. firstorder.
  Qed.

  Corollary in_mret_neq_iff : forall (A : Type) (a1 a2 : A) (k j : K),
      k <> j ->
      (j, a2) ∈m mret T k a1 <-> False.
  Proof.
    intros. rewrite ind_iff_in. setoid_rewrite ind_mret_iff.
    firstorder.
  Qed.

  (** *** Occurrences in <<mbindd>> with context *)
  (******************************************************************************)
  Lemma ind_mbindd_iff1 :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbindd S f t ->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold tomsetd, compose in *.
    rewrite (tomlistd_mbindd S) in hyp. induction (tomlistd S t).
    - inversion hyp.
    - destruct a as [w [k a]]. rewrite mbinddt_list_cons in hyp.
      rewrite in_list_app in hyp. destruct hyp as [hyp1 | hyp2].
      + rewrite (in_map_iff list) in hyp1.
        destruct hyp1 as [[w2 [k2' b']] [hyp1 hyp2]].
        inversion hyp2; subst. exists k w w2 a. splits.
        { rewrite in_list_cons. now left. }
        { auto. }
        { easy. }
      + apply IHl in hyp2. clear IHl.
        destruct hyp2 as [k1 [w1 [w2 [a' [hyp1 [hyp2 hyp3]] ]]]].
        subst. repeat eexists.
        { rewrite in_list_cons. right. eauto. }
        { auto. }
  Qed.

  Lemma ind_mbindd_iff2 :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
    (exists (k1 : K) (w1 w2 : W) (a : A),
      (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2) ->
      (wtotal, (k2, b)) ∈md mbindd S f t.
  Proof.
    introv [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]. subst.
    unfold tomsetd, compose in *. rewrite (tomlistd_mbindd S).
    induction (tomlistd S t).
    - inversion hyp1.
    - destruct a0 as [w [k' a']]. rewrite mbinddt_list_cons.
      simpl_list. rewrite in_list_cons in hyp1. destruct hyp1 as [hyp1 | hyp1].
      + inverts hyp1. left. rewrite (in_map_iff list). exists (w2, (k2, b)).
        now splits.
      + right. now apply IHl in hyp1.
  Qed.

  Theorem ind_mbindd_iff :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbindd S f t <->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 (w1, a)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using ind_mbindd_iff1, ind_mbindd_iff2.
  Qed.

  (** *** Corollaries for other operations *)
  (******************************************************************************)
  Corollary ind_mbind_iff :
    forall `(f : forall k, A -> T k B) (t : S A) (k2 : K) (wtotal : W) (b : B),
      (wtotal, (k2, b)) ∈md mbind S f t <->
      exists (k1 : K) (w1 w2 : W) (a : A),
        (w1, (k1, a)) ∈md t /\ (w2, (k2, b)) ∈md f k1 a
        /\ wtotal = w1 ● w2.
  Proof.
    intros. rewrite mbind_to_mbindd. apply ind_mbindd_iff.
  Qed.

  Corollary ind_mfmapd_iff :
    forall `(f : forall k, W * A -> B) (t : S A) (k : K) (w : W) (b : B),
      (w, (k, b)) ∈md mfmapd S f t <->
      exists (a : A), (w, (k, a)) ∈md t /\ b = f k (w, a).
  Proof.
    intros. unfold mfmapd, compose. setoid_rewrite ind_mbindd_iff.
    unfold_ops @Map_I. setoid_rewrite ind_mret_iff.
    split.
    - intros [k1 [w1 [w2 [a [hyp1 [[hyp2 [hyp2' hyp2'']] hyp3]]]]]].
      subst. exists a. simpl_monoid. auto.
    - intros [a [hyp1 hyp2]]. subst. repeat eexists.
      easy. now simpl_monoid.
  Qed.

  Corollary ind_mfmap_iff :
    forall `(f : K -> A -> B) (t : S A) (k : K) (w : W) (b : B),
      (w, (k, b)) ∈md mfmap S f t <->
      exists (a : A), (w, (k, a)) ∈md t /\ b = f k a.
  Proof.
    intros. rewrite (mfmap_to_mfmapd S).
    rewrite ind_mfmapd_iff. easy.
  Qed.

  (** *** Occurrences without context *)
  (******************************************************************************)
  Theorem in_mbindd_iff :
    forall `(f : forall k, W * A -> T k B) (t : S A) (k2 : K) (b : B),
      (k2, b) ∈m mbindd S f t <->
      exists (k1 : K) (w1 : W) (a : A),
        (w1, (k1, a)) ∈md t
        /\ (k2, b) ∈m (f k1 (w1, a)).
  Proof.
    intros.
    rewrite ind_iff_in. setoid_rewrite ind_mbindd_iff. split.
    - intros [wtotal [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]].
      exists k1 w1 a. split; [auto|].
      apply (ind_implies_in) in hyp2. auto.
    - intros [k1 [w1 [a [hyp1 hyp2]]]].
      rewrite ind_iff_in in hyp2. destruct hyp2 as [w2 rest].
      exists (w1 ● w2) k1 w1 w2 a. intuition.
  Qed.

  (** *** Corollaries for other operations *)
  (******************************************************************************)
  Corollary in_mbind_iff :
    forall `(f : forall k, A -> T k B) (t : S A) (k2 : K) (b : B),
      (k2, b) ∈m mbind S f t <->
      exists (k1 : K) (a : A), (k1, a) ∈m t /\ (k2, b) ∈m f k1 a.
  Proof.
    intros. unfold mbind, compose. setoid_rewrite ind_iff_in.
    setoid_rewrite ind_mbindd_iff. cbn. split.
    - firstorder.
    - intros [k1 [a [[w1 hyp1] [w hyp2]]]].
      repeat eexists; eauto.
  Qed.

  Corollary in_mfmapd_iff :
    forall `(f : forall k, W * A -> B) (t : S A) (k : K) (b : B),
      (k, b) ∈m mfmapd S f t <->
      exists (w : W) (a : A), (w, (k, a)) ∈md t /\ b = f k (w, a).
  Proof.
    intros. setoid_rewrite ind_iff_in.
    now setoid_rewrite ind_mfmapd_iff.
  Qed.

  Corollary in_mfmap_iff :
    forall `(f : forall k, A -> B) (t : S A) (k : K) (b : B),
      (k, b) ∈m mfmap S f t <->
      exists (a : A), (k, a) ∈m t /\ b = f k a.
  Proof.
    intros. setoid_rewrite ind_iff_in.
    setoid_rewrite ind_mfmap_iff.
    firstorder.
  Qed.

End DTM_membership.

(** ** Characterizing occurrences post-operation (targetted operations) *)
(******************************************************************************)
Section DTM_membership_targetted.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Context
    (j : K)
    {A : Type}.

  (** *** Occurrences in <<kbindd>> with context *)
  (******************************************************************************)
  Lemma ind_kbindd_eq_iff1 :
    forall `(f : W * A -> T j A) (t : S A) (wtotal : W) (a2 : A),
      (wtotal, (j, a2)) ∈md kbindd S j f t ->
      exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (j, a2)) ∈md f (w1, a1)
        /\ wtotal = w1 ● w2.
  Proof.
    introv hyp. unfold kbindd in hyp.
    apply (ind_mbindd_iff1 S) in hyp.
    destruct hyp as [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]. subst.
    compare values j and k1.
    + exists w1 w2 a. splits.
      { auto. }
      { rewrite btgd_eq in hyp2. auto. }
      { reflexivity. }
    + rewrite btgd_neq in hyp2; auto.
      unfold compose in hyp2; cbn in hyp2.
      rewrite ind_mret_iff in hyp2. destructs hyp2.
      subst. contradiction.
  Qed.

  Lemma ind_kbindd_eq_iff2 :
    forall `(f : W * A -> T j A) (t : S A) (wtotal : W) (a2 : A),
      (exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (j, a2)) ∈md f (w1, a1)
        /\ wtotal = w1 ● w2) ->
      (wtotal, (j, a2)) ∈md kbindd S j f t.
  Proof.
    introv [w1 [w2 [a1 hyp]]]. destructs hyp. unfold kbindd.
    apply (ind_mbindd_iff2 S).
    exists j w1 w2 a1. rewrite btgd_eq. auto.
  Qed.

  Theorem ind_kbindd_eq_iff :
    forall `(f : W * A -> T j A) (t : S A) (wtotal : W) (a2 : A),
      (wtotal, (j, a2)) ∈md kbindd S j f t <->
      exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (j, a2)) ∈md f (w1, a1)
        /\ wtotal = w1 ● w2.
  Proof.
    split; auto using ind_kbindd_eq_iff1, ind_kbindd_eq_iff2.
  Qed.

  Lemma ind_kbindd_neq_iff1 :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> T j A) (t : S A) (wtotal : W) (a2 : A),
      (wtotal, (i, a2)) ∈md kbindd S j f t ->
      (wtotal, (i, a2)) ∈md t \/
      (exists (w1 w2 : W) (a1 : A), (w1, (j, a1)) ∈md t /\ (w2, (i, a2)) ∈md f (w1, a1) /\ wtotal = w1 ● w2).
  Proof.
    introv ? hyp. unfold kbindd in hyp.
    apply (ind_mbindd_iff1 S) in hyp.
    destruct hyp as [k1 [w1 [w2 [a [hyp1 [hyp2 hyp3]]]]]]. subst.
    compare values j and k1.
    + right. exists w1 w2 a. rewrite btgd_eq in hyp2. splits; auto.
    + left. rewrite btgd_neq in hyp2; auto.
      unfold compose in hyp2. cbn in hyp2.
      rewrite ind_mret_iff in hyp2. destructs hyp2; subst.
      simpl_monoid. auto.
  Qed.

  Lemma ind_kbindd_neq_iff2 :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> T j A) (t : S A) (wtotal : W) (a2 : A),
      (wtotal, (i, a2)) ∈md t \/
      (exists (w1 w2 : W) (a1 : A), (w1, (j, a1)) ∈md t /\ (w2, (i, a2)) ∈md f (w1, a1) /\ wtotal = w1 ● w2) ->
      (wtotal, (i, a2)) ∈md kbindd S j f t.
  Proof.
    introv ? hyp. destruct hyp as [hyp | hyp].
    - apply (ind_mbindd_iff2 S). exists i wtotal Ƶ a2.
      splits.
      { auto. }
      { rewrite btgd_neq; auto. unfold compose; cbn.
        rewrite ind_mret_iff; auto. }
      { now simpl_monoid. }
    - destruct hyp as [w1 [w2 [a1 [hyp1 [hyp2 hyp3]]]]]. subst.
      apply (ind_mbindd_iff2 S).
      exists j w1 w2 a1. rewrite btgd_eq. auto.
  Qed.

  Theorem ind_kbindd_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> T j A) (t : S A) (wtotal : W) (a2 : A),
      (wtotal, (i, a2)) ∈md kbindd S j f t <->
      (wtotal, (i, a2)) ∈md t \/
      (exists (w1 w2 : W) (a1 : A), (w1, (j, a1)) ∈md t /\ (w2, (i, a2)) ∈md f (w1, a1) /\ wtotal = w1 ● w2).
  Proof.
    split; auto using ind_kbindd_neq_iff1, ind_kbindd_neq_iff2.
  Qed.

  (** *** Corollaries for <<kbind>>, <<kfmapd>>, and <<kfmap>>*)
  (******************************************************************************)
  Corollary ind_kbind_eq_iff :
    forall `(f : A -> T j A) (t : S A) (wtotal : W) (a2 : A),
      (wtotal, (j, a2)) ∈md kbind S j f t <->
      exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (j, a2)) ∈md f a1
        /\ wtotal = w1 ● w2.
  Proof.
    intros. rewrite kbind_to_kbindd. now rewrite (ind_kbindd_eq_iff).
  Qed.

  Corollary ind_kbind_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : A -> T j A) (t : S A) (wtotal : W) (a2 : A),
      (wtotal, (i, a2)) ∈md kbind S j f t <->
      (wtotal, (i, a2)) ∈md t \/
      (exists (w1 w2 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (w2, (i, a2)) ∈md f a1
        /\ wtotal = w1 ● w2).
  Proof.
    intros. rewrite kbind_to_kbindd. rewrite ind_kbindd_neq_iff; auto.
    unfold compose. cbn. easy.
  Qed.

  Corollary ind_kfmapd_eq_iff :
    forall `(f : W * A -> A) (t : S A) (w : W) (a2 : A),
      (w, (j, a2)) ∈md kfmapd S j f t <->
      exists (a1 : A), (w, (j, a1)) ∈md t /\ a2 = f (w, a1).
  Proof.
    intros. unfold kfmapd. rewrite (ind_mfmapd_iff S).
    now rewrite tgtd_eq.
  Qed.

  Corollary ind_kfmapd_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> A) (t : S A) (w : W) (a2 : A),
      (w, (i, a2)) ∈md kfmapd S j f t <->
      (w, (i, a2)) ∈md t.
  Proof.
    intros. unfold kfmapd. rewrite (ind_mfmapd_iff S).
    rewrite tgtd_neq; auto. cbn. split.
    - intros [a [hyp eq]]; subst. auto.
    - intros hyp. now (exists a2).
  Qed.

  Corollary ind_kfmap_eq_iff :
    forall `(f : A -> A) (t : S A) (w : W) (a2 : A),
      (w, (j, a2)) ∈md kfmap S j f t <->
      exists (a1 : A), (w, (j, a1)) ∈md t /\ a2 = f a1.
  Proof.
    intros. unfold kfmap. rewrite (ind_mfmap_iff S).
    now rewrite tgt_eq.
  Qed.

  Corollary ind_kfmap_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : A -> A) (t : S A) (w : W) (a2 : A),
      (w, (i, a2)) ∈md kfmap S j f t <->
      (w, (i, a2)) ∈md t.
  Proof.
    intros. unfold kfmap. rewrite (ind_mfmap_iff S).
    rewrite tgt_neq; auto. split.
    - intros [a [hyp eq]]; subst. auto.
    - intros hyp. now (exists a2).
  Qed.

  (** *** Occurrences without context *)
  (******************************************************************************)
  Theorem in_kbindd_eq_iff :
    forall `(f : W * A -> T j A) (t : S A) (a2 : A),
      (j, a2) ∈m kbindd S j f t <->
      exists (w1 : W) (a1 : A),
        (w1, (j, a1)) ∈md t /\ (j, a2) ∈m f (w1, a1).
  Proof.
    intros. rewrite ind_iff_in.
    setoid_rewrite ind_iff_in.
    setoid_rewrite ind_kbindd_eq_iff.
    split.
    - intros [w [w1 [w2 [a1 [hyp1 [hyp2 hyp3]]]]]].
      eexists. eexists. split; eauto.
    - intros [w [a1 [hyp1 [w2 hyp2]]]].
      repeat eexists; eauto.
  Qed.

  Theorem in_kbindd_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> T j A) (t : S A) (a2 : A),
      (i, a2) ∈m kbindd S j f t <->
      (i, a2) ∈m t \/
      (exists (w1 : W) (a1 : A), (w1, (j, a1)) ∈md t /\ (i, a2) ∈m f (w1, a1)).
  Proof.
    intros. rewrite ind_iff_in.
    setoid_rewrite ind_iff_in.
    setoid_rewrite ind_kbindd_neq_iff; auto.
    split.
    - intros [w [hyp | hyp]].
      + left. eauto.
      + right. destruct hyp as [w1 [w2 [a1 [hyp1 [hyp2 hyp3]]]]].
        repeat eexists; eauto.
    - intros [hyp | hyp].
      + destruct hyp as [w hyp]. eexists. left. eauto.
      + destruct hyp as [w1 [a1 [hyp1 [w2 hyp2]]]].
        eexists. right. repeat eexists; eauto.
  Qed.

 Corollary in_kbind_eq_iff :
    forall `(f : A -> T j A) (t : S A) (a2 : A),
      (j, a2) ∈m kbind S j f t <->
      exists (a1 : A),
        (j, a1) ∈m t /\ (j, a2) ∈m f a1.
  Proof.
    intros. rewrite kbind_to_kbindd. rewrite (in_kbindd_eq_iff).
    setoid_rewrite ind_iff_in at 2.
    unfold compose. cbn. firstorder.
  Qed.

  Corollary in_kbind_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : A -> T j A) (t : S A) (a2 : A),
      (i, a2) ∈m kbind S j f t <->
      (i, a2) ∈m t \/
      (exists (a1 : A),
        (j, a1) ∈m t /\ (i, a2) ∈m f a1).
  Proof.
    intros. rewrite kbind_to_kbindd. rewrite in_kbindd_neq_iff; auto.
    split.
    - intros [hyp|hyp].
      + now left.
      + right. unfold compose in hyp. cbn in hyp.
        destruct hyp as [? [a1 [hyp1 hyp2]]].
        apply ind_implies_in in hyp1. eauto.
    - intros [hyp|hyp].
      + now left.
      + right.
        destruct hyp as [a1 [hyp1 hyp2]].
        rewrite ind_iff_in in hyp1. destruct hyp1 as [w1 hyp1].
        exists w1 a1. auto.
  Qed.

  Corollary in_kfmapd_eq_iff :
    forall `(f : W * A -> A) (t : S A) (a2 : A),
      (j, a2) ∈m kfmapd S j f t <->
      exists (w : W) (a1 : A), (w, (j, a1)) ∈md t /\ a2 = f (w, a1).
  Proof.
    intros. unfold kfmapd. rewrite (in_mfmapd_iff S).
    now rewrite tgtd_eq.
  Qed.

  Corollary in_kfmapd_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : W * A -> A) (t : S A) (a2 : A),
      (i, a2) ∈m kfmapd S j f t <->
      (i, a2) ∈m t.
  Proof.
    intros. unfold kfmapd. rewrite (in_mfmapd_iff S).
    rewrite tgtd_neq; auto. cbn. split.
    - intros [w [a [hyp eq]]]; subst.
      eapply ind_implies_in; eauto.
    - intros hyp. rewrite ind_iff_in in hyp.
      destruct hyp as [w hyp]. eauto.
  Qed.

  Corollary in_kfmap_eq_iff :
    forall `(f : A -> A) (t : S A) (a2 : A),
      (j, a2) ∈m kfmap S j f t <->
      exists (a1 : A), (j, a1) ∈m t /\ a2 = f a1.
  Proof.
    intros. unfold kfmap. rewrite (in_mfmap_iff S).
    now rewrite tgt_eq.
  Qed.

  Corollary in_kfmap_neq_iff :
    forall (i : K) (Hneq : j <> i) `(f : A -> A) (t : S A) (a2 : A),
      (i, a2) ∈m kfmap S j f t <->
      (i, a2) ∈m t.
  Proof.
    intros. unfold kfmap. rewrite (in_mfmap_iff S).
    rewrite tgt_neq; auto. split.
    - intros [a [hyp ?]]; subst. assumption.
    - intros; now (exists a2).
  Qed.

End DTM_membership_targetted.

Import Notations2.

(** * Iterating over a DTM *)
(******************************************************************************)
Section schedule_operation.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Definition schedule {A : Type} (B : Type) : forall (k : K), W * A -> @Batch _ T W A B (T k B) :=
    fun k '(w, a) => Go (@id (T k B)) ⧆ (w, a).

  Definition iterate {A : Type} (B : Type) : S A -> @Batch _ T W A B (S B) :=
    mbinddt S (@Batch _ T W A B) (schedule B).

End schedule_operation.

(** ** Representing <<mbinddt>> with <<runBatch>> *)
(******************************************************************************)

Section iterate.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T}.

  Theorem mbinddt_to_runBatch :
    forall `{Applicative F} (A B : Type) (t : S A)
      (f : forall k, W * A -> F (T k B)),
      mbinddt S F f t = runBatch f (iterate S B t).
  Proof.
    intros. unfold iterate.
    compose near t on right.
    rewrite (dtp_mbinddt_morphism W S T Batch F).
    fequal. ext k [w a]. cbn.
    now rewrite ap1.
  Qed.

  Corollary mbindd_to_runBatch :
    forall (A B : Type) (t : S A)
      (f : forall k, W * A -> T k B),
      mbindd S f t = runBatch (F := fun A => A) f (iterate S B t).
  Proof.
    intros. rewrite mbindd_to_mbinddt. now rewrite mbinddt_to_runBatch.
  Qed.

  Corollary mbindt_to_runBatch :
    forall `{Applicative F} (A B : Type) (t : S A)
      (f : forall k, A -> F (T k B)),
      mbindt S F f t = runBatch (f ◻ const (extract (W ×) A)) (iterate S B t).
  Proof.
    intros. rewrite mbindt_to_mbinddt. now rewrite mbinddt_to_runBatch.
  Qed.

  Corollary mfmapdt_to_runBatch  :
    forall `{Applicative F} (A B : Type) (t : S A)
      `(f : K -> W * A -> F B),
      mfmapdt S F f t = runBatch (fun k => map F (mret T k) ∘ f k) (iterate S B t).
  Proof.
    intros. rewrite mfmapdt_to_mbinddt. now rewrite mbinddt_to_runBatch.
  Qed.

  Corollary mbind_to_runBatch :
    forall (A B : Type) (t : S A)
      (f : forall k, A -> T k B),
      mbind S f t = runBatch (F := fun A => A) (f ◻ const (extract (W ×) A)) (iterate S B t).
  Proof.
    intros. rewrite mbind_to_mbinddt. now rewrite mbinddt_to_runBatch.
  Qed.

  Corollary mfmapd_to_runBatch `(f : K -> W * A -> B) (t : S A) :
    mfmapd S f t = runBatch (F := fun A => A) (mret T ◻ f) (iterate S B t).
  Proof.
    rewrite mfmapd_to_mbinddt. now rewrite mbinddt_to_runBatch.
  Qed.

  Corollary mfmapt_to_runBatch `{Applicative F} `(f : K -> A -> F B) (t : S A) :
    mfmapt S F f t = runBatch (fun k => map F (mret T k) ∘ f k ∘ extract (W ×) A) (iterate S B t).
  Proof.
    rewrite mfmapt_to_mbinddt. now rewrite mbinddt_to_runBatch.
  Qed.

  Corollary mfmap_to_runBatch `(f : K -> A -> B) (t : S A) :
    mfmap S f t = runBatch (F := fun A => A) (mret T ◻ f ◻ const (extract (W ×) A)) (iterate S B t).
  Proof.
    rewrite mfmap_to_mbinddt. now rewrite mbinddt_to_runBatch.
  Qed.

  (** ** Identities for <<tolist>> and <<foldMap>> *)
  (******************************************************************************)
  Lemma tomlistd_gen_to_runBatch (fake : Type) `(t : S A) :
    tomlistd_gen S fake t = runBatch (fun k '(w, a) => [(w, (k, a))]) (iterate S fake t).
  Proof.
    unfold tomlistd_gen. now rewrite mfmapdt_to_runBatch.
  Qed.

  Lemma tomlistd_to_runBatch  (fake : Type) `(t : S A) :
    tomlistd S t = runBatch (fun k '(w, a) => [(w, (k, a))]) (iterate S fake t).
  Proof.
    unfold tomlistd. rewrite (tomlistd_equiv S False fake).
    now rewrite tomlistd_gen_to_runBatch.
  Qed.

  Lemma tomsetd_to_runBatch  (fake : Type) `(t : S A) :
    tomsetd S t = runBatch (F := (@const Type Type (set (W * (K * A)))))
                              (fun k '(w, a) => {{(w, (k, a))}}) (iterate S fake t).
  Proof.
    unfold tomsetd, compose. rewrite (tomlistd_to_runBatch fake).
    change (toset list (A := W * (K * A))) with (const (toset (A := W * (K * A)) list) (S fake)).
    cbn. (* <- needed for implicit arguments. *)
    rewrite (runBatch_morphism (F := const (list (W * (K * A)))) (G := const (set (W * (K * A))))).
    unfold compose. fequal. ext k [w a].
    solve_basic_set.
  Qed.

  Lemma tomlist_to_runBatch (fake : Type) `(t : S A) :
    tomlist S t = runBatch (fun k '(w, a) => [(k, a)]) (iterate S fake t).
  Proof.
    unfold tomlist. unfold compose. rewrite (tomlistd_to_runBatch fake).
    change (map list ?f) with (const (map list f) (S fake)).
    rewrite (runBatch_morphism (F := const (list (W * (K * A))))
                                  (G := const (list (K * A)))
                                  (ψ := const (map list (extract (prod W))))).
    fequal. now ext k [w a].
  Qed.

  (** ** Other identities *)
  (******************************************************************************)
  Lemma id_to_runBatch `(t : S A) :
    t = runBatch (F := fun A => A) (mret T ◻ const (extract (W ×) A)) (iterate S A t).
  Proof.
    change t with (id t) at 1.
    rewrite <- (dtp_mbinddt_mret W S T).
    rewrite mbinddt_to_runBatch.
    reflexivity.
  Qed.

End iterate.

(** ** Respectfulness for <<mbindd>> *)
(******************************************************************************)
Section mbindd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Theorem mbindd_respectful :
    forall A B (t : S A) (f g : forall k, W * A -> T k B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k (w, a))
      -> mbindd S f t = mbindd S g t.
  Proof.
    introv hyp.
    rewrite (tomsetd_to_runBatch S B t) in hyp.
    do 2 rewrite (mbindd_to_runBatch S).
    induction (iterate S B t).
    - easy.
    - destruct p. do 2 rewrite runBatch_rw2.
      rewrite runBatch_rw2 in hyp.
      fequal.
      + apply IHb. intros. apply hyp.
        cbn. now left.
      + apply hyp. now right.
  Qed.

  (** *** For equalities with special cases *)
  (** Corollaries with conclusions of the form <<mbindd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mbindd_respectful_mbind :
    forall A B (t : S A) (f : forall k, W * A -> T k B) (g : forall k, A -> T k B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k a)
      -> mbindd S f t = mbind S g t.
  Proof.
    introv hyp. rewrite mbind_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_mfmapd :
    forall A B (t : S A) (f : forall k, W * A -> T k B) (g : K -> W * A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k (g k (w, a)))
      -> mbindd S f t = mfmapd S g t.
  Proof.
    introv hyp. rewrite mfmapd_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_mfmap :
    forall A B (t : S A) (f : forall k, W * A -> T k B) (g : K -> A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k (g k a))
      -> mbindd S f t = mfmap S g t.
  Proof.
    introv hyp. rewrite mfmap_to_mbindd.
    apply mbindd_respectful. introv Hin.
    unfold compose. cbn. auto.
  Qed.

  Corollary mbindd_respectful_id :
    forall A (t : S A) (f : forall k, W * A -> T k A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = mret T k a)
      -> mbindd S f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mbindd_id S).
    eapply mbindd_respectful.
    unfold compose; cbn. auto.
  Qed.

End mbindd_respectful.

(** ** Respectfulness for <<mbindd>> *)
(******************************************************************************)
Section mbind_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mbind_respectful :
    forall A B (t : S A) (f g : forall k, A -> T k B),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = g k a)
      -> mbind S f t = mbind S g t.
  Proof.
    introv hyp. rewrite mbind_to_mbindd.
    apply mbindd_respectful. introv premise. apply ind_implies_in in premise.
    unfold compose; cbn. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mbind t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mbind_respectful_mfmapd :
    forall A B (t : S A) (f : forall k, A -> T k B) (g : K -> W * A -> B),
      (forall (k : K) (w : W) (a : A), (w, (k, a)) ∈md t -> f k a = mret T k (g k (w, a)))
      -> mbind S f t = mfmapd S g t.
  Proof.
    intros. rewrite mfmapd_to_mbindd.
    symmetry. apply mbindd_respectful_mbind.
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary mbind_respectful_mfmap :
    forall A B (t : S A) (f : forall k, A -> T k B) (g : K -> A -> B),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = mret T k (g k a))
      -> mbind S f t = mfmap S g t.
  Proof.
    intros. rewrite mfmap_to_mbind.
    symmetry. apply mbind_respectful.
    introv Hin. symmetry. unfold compose; cbn.
    auto.
  Qed.

  Corollary mbind_respectful_id : forall A (t : S A) (f : forall k, A -> T k A),
      (forall (k : K) (a : A), (k, a) ∈m t -> f k a = mret T k a)
      -> mbind S f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mbind_id S).
    eapply mbind_respectful.
    unfold compose; cbn. auto.
  Qed.

End mbind_respectful.

(** ** Respectfulness for <<mfmapd>> *)
(******************************************************************************)
Section mfmapd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mfmapd_respectful :
    forall A B (t : S A) (f g : K -> W * A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k (w, a))
      -> mfmapd S f t = mfmapd S g t.
  Proof.
    introv hyp. do 2 rewrite mfmapd_to_mbindd.
    apply mbindd_respectful. introv premise.
    unfold compose; cbn. fequal. auto.
  Qed.

  (** *** For equalities with other operations *)
  (** Corollaries with conclusions of the form <<mfmapd t = f t>> for
  other <<m*>> operations *)
  (******************************************************************************)
  Corollary mfmapd_respectful_mfmap :
    forall A (t : S A) (f : K -> W * A -> A) (g : K -> A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = g k a)
      -> mfmapd S f t = mfmap S g t.
  Proof.
    intros. rewrite mfmap_to_mfmapd.
    apply mfmapd_respectful. introv Hin.
    unfold compose; cbn; auto.
  Qed.

  Corollary mfmapd_respectful_id : forall A (t : S A) (f : K -> W * A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k (w, a) = a)
      -> mfmapd S f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mfmapd_id S).
    eapply mfmapd_respectful.
    cbn. auto.
  Qed.

End mfmapd_respectful.

(** ** Respectfulness for <<mfmap>> *)
(******************************************************************************)
Section mfmap_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma mfmap_respectful :
    forall A B (t : S A) (f g : K -> A -> B),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k a = g k a)
      -> mfmap S f t = mfmap S g t.
  Proof.
    introv hyp. do 2 rewrite mfmap_to_mfmapd.
    now apply mfmapd_respectful.
  Qed.

  Corollary mfmap_respectful_id :
    forall A (t : S A) (f : K -> A -> A),
      (forall (w : W) (k : K) (a : A), (w, (k, a)) ∈md t -> f k a = a)
      -> mfmap S f t = t.
  Proof.
    intros. change t with (id t) at 2.
    rewrite <- (mfmap_id S).
    eapply mfmap_respectful.
    auto.
  Qed.

End mfmap_respectful.

(** ** Respectfulness for <<kbindd>> *)
(******************************************************************************)
Section kbindd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Lemma kbindd_respectful :
    forall A (t : S A) (f g : W * A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g (w, a))
      -> kbindd S j f t = kbindd S j g t.
  Proof.
    introv hyp. unfold kbindd. apply mbindd_respectful.
    introv premise. compare values j and k.
    - do 2 rewrite btgd_eq. auto.
    - do 2 (rewrite btgd_neq; auto).
  Qed.

  (** *** For equalities with special cases *)
  (******************************************************************************)
  Corollary kbindd_respectful_kbind :
    forall A (t : S A) (f : W * A -> T j A) (g : A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g a)
      -> kbindd S j f t = kbind S j g t.
  Proof.
    introv hyp. rewrite kbind_to_kbindd.
    apply kbindd_respectful. introv Hin.
    apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_kfmapd :
    forall A (t : S A) (f : W * A -> T j A) (g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j (g (w, a)))
      -> kbindd S j f t = kfmapd S j g t.
  Proof.
    introv hyp. rewrite kfmapd_to_kbindd.
    apply kbindd_respectful. introv Hin.
    apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_kfmap :
    forall A (t : S A) (f : W * A -> T j A) (g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j (g a))
      -> kbindd S j f t = kfmap S j g t.
  Proof.
    introv hyp. rewrite kfmap_to_kfmapd.
    apply kbindd_respectful_kfmapd.
    introv Hin. apply hyp. auto.
  Qed.

  Corollary kbindd_respectful_id :
    forall A (t : S A) (f : W * A -> T j A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = mret T j a)
      -> kbindd S j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    erewrite <- (kbindd_id S).
    apply kbindd_respectful.
    auto.
  Qed.

End kbindd_respectful.

(** ** Respectfulness for mixed structures *)
(******************************************************************************)
Section mixed_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Corollary kbind_respectful_kfmapd :
    forall A (t : S A) (f : A -> T j A) (g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = mret T j (g (w, a)))
      -> kbind S j f t = kfmapd S j g t.
  Proof.
    introv hyp. rewrite kfmapd_to_kbindd.
    rewrite kbind_to_kbindd. apply kbindd_respectful.
    introv Hin. apply hyp. auto.
  Qed.

End mixed_respectful.

(** ** Respectfulness for <<kbind>> *)
(******************************************************************************)
Section kbindd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Lemma kbind_respectful :
    forall A (t : S A) (f g : A -> T j A),
      (forall (a : A), (j, a) ∈m t -> f a = g a)
      -> kbind S j f t = kbind S j g t.
  Proof.
    introv hyp. unfold kbind. apply mbind_respectful.
    introv premise. compare values j and k.
    - do 2 rewrite btg_eq. auto.
    - do 2 (rewrite btg_neq; auto).
  Qed.

  (** *** For equalities with special cases *)
  (******************************************************************************)
  Corollary kbind_respectful_kfmap :
    forall A (t : S A) (f : A -> T j A) (g : A -> A),
      (forall (a : A), (j, a) ∈m t -> f a = mret T j (g a))
      -> kbind S j f t = kfmap S j g t.
  Proof.
    introv hyp. rewrite kfmap_to_kbind.
    apply kbind_respectful.
    introv Hin. apply hyp. auto.
  Qed.

  Corollary kbind_respectful_id :
    forall A (t : S A) (f : A -> T j A),
      (forall (a : A), (j, a) ∈m t -> f a = mret T j a)
      -> kbind S j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kbind_id S (j := j)).
    now apply kbind_respectful.
  Qed.

End kbindd_respectful.

(** ** Respectfulness for <<kfmapd>> *)
(******************************************************************************)
Section kfmapd_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Lemma kfmapd_respectful :
    forall A (t : S A) (f g : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g (w, a))
      -> kfmapd S j f t = kfmapd S j g t.
  Proof.
    introv hyp. unfold kfmapd.
    apply mfmapd_respectful. introv premise.
    compare values j and k.
    - do 2 rewrite tgtd_eq. auto.
    - do 2 (rewrite tgtd_neq; auto).
  Qed.

  (** *** For equalities with other operations *)
  (******************************************************************************)
  Corollary kfmapd_respectful_kfmap :
    forall A (t : S A) (f : W * A -> A) (g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = g a)
      -> kfmapd S j f t = kfmap S j g t.
  Proof.
    introv hyp. rewrite kfmap_to_kfmapd.
    apply kfmapd_respectful. auto.
  Qed.

  Corollary kfmapd_respectful_id : forall A (t : S A) (f : W * A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f (w, a) = a)
      -> kfmapd S j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kfmapd_id (j := j) S).
    apply kfmapd_respectful. auto.
  Qed.

End kfmapd_respectful.

(** ** Respectfulness for <<kfmap>> *)
(******************************************************************************)
Section kfmap_respectful.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T} (j : K).

  Lemma kfmap_respectful :
    forall A (t : S A) (f g : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = g a)
      -> kfmap S j f t = kfmap S j g t.
  Proof.
    introv hyp. unfold kfmap. apply mfmap_respectful.
    introv premise. compare values j and k.
    - autorewrite with tea_tgt. eauto.
    - autorewrite with tea_tgt_neq. auto.
  Qed.

  Corollary kfmap_respectful_id :
    forall A (t : S A) (f : A -> A),
      (forall (w : W) (a : A), (w, (j, a)) ∈md t -> f a = a)
      -> kfmap S j f t = t.
  Proof.
    introv hyp. change t with (id t) at 2.
    rewrite <- (kfmap_id (j := j) S).
    apply kfmap_respectful. auto.
  Qed.

End kfmap_respectful.
