From Tealeaves Require Import
     Util.Product
     Classes.Monoid
     Classes.Functor
     Functors.Writer.

From Tealeaves.Multisorted Require Export
     Theory.Category.

Import Multisorted.Theory.Category.Notations.
Import Product.Notations.
Import Monoid.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.

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
      mbinddt : forall (F : Type -> Type) `{Fmap F} `{Pure F} `{Mult F} {A B : Type},
        (forall (k : K), W * A -> F (T k B)) -> S A -> F (S B).

  End operations.

  (** ** Definition of Kleisli composition *)
  (******************************************************************************)
  Definition compose_dtm
             {W : Type}
             {T : K -> Type -> Type}
             `{mn_op : Monoid_op W}
             `{mn_unit : Monoid_unit W}
             `{Fmap F} `{Mult F} `{Pure F}
             `{Fmap G} `{Mult G} `{Pure G}
             `{forall k, MBind W T (T k)}
             {A B C : Type}
             (g : forall k, W * B -> G (T k C))
             (f : forall k, W * A -> F (T k B)) : forall k, W * A -> F (G (T k C)) :=
    fun (k : K) '(w, a) => fmap F (mbinddt W T (T k) G (g ◻ const (incr w))) (f k (w, a)).

  Infix "⋆dtm" := compose_dtm (at level 40) : tealeaves_scope.

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
            mbinddt W T S (fun a => a) (mret T A ◻ const (extract (W ×))) = @id (S A);
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
      `{Fmap F} `{Mult F} `{Pure F}.

    Definition mbindd (f : forall k, W * A -> T k B) : S A -> S B :=
      mbinddt S (fun x => x) f.

    Definition mfmapdt (f : forall k, W * A -> F B) : S A -> F (S B) :=
      mbinddt S F (fun k => fmap F (mret T k) ∘ f k).

    Definition mbindt (f : forall k, A -> F (T k B)) : S A -> F (S B) :=
      mbinddt S F (f ◻ const (extract (W ×))).

    Definition mbind (f : forall k, A -> T k B) : S A -> S B :=
      mbindd (f ◻ const (extract (W ×))).

    Definition mfmapd (f : forall k, W * A -> B) : S A -> S B :=
      mbindd (fun k => mret T k ∘ f k).

    Definition mfmapt (f : forall k, A -> F B) : S A -> F (S B) :=
      mbindt (fun k => fmap F (mret T k) ∘ f k).

    Definition mfmap (f : forall k, A -> B) : S A -> S B :=
      mfmapd (f ◻ const (extract (W ×))).

  End definitions.

  Section special_cases.

    Context
      {A B : Type}
      (F : Type -> Type)
      `{Fmap F} `{Mult F} `{Pure F}.

    (** *** Rewriting rules for special cases of <<mbinddt>> *)
    (******************************************************************************)
    Lemma mbindt_to_mbinddt (f : forall k, A -> F (T k B)):
        mbindt F f = mbinddt S F (f ◻ const (extract (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma mbindd_to_mbinddt (f : forall k, W * A -> T k B):
        mbindd f = mbinddt S (fun A => A) f.
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapdt_to_mbinddt (f : K -> W * A -> F B):
        mfmapdt F f = mbinddt S F (fun k => fmap F (mret T k) ∘ f k).
    Proof.
      reflexivity.
    Qed.

    Lemma mbind_to_mbinddt (f : forall k, A -> T k B):
        mbind f = mbinddt S (fun A => A) (f ◻ const (extract (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapd_to_mbinddt (f : K -> W * A -> B):
        mfmapd f = mbinddt S (fun A => A) (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapt_to_mbinddt (f : K -> A -> F B):
      mfmapt F f = mbinddt S F (fun k => fmap F (mret T k) ∘ f k ∘ extract (W ×)).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmap_to_mbinddt (f : K -> A -> B):
      mfmap f = mbinddt S (fun A => A) (mret T ◻ f ◻ const (extract (W ×))).
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
      mfmapt F f = mbindt F (fun k => fmap F (mret T k) ∘ f k).
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
      mbind f = mbindd (f ◻ const (extract (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapd_to_mbindd (f : W * A -k-> B):
      mfmapd f = mbindd (mret T ◻ f).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmap_to_mbindd (f : A -k-> B):
      mfmap f = mbindd (mret T ◻ f ◻ const (extract (W ×))).
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
      mfmap f = mfmapdt (fun A => A) (f ◻ const (extract (W ×))).
    Proof.
      reflexivity.
    Qed.

    Lemma mfmapt_to_mfmapdt (f : K -> A -> F B):
      mfmapt F f = mfmapdt F (f ◻ const (extract (W ×))).
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
      mfmap f = mfmapd (f ◻ const (extract (W ×))).
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
      fmap F (mbindd S g) ∘ mbinddt S F f =
      mbinddt S F (fun k '(w, a) => fmap F (mbindd (T k) (g ◻ const (incr w))) (f k (w, a))).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F (fun A => A)).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma mfmapdt_mbinddt: forall
      (g : K -> W * B -> G C)
      (f : forall k, W * A -> F (T k B)),
      fmap F (mfmapdt S G g) ∘ mbinddt S F f =
      mbinddt S (F ∘ G) (fun k '(w, a) => fmap F (mfmapdt (T k) G (g ◻ const (incr w))) (f k (w, a))).
  Proof.
    intros. rewrite mfmapdt_to_mbinddt.
    now rewrite (dtp_mbinddt_mbinddt W S T F G).
  Qed.

  Lemma mbindt_mbinddt: forall
      (g : forall k, B -> G (T k C))
      (f : forall k, W * A -> F (T k B)),
      fmap F (mbindt S G g) ∘ mbinddt S F f =
      mbinddt S (F ∘ G) (fun k => fmap F (mbindt (T k) G g) ∘ f k).
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
      fmap F (mbind S g) ∘ mbinddt S F f =
      mbinddt S F (fun k => fmap F (mbind (T k) g) ∘ f k).
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
      fmap F (mfmapd S g) ∘ mbinddt S F f =
      mbinddt S F (fun k '(w, a) => fmap F (mfmapd (T k) (g ◻ const (incr w))) (f k (w, a))).
  Proof.
    intros. rewrite mfmapd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F (fun A => A)).
    fequal. now rewrite Mult_compose_identity1.
  Qed.

  Lemma mfmapt_mbinddt: forall
      (g : K -> B -> G C)
      (f : forall k, W * A -> F (T k B)),
      fmap F (mfmapt S G g) ∘ mbinddt S F f =
      mbinddt S (F ∘ G) (fun k => fmap F (mfmapt (T k) G g) ∘ f k).
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
      fmap F (mfmap S g) ∘ mbinddt S F f =
      mbinddt S F (fun k => fmap F (mfmap (T k) g) ∘ f k).
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
      mbinddt S G (fun k '(w, a) => mbinddt (T k) G (g ◻ const (incr w)) (f k (w, a))).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    change (mbinddt S G g) with (fmap (fun A => A) (mbinddt S G g)).
    rewrite (dtp_mbinddt_mbinddt W S T (fun A => A) G).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma mbinddt_mfmapdt: forall
      (g : forall k, W * B -> G (T k C))
      (f : K -> W * A -> F B),
      fmap F (mbinddt S G g) ∘ mfmapdt S F f =
      mbinddt S (F ∘ G) (fun k '(w, a) => fmap F (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros. rewrite mfmapdt_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F G).
    fequal. ext k [w a]. unfold compose; cbn.
    compose near (f k (w, a)) on left.
    rewrite (fun_fmap_fmap F).
    fequal. ext b. unfold compose; cbn.
    compose near b on left.
    rewrite (dtm_mbinddt_comp_mret W T k G).
    cbn. now simpl_monoid.
  Qed.

  Lemma mbinddt_mbindt: forall
      (g : forall k, W * B -> G (T k C))
      (f : forall k, A -> F (T k B)),
      fmap F (mbinddt S G g) ∘ mbindt S F f =
      mbinddt S (F ∘ G) (fun k '(w, a) => fmap F (mbinddt (T k) G (g ◻ const (incr w))) (f k a)).
  Proof.
    intros. rewrite mbindt_to_mbinddt.
    now rewrite (dtp_mbinddt_mbinddt W S T F G).
  Qed.

  Lemma mbinddt_mbind: forall
      (g : forall k, W * B -> G (T k C))
      (f : forall k, A -> T k B),
      mbinddt S G g ∘ mbind S f =
      mbinddt S G (fun k '(w, a) => mbinddt (T k) G (g ◻ const (incr w)) (f k a)).
  Proof.
    intros. rewrite mbind_to_mbinddt.
    change (mbinddt S G g) with (fmap (fun A => A) (mbinddt S G g)).
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
    change (mbinddt S G g) with (fmap (fun A => A) (mbinddt S G g)).
    rewrite (dtp_mbinddt_mbinddt W S T (fun A => A) G).
    fequal. now rewrite Mult_compose_identity2.
    ext j [w2 b]. unfold compose; cbn.
    unfold_ops @Fmap_I. compose near (f j (w2, b)).
    rewrite (dtm_mbinddt_comp_mret W T j G).
    unfold compose; cbn.
    now simpl_monoid.
  Qed.

  Lemma mbinddt_mfmapt: forall
      (g : forall k, W * B -> G (T k C))
      (f : K -> A -> F B),
      fmap F (mbinddt S G g) ∘ mfmapt S F f =
      mbinddt S (F ∘ G) (fun k '(w, a) => fmap F (fun b => g k (w, b)) (f k a)).
  Proof.
    intros. unfold mfmapt. rewrite mbinddt_mbindt.
    fequal. ext k [w a]. unfold compose. compose near (f k a) on left.
    rewrite (fun_fmap_fmap F). fequal.
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
      mbinddt S F (fun k => pure F ∘ mret T k ∘ extract (W ×)) = pure F (A := S A).
  Proof.
    intros. replace (fun (k : K) => pure F ∘ mret T k ∘ extract (W ×))
              with (fun (k : K) => pure F ∘ (mret T k ∘ extract (W ×) (A := A))).
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
      fmap F (mbindd S g) ∘ mfmapdt S F f =
      mbinddt S F (fun (k : K) '(w, a) => fmap F (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros. rewrite mfmapdt_to_mbinddt.
    rewrite mbindd_to_mbinddt.
    rewrite (dtp_mbinddt_mbinddt W S T F (fun x => x)).
    fequal.
    - now rewrite Mult_compose_identity1.
    - ext k [w a]. unfold compose; cbn.
      compose near (f k (w, a)) on left.
      rewrite (fun_fmap_fmap F). fequal.
      rewrite (dtm_mbinddt_comp_mret W T k (fun A =>A)).
      ext b. unfold compose; cbn. now simpl_monoid.
  Qed.

  Lemma mbindd_mbindt: forall
      (g : forall k, W * B -> T k C)
      (f : forall k, A -> F (T k B)),
      fmap F (mbindd S g) ∘ mbindt S F f =
      mbinddt S F (fun (k : K) '(w, a) => fmap F (mbindd (T k) (g ◻ const (incr w))) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  Lemma mbindd_mfmapt: forall
      (g : forall k, W * B -> T k C)
      (f : forall k, A -> F B),
      fmap F (mbindd S g) ∘ mfmapt S F f =
      mbinddt S F (fun (k : K) '(w, a) => fmap F (fun b => g k (w, b)) (f k a)).
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
      mbinddt S G (fun (k : K) '(w, a) => mfmapdt (T k) G (g ◻ const (incr w)) (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  Lemma mfmapdt_mbindt: forall
      (g : forall k, W * B -> G C)
      (f : forall k, A -> F (T k B)),
      fmap F (mfmapdt S G g) ∘ mbindt S F f =
      mbinddt S (F ∘ G) (fun (k : K) '(w, a) => fmap F (mfmapdt (T k) G (g ◻ const (incr w))) (f k a)).
  Proof.
    (* TODO *)
  Abort.

  Lemma mfmapdt_mbind: forall
      (g : K -> W * B -> G C) (f : forall k, A -> T k B),
      mfmapdt S G g ∘ mbind S f = mbinddt S G (fun k '(w, a) => mfmapdt (T k) G (g ◻ const (incr w)) (f k a)).
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
      fmap F (mbindt S G g) ∘ mfmapdt S F f =
      mbinddt S (F ∘ G) (fun (k : K) '(w, a) => fmap F (g k) (f k (w, a))).
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
  fun k '(w, a) => mbindd (T k) (g ◻ const (incr w)) (f k (w, a)).

Infix "⋆dm" := compose_dm (at level 40).

Section DecoratedMonad.

  Context
    (S : Type -> Type)
    `{DTPreModule W S T}
    `{! DTM W T} {A B C : Type}.

  (** *** Composition and identity law *)
  (******************************************************************************)
  Theorem mbindd_id:
    mbindd S (mret T ◻ const (extract (W ×))) = @id (S A).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    now rewrite <- (dtp_mbinddt_mret W S T).
  Qed.

  Theorem mbindd_mbindd: forall
      (g : W * B ~k~> T C)
      (f : W * A ~k~> T B),
      mbindd S g ∘ mbindd S f =
      mbindd S (fun (k : K) '(w, a) => mbindd (T k) (g ◻ const (incr w)) (f k (w, a))).
  Proof.
    intros. rewrite mbindd_to_mbinddt.
    change_left (fmap (fun x => x) (mbinddt S (fun x : Type => x) g) ∘ (mbinddt S (fun x : Type => x) f)).
    rewrite (dtp_mbinddt_mbinddt W S T (fun x => x) (fun x => x)).
    ext t.
    change (compose_dtm g f) with
        (fun (k : K) '(w, a) => mbinddt (T k) (fun x : Type => x) (g ◻ const (incr w)) (f k (w, a))).
    fequal. now rewrite Mult_compose_identity2.
  Qed.

  (** *** Right unit law for monads *)
  (******************************************************************************)
  Theorem mbindd_comp_mret: forall
      (k : K) (f : forall k, W * A -> T k B),
      mbindd (T k) f ∘ mret T k = f k ∘ ret (W ×).
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
      mbindd S (fun (k : K) '(w, a) => mbindd (T k) (g ◻ const (incr w)) (f k a)).
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
      mbindd S (fun (k : K) '(w, a) => mfmapd (T k) (g ◻ const (incr w)) (f k (w, a))).
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
    mfmapdt S (fun x => x) (const (extract (W ×))) = @id (S A).
  Proof.
    intros. unfold mfmapdt. apply (dtp_mbinddt_mret W S T).
  Qed.

  Theorem mfmapdt_mfmapdt: forall
    (g : forall k, W * B -> G C) (f : forall k, W * A -> F B),
    fmap F (mfmapdt S G g) ∘ mfmapdt S F f =
    mfmapdt S (F ∘ G) (fun (k : K) '(w, a) => fmap F (fun b => g k (w, b)) (f k (w, a))).
  Proof.
    intros. unfold mfmapdt. rewrite (dtp_mbinddt_mbinddt W S T F G).
    unfold compose_dtm. fequal. ext k [w a].
    unfold_ops @Fmap_compose.  unfold compose.
    compose near (f k (w, a)).
    do 2 rewrite (fun_fmap_fmap F). rewrite (dtm_mbinddt_comp_mret W T k G).
    fequal. ext b. cbn. now simpl_monoid.
  Qed.

  (** *** Composition with <<mret>> *)
  (******************************************************************************)
  Lemma mfmapdt_comp_mret: forall
      (k : K) (f : forall k, W * A -> F B),
      mfmapdt (T k) F f ∘ mret T k = fmap F (mret T k) ∘ f k ∘ pair Ƶ.
  Proof.
    intros. unfold mfmapdt.
    now rewrite (dtm_mbinddt_comp_mret W T k F).
  Qed.

  (** *** Purity *)
  (******************************************************************************)
  Lemma mfmapdt_pure:
      mfmapdt S F (fun k => pure F ∘ extract (W ×)) = pure F (A := S A).
  Proof.
    intros. unfold mfmapdt.
    replace (fun k : K => fmap F (mret T k) ∘ (pure F ∘ extract (prod W)))
      with (fun (k : K) => (pure F ∘ (mret T k ∘ extract (W ×) (A := A)))).
    rewrite <- (dtp_mbinddt_morphism W S T (fun x => x) F (ϕ := @pure F _)).
    now rewrite (dtp_mbinddt_mret W S T).
    ext k [w a]. unfold compose; cbn.
    now rewrite (app_pure_natural F).
  Qed.

  (** *** Composition with special cases  on the right *)
  (******************************************************************************)
  Lemma mfmapdt_mfmapt: forall
      (g : K -> W * B -> G C) (f : K -> A -> F B),
      fmap F (mfmapdt S G g) ∘ mfmapt S F f =
      mfmapdt S (F ∘ G) (fun (k : K) '(w, a) => fmap F (fun b => g k (w, b)) (f k a)).
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
      fmap F (mfmapd S g) ∘ mfmapdt S F f =
      mfmapdt S F (fun k '(w, a) => fmap F (fun (b : B) => (g k (w, b))) (f k (w, a))).
  Proof.
    (* TODO *)
  Abort.

  Lemma mfmapt_mfmapdt: forall
      (g : K -> B -> C) (f : K -> W * A -> F B),
      fmap F (mfmap S g) ∘ mfmapdt S F f = mfmapdt S F (fun k => fmap F (g k) ∘ f k).
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
      fmap F (mbindt S G g) ∘ mbindt S F f =
      mbindt S (F ∘ G) (fun (k : K) (a : A) => fmap F (mbindt (T k) G g) (f k a)).
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
      fmap F (mbind S g) ∘ mfmapt S F f =
      mbindt S F (fun k => fmap F (g k) ∘ f k).
  Proof.
    intros. rewrite (mfmapt_to_mbindt S F).
    rewrite mbind_to_mbindt.
    rewrite (mbindt_mbindt S F (fun A => A)).
    fequal.
    - now rewrite Mult_compose_identity1.
    - ext k a. unfold compose. compose near (f k a) on left.
      rewrite (fun_fmap_fmap F). fequal.
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
      mbindd S (fun k '(w, a) => mfmapd (T k) (g ◻ const (incr w)) (f k a)).
  Proof.
    intros. rewrite mfmapd_to_mbindd. rewrite mbind_to_mbindd.
    now rewrite (mbindd_mbindd S).
  Qed.

  Lemma mfmapd_mfmapt :
    forall (g : K -> W * B -> C)
      (f : forall k, A -> F B),
      fmap F (mfmapd S g) ∘ mfmapt S F f =
      mfmapdt S F (fun k '(w, a) => fmap F (fun b => g k (w, b)) (f k a)).
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
    change (mbindt S G (fun k : K => fmap G (mret T k) ∘ g k))
      with (fmap (fun A => A) (mbindt S G (fun k : K => fmap G (mret T k) ∘ g k))).
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
    change (mbindt S G (fun k : K => fmap G (mret T k) ∘ g k))
      with (fmap (fun A => A) (mbindt S G (fun k : K => fmap G (mret T k) ∘ g k))).
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
      fmap F (mfmapt S G g) ∘ mfmapt S F f =
      mfmapt S (F ∘ G) (fun (k : K) (a : A) => fmap F (g k) (f k a)).
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
      mfmapt (T k) F f (mret T k a) = fmap F (mret T k) (f k a).
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
      kbind f = kbindd (f ∘ extract (W ×)).
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
      kfmap f = kbindd (mret T j ∘ f ∘ extract (W ×)).
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
      kfmap f = kfmapd (f ∘ extract (W ×)).
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
  fun '(w, a) => kbindd (T j) j (g ∘ incr w) (f (w, a)).

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
    kbindd S j (mret T j ∘ (extract (W ×))) = @id (S A).
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
      kfmapd S j g ∘ kbindd S j f = kbindd S j (fun '(w, a) => kfmapd (T j) j (g ∘ incr w) (f (w, a))).
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
      kbindd S j g ∘ kbind S j f = kbindd S j (fun '(w, a) => kbindd (T j) j (g ∘ incr w) (f a)).
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
