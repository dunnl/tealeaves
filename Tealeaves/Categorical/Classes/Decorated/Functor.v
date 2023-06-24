(** This file implements "functors decorated by type <<E>>" and
    proves their basic properties.  *)

From Tealeaves Require Export
  Categorical.Classes.Comonad
  Categorical.Functors.Environment
  Categorical.Functors.Writer
  Definitions.Shift.

Import Product.Notations.
Import Functor.Notations.

#[local] Generalizable Variables E A.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.

(** * Decorated functors *)
(******************************************************************************)
Section DecoratedFunctor_operations.

  Context
    (E : Type)
    (F : Type -> Type).

  Class Decorate :=
    dec : F ⇒ F ○ (E ×).

End DecoratedFunctor_operations.

Section DecoratedFunctor.

  Context
    (E : Type)
    (F : Type -> Type)
    `{Map F}
    `{Decorate E F}.

  Class DecoratedFunctor :=
    { dfun_functor :> Functor F;
      dfun_dec_natural :> Natural (@dec E F _);
      dfun_dec_dec : forall (A : Type),
        dec E F (E * A) ∘ dec E F A = map F (cojoin (prod E)) ∘ dec E F A;
      dfun_dec_extract : forall (A : Type),
        map F (extract (E ×) A) ∘ dec E F A = @id (F A);
    }.

End DecoratedFunctor.

(* Mark <<E>> and the type argument implicit *)
Arguments dec {E}%type_scope _%function_scope {Decorate} {A}%type_scope _.

(** ** Decoration-preserving natural transformations *)
(******************************************************************************)
Class DecoratePreservingTransformation
  {F G : Type -> Type}
  `{! Map F} `{Decorate E F}
  `{! Map G} `{Decorate E G}
  (ϕ : F ⇒ G) :=
  { dectrans_commute : `(ϕ (E * A) ∘ dec F = dec G ∘ ϕ A);
    dectrans_natural : Natural ϕ;
  }.

Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables T F W.

From Tealeaves.Categorical.Classes Require Import RightComodule.

(** * Helper lemmas for proving typeclass instances *)
(** Each of the following lemmas is useful for proving one of the laws
    of decorated functors in the binder case(s) of proofs that proceed
    by induction on terms. *)
(******************************************************************************)
Section helper_lemmas.

  Context
    `{Functor F}
    `{Decorate W F}
    `{Monoid W}.

  (** This lemmasis useful for proving naturality of <<dec>>. *)
  Lemma dec_helper_1 {A B} : forall (f : A -> B) (t : F A) (w : W),
      map F (map (prod W) f) (dec F t) =
        dec F (map F f t) ->
      map F (map (prod W) f) (shift F (w, dec F t)) =
        shift F (w, dec F (map F f t)).
  Proof.
    introv IH. (* there is a hidden compose to unfold *)
    unfold compose; rewrite 2(shift_spec F).
    compose near (dec F t) on left. rewrite (fun_map_map F).
    rewrite <- IH.
    compose near (dec F t) on right. rewrite (fun_map_map F).
    fequal. now ext [w' a].
  Qed.

  (** Now we can assume that <<dec>> is a natural transformation,
      which is needed for the following. *)
  Context
    `{! Natural (@dec W F _)}.

  (** This lemmas is useful for proving the dec-extract law. *)
  Lemma dec_helper_2 {A} : forall (t : F A) (w : W),
      map F (extract (prod W) A) (dec F t) = t ->
      map F (extract (prod W) A) (shift F (w, dec F t)) = t.
  Proof.
    intros.
    compose near (w, dec F t).
    rewrite (shift_extract F). unfold compose; cbn.
    auto.
  Qed.

  (** This lemmas is useful for proving the double decoration law. *)
  Lemma dec_helper_3 {A} : forall (t : F A) (w : W),
      dec F (dec F t) = map F (cojoin (prod W)) (dec F t) ->
      shift F (w, dec F (shift F (w, dec F t))) =
        map F (cojoin (prod W)) (shift F (w, dec F t)).
  Proof.
    introv IH. unfold compose. rewrite 2(shift_spec F).
    compose near (dec F t).
    rewrite <- (natural (F := F) (G := F ○ prod W)).
    unfold compose. compose near (dec F (dec F t)).
    rewrite IH. unfold_ops @Map_compose.
    rewrite (fun_map_map F).
    compose near (dec F t).
    rewrite (fun_map_map F).
    rewrite (fun_map_map F).
    unfold compose. fequal.
    now ext [w' a].
  Qed.

End helper_lemmas.

(** * Algebraic decorated functor to Kleisli decorated functor *)
(******************************************************************************)

From Tealeaves Require Import Classes.Decorated.Functor.

(** ** Kleisli laws for <<fmapd>> *)
(******************************************************************************)
Module ToKleisli.

  Section operation.

    Context
      (E : Type)
      (F : Type -> Type)
      `{Map F} `{Decorate E F}.

    #[export] Instance Mapd_dec : Mapd E F :=
      fun A B (f : E * A -> B) => map F f ∘ dec F.

  End operation.

  Import Tealeaves.Classes.Comonad.Notations.
  Import Comonad.ToKleisli.

  Section with_functor.

    Context
      (F : Type -> Type)
      `{Categorical.Classes.Decorated.Functor.DecoratedFunctor E F}.

    Theorem mapd_id {A} : mapd E F A A (extract (E ×) A) = @id (F A).
    Proof.
      introv. unfold_ops @Mapd_dec.
      apply (dfun_dec_extract E F).
    Qed.

    Theorem mapd_mapd (A B C : Type) (g : E * B -> C) (f : E * A -> B) :
      mapd E F B C g ∘ mapd E F A B f = mapd E F A C (kc4 (H := Cobind_Cojoin (E ×)) (E ×) g f).
    Proof.
      unfold_ops @Mapd_dec.
      reassociate <- on left.
      reassociate -> near (map F f).
      rewrite <- (natural (G := F ○ prod E)).
      reassociate <- on left.
      unfold transparent tcs.
      rewrite (fun_map_map F).
      reassociate -> on left.
      rewrite (dfun_dec_dec E F).
      reassociate <- on left.
      rewrite (fun_map_map F).
      reflexivity.
    Qed.

    #[export] Instance DecoratedFunctor: Classes.Decorated.Functor.DecoratedFunctor E F (H := Mapd_dec E F) :=
      {| dfun_mapd1 := @mapd_id;
        dfun_mapd2 := @mapd_mapd
      |}.

  End with_functor.

End ToKleisli.

(*
(** * Miscellaneous properties of decorated functors *)
(******************************************************************************)
Section DecoratedFunctor_misc.

  Context
    (T : Type -> Type)
    `{DecoratedFunctor E T}.

  Theorem cobind_dec {A B} : forall (f : E * A -> B),
      map T (cobind (E ×) f) ∘ dec T = dec T ∘ map T f ∘ dec T.
  Proof.
    intros. unfold_ops @Cobind_Cojoin. rewrite <- (fun_map_map T).
    reassociate ->. rewrite <- (dfun_dec_dec E T).
    reassociate <-.
    change (map T (map (E ×) f)) with (map (T ∘ (E ×)) f).
    now rewrite (natural (ϕ := @dec E T _)).
  Qed.

End DecoratedFunctor_misc.
*)

(** * Decorated functor instance for [Environment] *)
(******************************************************************************)
Section DecoratedFunctor_Environment.

  Context
    {E : Type}.

  #[global] Instance Decorate_prod : Decorate E (prod E) := @cojoin (prod E) _.

  #[global, program] Instance DecoratedFunctor_prod : DecoratedFunctor E (prod E).

  Solve Obligations with (intros; now ext [? ?]).

End DecoratedFunctor_Environment.

From Tealeaves Require Import
  Functors.Writer.

Import Monad.Notations.
Import Strength.Notations.
Import Product.Notations.
Import Monoid.Notations.

#[local] Generalizable Variables G.
