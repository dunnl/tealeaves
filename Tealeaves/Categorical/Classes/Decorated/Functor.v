(** This file implements "functors decorated by type <<E>>" and
    proves their basic properties.  *)

From Tealeaves Require Export
  Categorical.Classes.Comonad
  Functors.Environment
  Functors.Writer.

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
        map F (extract (E ×)) ∘ dec E F A = @id (F A);
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

From Tealeaves.Classes Require Import RightComodule.

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
      map F (extract (prod W)) (dec F t) = t ->
      map F (extract (prod W)) (shift F (w, dec F t)) = t.
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
