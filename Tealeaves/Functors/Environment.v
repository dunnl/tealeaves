From Tealeaves Require Import
  Data.Product
  Data.Strength
  Classes.Comonoid
  Classes.Comonad.

Import Product.Notations.
Import Strength.Notations.

(** * Product functor *)
(** For any type [A], there is an endofunctor whose object map is
    <<fun B => prod A B>>. *)
(******************************************************************************)
#[export] Instance Fmap_prod {E} : Fmap (E ×) := (fun A B => map_snd).

#[program, export] Instance Functor_prod E : Functor (E ×).

Solve All Obligations with (introv; now ext [? ?]).


(** * Environment comonad (a/k/a "Reader" or "co-Reader") *)
(** The properties of Cartesian products imply the product functor (by
    any type <<E>>) forms a comonad. This comonad is sometimes called
    "Reader" in the Haskell community (or sometimes "co-Reader")
    because it is the comonad formed by taking the so-called Reader
    monad across the product/exponent adjunction. It is also sometimes
    called the Writer comonad because it shares the same underlying
    object-map as the Writer monad, except here <<E>> is not required
    to be a monoid, although its semantics are a form of reading
    rather than writing.

    The extract operation is projection to the second element. The
    duplication operation makes two copies of the first element. *)
(******************************************************************************)
Lemma dup_left_spec {A B} :
    @dup_left A B  = α ∘ map_fst comonoid_comult.
Proof.
  now ext [? ?].
Qed.

Section environment_comonad_instance.

  Context
    `{W : Type}.

  #[export] Instance Cojoin_prod : Cojoin (W ×) :=
    @dup_left W.

  #[export] Instance Extract_prod : Extract (W ×) :=
    @snd W.

  #[export] Instance Natural_extract_prod : Natural (@extract (W ×) _).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [? ?].
  Qed.

  #[export] Instance Natural_cojoin_prod : Natural (@cojoin (W ×) _).
  Proof.
    constructor; try typeclasses eauto.
    introv. now ext [? ?].
  Qed.

  #[export, program] Instance Comonad_prod : Comonad (W ×).

  Solve All Obligations with (introv; now ext [? ?]).

End environment_comonad_instance.

(** * Miscellaneous properties *)
(******************************************************************************)
Section miscellaneous.

  Context
    (E : Type)
    (F : Type -> Type).

  Theorem strength_extract `{Functor F} {A : Type} :
    `(fmap F (extract (E ×)) ∘ σ F = extract (E ×) (A := F A)).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite (fun_fmap_fmap F), (fun_fmap_id F).
  Qed.

  Theorem strength_cojoin `{Functor F} {A : Type} :
    `(fmap F (cojoin (E ×)) ∘ σ F = σ F ∘ cobind (E ×) (σ F) (A := F A)).
  Proof.
    intros. unfold strength, compose. ext [w a]. cbn.
    compose_near a. now rewrite 2(fun_fmap_fmap F).
  Qed.

  Theorem product_fmap_commute {E1 E2 A B : Type} (g : E1 -> E2) (f : A -> B) :
    fmap (E2 ×) f ∘ map_fst g = map_fst g ∘ fmap (E1 ×) f.
  Proof.
    now ext [w a].
  Qed.

End miscellaneous.
