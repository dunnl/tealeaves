From Tealeaves Require Export
  Classes.Kleisli.DecoratedTraversableMonad
  Functors.List_Telescoping_General
  Functors.List.

Import Product.Notations.
Import Monad.Notations.
Import Monoid.Notations.
Import Comonad.Notations.
Import DecoratedTraversableMonad.Notations.

(** * Polymorphically Decorated Monads *)
(******************************************************************************)
Section DecoratedMonadPoly.

  (** ** Operations <<binddp>> *)
  (******************************************************************************)
  Class BinddP
    (T : Type -> Type -> Type) :=
    binddp :
      forall (B1 B2 V1 V2: Type),
        (list B1 * B1 -> B2) ->
        (list B1 * V1 -> T B2 V2) ->
        T B1 V1 -> T B2 V2.

  (** ** Axioms *)
  (******************************************************************************)
  Section axioms.

    Context (T: Type -> Type -> Type).
    Context (B1 B2: Type) (V1 V2: Type).
    Context (ρ : list B1 * B1 -> B2).
    Context (σ : list B1 * V1 -> T B2 V2).
    Context (BinddP_T: BinddP T).
    Context (RetP_T: forall B, Return (T B)).

    Definition binddP_axiom1 :=
      @binddp T _ B1 B1 V1 V1
        (extract (W := ((list B1) ×)))
        (* discard context on binders *)
        (@ret (T B1) _ V1 ∘ extract (W := ((list B1) ×)))
      (* discard context on leaves and coerce to subterms *)
      = @id (T B1 V1).

    Definition binddP_axiom2 := forall (v: V1),
        @binddp T _ B1 B2 V1 V2 ρ σ (ret (T := T B1) v) = σ (nil, v).


    Context (B3 V3: Type).
    Context (ρ2 : list B2 * B2 -> B3).
    Context (σ2 : list B2 * V2 -> T B3 V3).

    Definition kc_dmp:
      list B1 * V1 -> T B3 V3 :=
      fun '(ctx, v) =>
        let ctx2 := mapd_list_prefix ρ ctx
        in binddp _ _ _ _ (ρ2 ⦿ ctx2) (σ2 ⦿ ctx2) (σ (ctx, v)).

  End axioms.

End DecoratedMonadPoly.

#[global] Arguments binddp {T}%function_scope {BinddP} {B1 B2 V1 V2}%type_scope (_ _)%function_scope _.

#[global] Arguments kc_dmp {T}%function_scope {B1 B2 V1 V2}%type_scope (ρ σ)%function_scope {BinddP_T}
  {B3 V3}%type_scope  (ρ2 σ2)%function_scope _.

(** ** Typeclass *)
(******************************************************************************)
Class DecoratedMonadPoly
    (T: Type -> Type -> Type)
    `{forall W, Return (T W)}
    `{BinddP T} :=
  { kdmp_binddp0:
    forall {B1 B2 V1 V2: Type}
      (ρ: list B1 * B1 -> B2)
      (σ: list B1 * V1 -> T B2 V2),
      binddp ρ σ ∘ ret (T := T B1) = σ ∘ ret (T := ((list B1)×));
    kdmp_binddp1:
    forall {B V: Type},
      binddp
        (extract (W := (list B ×)))
        (ret (T := T B) ∘ extract (W := (list B ×)))
      = @id (T B V);
    kdmp_binddp2:
    forall {B1 B2 B3: Type}
      {V1 V2 V3: Type}
      (ρ1: list B1 * B1 -> B2)
      (ρ2: list B2 * B2 -> B3)
      (σ1: list B1 * V1 -> T B2 V2)
      (σ2: list B2 * V2 -> T B3 V3),
      binddp ρ2 σ2 ∘ binddp (T := T) ρ1 σ1 =
        binddp (T := T) (ρ2 ∘ cobind (W := Z) ρ1) (kc_dmp ρ1 σ1 ρ2 σ2);
  }.

