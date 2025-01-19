From Tealeaves Require Export
  Functors.Early.Writer
  Functors.Reader
  Misc.Product
  Classes.Monoid.

#[local] Generalizable Variables W T F A M.

From Tealeaves Require Import
  Classes.Categorical.Bimonad
  Classes.Categorical.RightModule.

Import Strength.Notations.
Import Monad.Notations.
Import Monoid.Notations.
Import Product.Notations.

#[local] Arguments ret (T)%function_scope {Return} (A)%type_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments extract (W)%function_scope {Extract} (A)%type_scope _.
#[local] Arguments cojoin W%function_scope {Cojoin} {A}%type_scope _.


(** ** <<T ∘ (W ×)>> is a monad *)
(******************************************************************************)
Section strength_as_writer_distributive_law.

  Context
    `{Monoid W}.

  Lemma strength_ret_l `{Functor F} : forall A : Type,
      σ ∘ ret (W ×) (F A) =
      map F (ret (W ×) A).
  Proof.
    reflexivity.
  Qed.

  Lemma strength_join_l `{Functor F} : forall A : Type,
      σ ∘ join (T := (W ×)) (A := F A) =
      map F (join (T := (W ×)) (A := A)) ∘ σ ∘ map (W ×) σ.
  Proof.
    intros. ext [w1 [w2 t]]. unfold compose; cbn.
    compose near t. rewrite fun_map_map.
    compose near t on right. rewrite fun_map_map.
    reflexivity.
  Qed.

  Context
    `{Monad T}.

  #[export, program] Instance BeckDistributiveLaw_strength :
    BeckDistributiveLaw (W ×) T :=
    {| bdist_join_r := strength_join T W;
       bdist_unit_r := strength_ret T W;
       bdist_join_l := strength_join_l;
       bdist_unit_l := strength_ret_l;
    |}.

  #[export] Instance: Monad (T ∘ (W ×)) := Monad_Beck.

End strength_as_writer_distributive_law.


(** ** Miscellaneous properties *)
(******************************************************************************)
Section Writer_miscellaneous.

  Context
    `{Monoid W}.

  Import Categorical.Monad.Notations.

  (* This rewrite is useful when proving decoration-traversal compatibility
     in the binder case. *)
  Theorem strength_shift1 : forall (F : Type -> Type) `{Functor F} (w : W) (A : Type),
      σ ∘ μ (T := (W ×)) ∘ pair w = map F (μ (T := (W ×)) ∘ pair w) ∘ strength (F := F) (B := A).
  Proof.
    intros. ext [w' x]. unfold compose; cbn.
    compose near x. now rewrite fun_map_map.
  Qed.


End Writer_miscellaneous.

