(** This file contains additional abstract theory for decorated functors,
    such as their characterization as certain kinds of co-modules. *)

From Tealeaves Require Import
  Classes.Monoid
  Classes.Algebraic.Decorated.Functor
  Classes.Algebraic.RightComodule.

#[local] Generalizable Variables W F.

(** * A decorated functor is precisely a right comodule of <<prod W>> *)
(******************************************************************************)
Section RightComodule_DecoratedFunctor.

  Context `{DecoratedFunctor W F}.

  Definition RightComodule_DecoratedFunctor : RightComodule F (prod W) :=
  {| rcom_coaction_coaction := dfun_dec_dec W F;
     rcom_fmap_extr_coaction := dfun_dec_extract W F;
  |}.

End RightComodule_DecoratedFunctor.

Section DecoratedFunctor_RightComodule.

  (** This context is declared so that <<RightComodule>> uses the
  reader/writer comonad rather than an opaque one. *)
  Context
    `{Fmap F} `{RightCoaction F (prod W)}
    `{! RightComodule F (prod W)} `{Monoid W}.

  Definition DecoratedFunctor_RightComodule : DecoratedFunctor W F :=
  {| dfun_dec_dec := rcom_coaction_coaction F (prod W);
     dfun_dec_extract := rcom_fmap_extr_coaction F (prod W);
  |}.

End DecoratedFunctor_RightComodule.
