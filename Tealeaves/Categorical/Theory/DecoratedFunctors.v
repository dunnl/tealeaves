
(** * A decorated functor is precisely a right comodule of <<prod E>> *)
(******************************************************************************)
Section RightComodule_DecoratedFunctor.

  Context
    `{DecoratedFunctor E F}.

  Definition RightComodule_DecoratedFunctor : RightComodule F (prod E) :=
  {| rcom_coaction_coaction := dfun_dec_dec E F;
     rcom_fmap_extr_coaction := dfun_dec_extract E F;
  |}.

End RightComodule_DecoratedFunctor.

Section DecoratedFunctor_RightComodule.

  (** This context is declared so that <<RightComodule>> uses the
  reader/writer comonad rather than an opaque one. *)
  Context
    `{Fmap F} `{RightCoaction F (prod E)}
    `{! RightComodule F (prod E)} `{Monoid E}.

  Definition DecoratedFunctor_RightComodule : DecoratedFunctor E F :=
  {| dfun_dec_dec := rcom_coaction_coaction F (prod E);
     dfun_dec_extract := rcom_fmap_extr_coaction F (prod E);
  |}.

End DecoratedFunctor_RightComodule.
