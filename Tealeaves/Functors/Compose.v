From Tealeaves Require Export
  Util.Prelude
  Classes.Functor.

#[local] Generalizable Variables F G.

  (** It is sometimes necessary to explicitly unfold
<<compose>> in the type arguments of a <<compose>> in order to rewrite
with naturality laws without using <<Set Keyed Unification>>. *)
Ltac unfold_compose_in_compose :=
  repeat match goal with
    | |- context [@compose ?A ?B ?C] =>
        let A' := eval unfold compose in A in
          let B' := eval unfold compose in B in
            let C' := eval unfold compose in C in
              progress (change (@compose A B C) with (@compose A' B' C'))
    end.

(** * The composition of two functors *)
(******************************************************************************)
Section Functor_composition.

  Context
    `{Functor F}
    `{Functor G}.

  #[export] Instance Fmap_compose : Fmap (G ∘ F) :=
    fun A B f => fmap G (fmap F f).

  #[export, program] Instance Functor_compose : Functor (G ∘ F).

  Solve Obligations with
    (intros; unfold transparent tcs;
     unfold_compose_in_compose;
     (rewrite (fun_fmap_id F), (fun_fmap_id G)) +
       (rewrite (fun_fmap_fmap G), (fun_fmap_fmap F));
     reflexivity).

End Functor_composition.
