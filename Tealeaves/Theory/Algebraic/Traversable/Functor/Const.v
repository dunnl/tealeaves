From Tealeaves Require Export
  Classes.Algebraic.Traversable.Functor
  Functors.Constant.

#[local] Generalizable Variables M.

(** * Operations involving constant applicative functors *)
(******************************************************************************)
(** To distributive over constant applicative functors, i.e. to fold
    over monoidal values, we can use the <<Const>> applicative
    functor. Unfortunately this tends to clutter operations with
    <<unconst>> operations which get in the way of convenient
    rewriting. We provide a lighter-weight alternative in this section
    and some specifications proving equivalence with the <<Const>>
    versions. *)
Section TraversableFunctor_const.

  Context
    (T : Type -> Type)
    `{TraversableFunctor T}.

  (** *** Distribution over <<const>> is agnostic about the tag. *)
  (** Distribution over a constant applicative functor is agnostic
      about the type argument ("tag") to the constant functor. On
      paper it is easy to ignore this, but in Coq this must be
      proved. Observe this equality is ill-typed if [Const] is used instead. *)
  (******************************************************************************)
  Lemma dist_const1 : forall (X : Type) `{Monoid M},
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) X)
      =
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) False).
  Proof.
    intros. symmetry. change (?f = ?g) with (f = g ∘ (@id (T M))).
    rewrite <- (fun_fmap_id T).
    change (@id M) with
        (fmap (A := False) (B:=X) (const M) exfalso).
    change (fmap T (fmap (const M) ?f))
      with (fmap (T ∘ const M) f).
    rewrite <- (natural (ϕ := @dist T _ (const M) _ _ _) (B := X) (A := False)).
    reflexivity.
  Qed.

  Lemma dist_const2 : forall (X Y : Type) `{Monoid M},
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) X)
      =
      (@dist T _ (const M)
             (Fmap_const) (Pure_const) (Mult_const) Y).
  Proof.
    intros. now rewrite (dist_const1 X), (dist_const1 Y).
  Qed.

  (** *** Distribution over [Const] vs <<const>> *)
  (******************************************************************************)
  Theorem traversable_const_spec (tag : Type) `{Monoid M} :
    unconst ∘ @dist T _ (Const M)
            (Fmap_Const)
            (Pure_Const)
            (Mult_Const) tag ∘ fmap T (mkConst)
    = @dist T _ (const M)
            (Fmap_const)
            (Pure_const)
            (Mult_const) tag.
  Proof.
    intros. rewrite <- (dist_morph T (ϕ := @unconst _)).
    reassociate -> on left. rewrite (fun_fmap_fmap T).
    change (unconst ∘ mkConst) with (@id M).
    now rewrite (fun_fmap_id T).
  Qed.

End TraversableFunctor_const.
