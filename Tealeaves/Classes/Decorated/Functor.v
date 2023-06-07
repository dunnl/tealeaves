From Tealeaves Require Export
  Classes.Comonad
  Functors.Environment.

Import Product.Notations.

(** * Operation <<fmapdt>> *)
(******************************************************************************)
Section operations.

  Context
    (E : Type)
    (F : Type -> Type).

  Class Fmapd :=
    fmapd : forall {A B : Type} (f : E * A -> B), F A -> F B.

End operations.

Arguments fmapd {E}%type_scope F%function_scope {Fmapd} {A B}%type_scope f%function_scope _.

(** ** Typeclass *)
(******************************************************************************)
Section class.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Fmapd E T}.

  Class DecoratedFunctor :=
    { dfun_fmapd1 : forall (A : Type),
        fmapd T (extract (E ×)) = @id (T A);
      dfun_fmapd2 : forall (A B C : Type) (g : E * B -> C) (f : E * A -> B),
        fmapd T g ∘ fmapd T f = fmapd T (g ∘ cobind (E ×) f);
    }.

End class.

#[local] Generalizable Variables E T.

(** * To functor *)
(******************************************************************************)
Module ToFunctor.

  Section operation.

    Context
      (T : Type -> Type)
      `{Fmapd E T}.

  #[export] Instance Fmap_Fmapd : Fmap T :=
      fun (A B : Type) (f : A -> B) => fmapd T (f ∘ extract (E ×)).

  End operation.

  Section with_kleisli.

    Context
      (T : Type -> Type)
      `{DecoratedFunctor E T}.

    Lemma fmap_id : forall (A : Type),
        fmap T (@id A) = @id (T A).
    Proof.
      intros. unfold_ops @Fmap_Fmapd.
      now rewrite (dfun_fmapd1 E T).
    Qed.

    Lemma fmap_fmap : forall (A B C : Type) (f : A -> B) (g : B -> C),
        fmap T g ∘ fmap T f = fmap T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Fmapd.
      rewrite (dfun_fmapd2 E T).
      fequal. reassociate ->.
      now rewrite (kcom_cobind0 (E ×)).
    Qed.

    #[export] Instance: Classes.Functor.Functor T :=
      {| fun_fmap_id := fmap_id;
        fun_fmap_fmap := fmap_fmap;
      |}.

    Lemma fmap_fmapd : forall (A B C : Type)
                         (g : B -> C)
                         (f : E * A -> B),
        fmap T g ∘ fmapd T f =
          fmapd T (g ∘ f).
    Proof.
      intros. unfold_ops @Fmap_Fmapd.
      rewrite (dfun_fmapd2 E T).
      reassociate ->.
      now rewrite (kcom_cobind0 (E ×)).
    Qed.

    (*
    Lemma fmapd_fmap: forall (A B C : Type)
                        (g : E * B -> C)
                        (f : A -> B),
        fmapd T g ∘ fmap T f = fmapd T (g ∘ fmap (E ×) f).
    Proof.
      intros. unfold_ops @Fmap_Fmapd.
      rewrite (dfun_fmapd2 E T).
      unfold_ops @Fmap_Cobind.
      rewrite <- (fmap_to_cobind (E ×)).
      reflexivity.
    Qed.
    *)

  End with_kleisli.

End ToFunctor.
