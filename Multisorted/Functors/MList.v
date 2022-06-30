From Tealeaves Require Export
     Classes.Monoid
     Functors.List
     Functors.Constant
     Functors.Writer.

From Multisorted Require Export
     Classes.DTM.

Import Monoid.Notations.
Import List.ListNotations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope list_scope.

(** * Sorted lists with context *)
(******************************************************************************)
Section list.

  Context
    `{ix : Index}
    `{Monoid W}.

  Instance: MReturn (fun k A => list (W * (K * A))) :=
    fun A (k : K) (a : A) => [(Ƶ, (k, a))].

  (** This operation is a context- and tag-sensitive substitution operation
   on lists of annotated values. It is used internally to reason about the
   interaction between <<mbinddt>> and <<tomlistd>>. *)
  Fixpoint mbinddt_list
           `(f : forall (k : K), W * A -> list (W * (K * B)))
           (l : list (W * (K * A))) : list (W * (K * B)) :=
    match l with
    | nil => nil
    | cons (w, (k, a)) rest =>
      fmap list (incr w) (f k (w, a)) ++ mbinddt_list f rest
    end.

  Lemma mbinddt_list_nil : forall
      `(f : forall (k : K), W * A -> list (W * (K * B))),
      mbinddt_list f nil = nil.
  Proof.
    intros. easy.
  Qed.

  Lemma mbinddt_list_ret : forall
      `(f : forall (k : K), W * A -> list (W * (K * B))) (k : K) (a : A),
      mbinddt_list f (mret (fun k A => list (W * (K * A))) k a) = f k (Ƶ, a).
  Proof.
    intros. cbn. List.simpl_list.
    replace (incr (Ƶ : W)) with (@id (W * (K * B))).
    - now rewrite (fun_fmap_id list).
    - ext [w [k2 b]]. cbn. now simpl_monoid.
  Qed.

  Lemma mbinddt_list_cons : forall
      `(f : forall (k : K), W * A -> list (W * (K * B)))
      (w : W) (k : K) (a : A)
      (l : list (W * (K * A))),
      mbinddt_list f ((w, (k, a)) :: l) = fmap list (incr w) (f k (w, a)) ++ mbinddt_list f l.
  Proof.
    intros. easy.
  Qed.

  Lemma mbinddt_list_app : forall
      `(f : forall (k : K), W * A -> list (W * (K * B)))
      (l1 l2 : list (W * (K * A))),
      mbinddt_list f (l1 ++ l2) = mbinddt_list f l1 ++ mbinddt_list f l2.
  Proof.
    intros. induction l1.
    - easy.
    - destruct a as [w [k a]].
      cbn. rewrite IHl1.
      now rewrite List.app_assoc.
  Qed.

  #[global] Instance : forall `(f : forall (k : K), W * A -> list (W * (K * B))),
      ApplicativeMorphism (const (list (W * (K * A))))
                          (const (list (W * (K * B))))
                          (const (mbinddt_list f)).
  Proof.
    intros. eapply ApplicativeMorphism_monoid_morphism.
    Unshelve. constructor; try typeclasses eauto.
    - easy.
    - intros. apply mbinddt_list_app.
  Qed.

End list.
