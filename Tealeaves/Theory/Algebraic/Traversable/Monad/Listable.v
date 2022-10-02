From Tealeaves Require Import
  Classes.Algebraic.Listable.Monad
  Theory.Algebraic.Traversable.Monad.ToKleisli
  Theory.Kleisli.Traversable.Functor.Container
  Functors.Constant
  Functors.List.

Import Applicative.Notations.

#[local] Generalizable Variables T.

(******************************************************************************)
Section TraversableMonad_listable.

  Context
    `{TraversableMonad T}.

  Instance ApplicativeMorphism_join_list : forall A : Type,
      ApplicativeMorphism
        (const (list (list A)))
        (const (list A))
        (fun X => @join list Join_list A).
  Proof.
    intros. constructor; try typeclasses eauto.
    - intros X Y f x. cbv in x.
      rewrite (@fmap_const_spec (list A) X Y f).
      rewrite (@fmap_const_spec (list (list A)) X Y f).
      reflexivity.
    - intros X x. cbn. reflexivity.
    - intros X Y x y. cbv in x, y.
      change (?x ⊗ ?y) with (List.app x y).
      now rewrite join_list_app.
  Qed.

  Theorem tolist_ret : forall A : Type,
      tolist T ∘ ret T = ret list (A := A).
  Proof.
    intros. unfold_ops @Tolist_Traversable.
    rewrite <- (fun_fmap_fmap T).
    repeat reassociate -> on left. reassociate <- near (dist T (Const (list A))).
    rewrite (natural (ϕ := @ret T _));
      unfold_ops @Fmap_I.
    repeat reassociate -> on left.
    reassociate <- near (fmap T (@mkConst (list A) False)).
    rewrite (natural (ϕ := @ret T _));
      unfold_ops @Fmap_I.
    repeat reassociate -> on left;
      reassociate <- near (dist T _).
    rewrite (trvmon_ret T).
    ext a. reflexivity.
  Qed.

  Theorem tolist_join : forall A : Type,
      tolist T ∘ join T = join list ∘ tolist T ∘ fmap T (tolist T) (A := T A).
  Proof.
    intros. rewrite (traversable_tolist_spec T False). reassociate ->.
    unfold traverse. reassociate -> on left.
    rewrite (natural (ϕ := @join T _)).
    reassociate <- on left. rewrite (trvmon_join T (G := const (list A))).
    change (fmap (const (list A)) (join T) ∘ ?f) with f.
    rewrite <- (fun_fmap_fmap T).
    repeat reassociate <-. fequal.
    unfold_ops @Dist_compose. fequal.
    rewrite (traversable_tolist_spec T False). unfold traverse.
    reassociate <- on right.
    rewrite <- (dist_morph T (ϕ := (fun X : Type => @join list Join_list A))).
    reassociate -> on right. rewrite (fun_fmap_fmap T).
    rewrite (mon_join_ret list). rewrite (fun_fmap_id T).
    change (?f ∘ id) with f.
    now rewrite (dist_const1 T (T False)).
  Qed.

  #[global] Instance ListableMonad_TraversableMonad : ListableMonad T :=
    {| lmon_ret := tolist_ret;
       lmon_join := tolist_join;
    |}.

End TraversableMonad_listable.
