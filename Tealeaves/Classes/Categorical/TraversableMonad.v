From Tealeaves Require Export
  Classes.Categorical.Monad
  Classes.Categorical.TraversableFunctor.

Import Functor.Notations.
Import Monad.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables F G T A B.

(** * Traversable monads *)
(******************************************************************************)
#[local] Arguments dist F%function_scope {ApplicativeDist} G%function_scope  {H H0 H1} A%type_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments dist F%function_scope {ApplicativeDist} G%function_scope
  {H H0 H1} {A}%type_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.
#[local] Arguments join T%function_scope {Join} {A}%type_scope _.

(** ** Typeclass *)
(******************************************************************************)
Class TraversableMonad
  (T : Type -> Type)
  `{Map T} `{Return T} `{Join T} `{ApplicativeDist T} :=
  { trvmon_monad :> Monad T;
    trvmon_functor :> TraversableFunctor T;
    trvmon_ret : forall `{Applicative G},
      `(dist T G ∘ ret T (G A) = map G (ret T A));
    trvmon_join : forall `{Applicative G},
      `(dist T G ∘ join T (A := G A) = map G (join T) ∘ dist T G ∘ map T (dist T G));
  }.

(*
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
      rewrite (@map_const_spec (list A) X Y f).
      rewrite (@map_const_spec (list (list A)) X Y f).
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
    rewrite <- (fun_map_map T).
    repeat reassociate -> on left. reassociate <- near (dist T (Const (list A))).
    rewrite (natural (ϕ := @ret T _));
      unfold_ops @Map_I.
    repeat reassociate -> on left.
    reassociate <- near (map T (@mkConst (list A) False)).
    rewrite (natural (ϕ := @ret T _));
      unfold_ops @Map_I.
    repeat reassociate -> on left;
      reassociate <- near (dist T _).
    rewrite (trvmon_ret T).
    ext a. reflexivity.
  Qed.

  Theorem tolist_join : forall A : Type,
      tolist T ∘ join T = join list ∘ tolist T ∘ map T (tolist T) (A := T A).
  Proof.
    intros. rewrite (traversable_tolist_spec T False). reassociate ->.
    unfold traverse. reassociate -> on left.
    rewrite (natural (ϕ := @join T _)).
    reassociate <- on left. rewrite (trvmon_join T (G := const (list A))).
    change (map (const (list A)) (join T) ∘ ?f) with f.
    rewrite <- (fun_map_map T).
    repeat reassociate <-. fequal.
    unfold_ops @Dist_compose. fequal.
    rewrite (traversable_tolist_spec T False). unfold traverse.
    reassociate <- on right.
    rewrite <- (dist_morph T (ϕ := (fun X : Type => @join list Join_list A))).
    reassociate -> on right. rewrite (fun_map_map T).
    rewrite (mon_join_ret list). rewrite (fun_map_id T).
    change (?f ∘ id) with f.
    now rewrite (dist_const1 T (T False)).
  Qed.

  #[global] Instance ListableMonad_TraversableMonad : ListableMonad T :=
    {| lmon_ret := tolist_ret;
       lmon_join := tolist_join;
    |}.

End TraversableMonad_listable.
*)
