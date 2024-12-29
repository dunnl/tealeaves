From Tealeaves Require Import
  Classes.Categorical.Monad
  Classes.Kleisli.TraversableMonad
  Classes.Categorical.ContainerFunctor
  Classes.Categorical.ShapelyFunctor.

From Tealeaves Require Export
  Functors.Subset
  Misc.List.

Import ContainerFunctor.Notations.
Import TraversableMonad.Notations.
Import List.ListNotations.
Import Monoid.Notations.
Import Subset.Notations.
Import Applicative.Notations.
Export EqNotations.

#[local] Generalizable Variables M A B G ϕ.

(** * The [list] monad, categorically *)
(******************************************************************************)

(** ** Monad operations *)
(******************************************************************************)
#[export] Instance Return_list : Return list := fun A a => cons a nil.

#[export] Instance Join_list : Join list := @List.concat.

(** *** Rewriting lemmas for <<join>> *)
(******************************************************************************)
Lemma join_list_nil :
  `(join ([] : list (list A)) = []).
Proof.
  reflexivity.
Qed.

Lemma join_list_cons : forall A (l : list A) (ll : list (list A)),
    join (l :: ll) = l ++ join ll.
Proof.
  reflexivity.
Qed.

Lemma join_list_one : forall A (l : list A),
    join [ l ] = l.
Proof.
  intros. cbn. now List.simpl_list.
Qed.

Lemma join_list_app : forall A (l1 l2 : list (list A)),
    join (l1 ++ l2) = join l1 ++ join l2.
Proof.
  apply List.concat_app.
Qed.

#[export] Hint Rewrite join_list_nil join_list_cons join_list_one join_list_app :
  tea_list.

(** ** Monad instance *)
(******************************************************************************)
#[export] Instance Natural_ret_list : Natural (@ret list _).
Proof.
  constructor; try typeclasses eauto.
  introv. now ext l.
Qed.

#[export] Instance Natural_join_list : Natural (@join list _).
Proof.
  constructor; try typeclasses eauto.
  intros ? ? f. ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

Theorem join_ret_list {A} :
  join ∘ ret (T := list) = @id (list A).
Proof.
  ext l. unfold compose. destruct l.
  - reflexivity.
  - cbn. now List.simpl_list.
Qed.

Theorem join_map_ret_list {A} :
  join ∘ map (F := list) (ret (T := list)) = @id (list A).
Proof.
  ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

Theorem join_join_list {A} :
  join (T := list) ∘ join (T := list) (A:=list A) =
  join ∘ map (F := list) (join).
Proof.
  ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

#[export] Instance CategoricalMonad_list :
  Categorical.Monad.Monad list :=
  {| mon_join_ret := @join_ret_list;
     mon_join_map_ret := @join_map_ret_list;
     mon_join_join := @join_join_list;
  |}.

(** * The [list] traversable monad, Kleisli *)
(******************************************************************************)

(** ** <<bindt>>, <<bind>>, <<traverse>> operations *)
(******************************************************************************)
Fixpoint bindt_list (G : Type -> Type) `{Map G} `{Pure G} `{Mult G} (A B : Type) (f : A -> G (list B)) (l : list A)
  : G (list B) :=
  match l with
  | nil => pure (@nil B)
  | x :: xs =>
      pure (@List.app B) <⋆> f x <⋆> bindt_list G A B f xs
  end.

Fixpoint bind_list (A B : Type) (f : A -> list B) (l : list A) : list B :=
  match l with
  | nil => @nil B
  | x :: xs =>
      f x ● bind_list A B f xs
  end.

Fixpoint traverse_list (G : Type -> Type) `{Map G} `{Pure G} `{Mult G} (A B : Type) (f : A -> G B) (l : list A)
  : G (list B) :=
  match l with
  | nil => pure (@nil B)
  | x :: xs =>
      pure (@List.cons B) <⋆> f x <⋆> (traverse_list G A B f xs)
  end.

#[export] Instance Bindt_list : Bindt list list := @bindt_list.
#[export] Instance Bind_list : Bind list list := @bind_list.
#[export] Instance Traverse_list : Traverse list := @traverse_list.

#[export] Instance Comat_Bind_Bindt_list:
  Compat_Bind_Bindt list list.
Proof.
  hnf. ext A B f l.
  induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

#[export] Instance Comat_Traverse_Bindt_list:
  Compat_Traverse_Bindt list list.
Proof.
  hnf. intros.
  ext A B f l.
  induction l as [| a rest IHrest].
  - reflexivity.
  - cbn.
    rewrite IHrest.
    unfold compose at 1.
    rewrite pure_ap_map.
    rewrite map_to_ap.
    reflexivity.
Qed.

#[export] Instance Comat_Map_Bindt_list:
  Compat_Map_Bindt list list.
Proof.
  hnf. ext A B f l.
  induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

#[export] Instance Compat_Map_Traverse_list:
  Compat_Map_Traverse list
  := ltac:(typeclasses eauto).

#[export] Instance Compat_Map_Bind_list:
  Compat_Map_Bind list list
  := ltac:(typeclasses eauto).

(** ** Rewriting lemmas for <<bindt>> *)
(******************************************************************************)
Section bindt_rewriting_lemmas.

  Context
    (G : Type -> Type)
    `{Applicative G}
    (A B : Type).

  Lemma bindt_list_nil : forall (f : A -> G (list B)),
      bindt f (@nil A) = pure (@nil B).
  Proof.
    reflexivity.
  Qed.

  Lemma bindt_list_one : forall (f : A -> G (list B)) (a : A),
      bindt f (ret (T := list) a) = f a.
  Proof.
    intros.
    cbn.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap1.
    unfold compose; do 2 fequal;
      ext l; rewrite (List.app_nil_end).
    reflexivity.
  Qed.

  Lemma bindt_list_cons : forall (f : A -> G (list B)) (a : A) (l : list A),
      bindt f (a :: l) = pure (@app B) <⋆> f a <⋆> bindt f l.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma bindt_list_app : forall (f : A -> G (list B)) (l1 l2 : list A),
      bindt f (l1 ++ l2) = pure (@app B) <⋆> bindt f l1 <⋆> bindt f l2.
  Proof.
    intros.
    induction l1.
    - cbn. rewrite ap2.
      rewrite ap1.
      reflexivity.
    - cbn.
      rewrite IHl1.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      rewrite ap3.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      repeat fequal.
      ext x y z. unfold compose.
      unfold evalAt.
      now rewrite List.app_assoc.
  Qed.

End bindt_rewriting_lemmas.

#[export] Hint Rewrite bindt_list_nil bindt_list_cons bindt_list_one bindt_list_app :
  tea_list.

(** ** Rewriting lemmas for <<traverse>> *)
(******************************************************************************)
Section traverse_rewriting_lemmas.

  Context
    (G : Type -> Type)
    `{Applicative G}
    (A B : Type).

  Lemma traverse_list_nil : forall (f : A -> G B),
      traverse f (@nil A) = pure (@nil B).
  Proof.
    reflexivity.
  Qed.

  Lemma traverse_list_one : forall (f : A -> G B) (a : A),
      traverse f (ret (T := list) a) = map ret (f a).
  Proof.
    intros.
    cbn.
    rewrite ap3.
    rewrite <- ap4;
      rewrite ap2;
      rewrite ap2.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma traverse_list_cons : forall (f : A -> G B) (a : A) (l : list A),
      traverse f (a :: l) = pure (@cons B) <⋆> f a <⋆> traverse f l.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma traverse_list_app : forall (f : A -> G B) (l1 l2 : list A),
      traverse f (l1 ++ l2) = pure (@app B) <⋆> traverse f l1 <⋆> traverse f l2.
  Proof.
    intros.
    induction l1.
    - cbn. rewrite ap2.
      rewrite ap1.
      reflexivity.
    - cbn.
      rewrite IHl1.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      rewrite ap3.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      reflexivity.
  Qed.

  Definition snoc {A: Type} (l: list A) (a: A) := l ++ [a].

  Lemma traverse_list_snoc : forall (f : A -> G B) (l : list A) (a: A),
      traverse f (l ++ a::nil) =
        pure (@snoc B) <⋆> traverse f l <⋆> f a.
  Proof.
    intros.
    rewrite traverse_list_app.
    cbn.
    repeat rewrite <- ap4.
    repeat rewrite ap2.
    rewrite ap3.
    repeat rewrite <- ap4.
    repeat rewrite ap2.
    rewrite ap3.
    repeat rewrite <- ap4.
    repeat rewrite ap2.
    unfold compose.
    reflexivity.
  Qed.

End traverse_rewriting_lemmas.

#[export] Hint Rewrite traverse_list_nil traverse_list_cons traverse_list_one
  traverse_list_snoc traverse_list_app :
  tea_list.

(** ** Rewriting lemmas for <<bind>> *)
(******************************************************************************)
Section bind_rewriting_lemmas.

  Context
    (A B : Type).

  Lemma bind_list_nil : forall (f : A -> list B),
      bind f (@nil A) = @nil B.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_list_one : forall (f : A -> list B) (a : A),
      bind f (ret a) = f a.
  Proof.
    intros.
    cbn. change (@nil B) with (Ƶ : list B).
    now simpl_monoid.
  Qed.

  Lemma bind_list_cons : forall (f : A -> list B) (a : A) (l : list A),
      bind f (a :: l) = f a ++ bind f l.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_list_app : forall (f : A -> list B) (l1 l2 : list A),
      bind f (l1 ++ l2) = bind f l1 ++ bind f l2.
  Proof.
    intros.
    induction l1.
    - cbn. reflexivity.
    - cbn.
      rewrite IHl1.
      change (?f ● ?g) with (f ++ g).
      rewrite List.app_assoc.
      reflexivity.
  Qed.

End bind_rewriting_lemmas.

#[export] Hint Rewrite bind_list_nil bind_list_cons bind_list_one bind_list_app :
  tea_list.

(** ** Traversable monad instance *)
(******************************************************************************)
Section bindt_laws.

  Context
    (G : Type -> Type)
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    (A B C : Type).

  Lemma list_bindt0 : forall (f : A -> G (list B)),
      bindt f ∘ ret = f.
  Proof.
    intros. ext a.
    apply (bindt_list_one G).
  Qed.

  Lemma list_bindt1 :
    bindt (T := list) (U := list)
      (A := A) (B := A) (G := fun A => A) (ret (T := list)) = id.
  Proof.
    ext l. induction l.
    - reflexivity.
    - cbn. rewrite IHl.
      reflexivity.
  Qed.

  Lemma list_bindt2 :
    forall (g : B -> G2 (list C)) (f : A -> G1 (list B)),
      map (F := G1) (bindt g) ∘ bindt f =
        bindt (G := G1 ∘ G2) (g ⋆3 f).
  Proof.
    intros. ext l. induction l.
    - unfold compose; cbn.
      rewrite app_pure_natural.
      rewrite bindt_list_nil.
      reflexivity.
    - unfold compose at 1.
      rewrite bindt_list_cons.
      rewrite map_to_ap.
      do 3 rewrite <- ap4.
      do 4 rewrite ap2.
      rewrite bindt_list_cons.
      rewrite <- IHl.
      unfold compose at 7.
      do 2 rewrite (ap_compose1 G2 G1).
      unfold_ops @Pure_compose.
      rewrite map_to_ap.
      rewrite <- ap4.
      rewrite <- ap4.
      rewrite <- ap4.
      rewrite <- ap4.
      do 6 rewrite ap2.
      unfold kc3.
      unfold compose at 8.
      rewrite map_to_ap.
      rewrite <- ap4.
      do 2 rewrite ap2.
      rewrite ap3.
      rewrite <- ap4.
      do 2 rewrite ap2.
      fequal.
      fequal.
      fequal. ext l1 l2.
      unfold compose. rewrite (bindt_list_app G2).
      reflexivity.
  Qed.

End bindt_laws.

Lemma list_morph :
  forall `(morph : ApplicativeMorphism G1 G2 ϕ),
  forall (A B : Type) (f : A -> G1 (list B)),
    ϕ (list B) ∘ bindt f = bindt (ϕ (list B) ∘ f).
Proof.
  intros. unfold compose at 1 2. ext l.
  induction l.
  - cbn. rewrite appmor_pure. reflexivity.
  - cbn.
    rewrite (ap_morphism_1 (G := G1)).
    rewrite (ap_morphism_1 (G := G1)).
    rewrite appmor_pure.
    rewrite IHl.
    reflexivity.
Qed.

#[export] Instance TraversableRightPreModule_list:
  TraversableRightPreModule list list :=
  {| ktm_bindt1 := list_bindt1;
     ktm_bindt2 := @list_bindt2;
     ktm_morph := @list_morph;
  |}.

#[export] Instance TraversableMonad_list:
  TraversableMonad list :=
  {| ktm_bindt0 := list_bindt0;
  |}.

#[export] Instance TraversableRightModule_list:
  TraversableRightModule list list :=
  {| ktmod_monad := _; |}.

#[export] Instance TraversableFunctor_list:
  TraversableFunctor list :=
  TraversableFunctor_TraversableMonad.

(** * List algebras and folds *)
(******************************************************************************)

(** ** Some homomorphisms *)
(******************************************************************************)

(** *** <<map>> is a monoid homomorphism *)
(******************************************************************************)
#[export, program] Instance Monmor_list_map `(f : A -> B) :
  Monoid_Morphism (list A) (list B) (map f) :=
  {| monmor_op := map_list_app f; |}.

(** *** [join] is a monoid homomorphism *)
(** The <<join>> operation is a monoid homomorphism from <<list (list A)>> to
    <<list A>>. This is just a special case of the fact that monoid homomorphisms
    on free monoids are precisely of the form <<foldMap f>> for any <<f : A -> M>>,
    specialized to <<f = id>> case, but we don't need that much generality. *)
(******************************************************************************)
#[export] Instance Monmor_join (A : Type) :
  Monoid_Morphism (list (list A)) (list A) (join (A := A)) :=
  {| monmor_unit := @join_list_nil A;
     monmor_op := @join_list_app A;
  |}.

(** *** [bind] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind (A B : Type) (f : A -> list B) :
  Monoid_Morphism (list A) (list B) (bind f).
Proof.
  constructor; try typeclasses eauto.
  - reflexivity.
  - intros. induction a1.
    + reflexivity.
    + cbn. rewrite IHa1.
      now rewrite monoid_assoc.
Qed.

(** ** Misc properties *)
(******************************************************************************)
(** <<fold>> commutes with monoid homomorphisms *)
Lemma fold_mon_hom : forall `(ϕ : M1 -> M2) `{Monoid_Morphism M1 M2 ϕ},
    ϕ ∘ fold M1 = fold M2 ∘ map ϕ.
Proof.
  intros ? ? ϕ ? ? ? ? ?. unfold compose. ext l.
  induction l as [| ? ? IHl].
  - cbn. apply monmor_unit.
  - cbn. now rewrite (monmor_op (ϕ := ϕ)), IHl.
Qed.

(** In the special case that we fold a list of lists, the result is equivalent
    to joining the list of lists. *)
Lemma fold_equal_join : forall {A},
    fold (list A) = join (T := list) (A:=A).
Proof.
  intros. ext l. induction l as [| ? ? IHl].
  - reflexivity.
  - cbn. now rewrite IHl.
Qed.

(** ** <<foldMap_list>> *)
(******************************************************************************)
Definition foldMap_list {M : Type} `{op : Monoid_op M} `{unit : Monoid_unit M}
  {A : Type} (f : A -> M) : list A -> M :=
  fold M ∘ map f.

(** <<foldMap_list>> is a monoid homomorphism *)
#[export] Instance Monoid_Morphism_foldMap_list
  `{Monoid M} {A : Type}
  `(f : A -> M) : Monoid_Morphism (list A) M (foldMap_list f).
Proof.
  unfold foldMap_list.
  eapply Monoid_Morphism_compose;
    typeclasses eauto.
Qed.

(** <<foldMap_list>> commutes with monoid homomorphisms *)
Lemma foldMap_list_morphism `{Monoid_Morphism M1 M2 ϕ}
  : forall `(f : A -> M1),
    ϕ ∘ foldMap_list f = foldMap_list (ϕ ∘ f).
Proof.
  intros. unfold foldMap_list.
  reassociate <- on left.
  rewrite (fold_mon_hom ϕ).
  reassociate -> on left.
  rewrite fun_map_map.
  reflexivity.
Qed.

(** *** Rewriting with <<foldMap_list>> *)
(******************************************************************************)
Section foldMap_list_rw.

  Context
    {A M : Type}
    `{Monoid M}
    (f : A -> M).

  Lemma foldMap_list_nil : foldMap_list f (@nil A) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_list_cons : forall (x : A) (xs : list A),
      foldMap_list f (x :: xs) = f x ● foldMap_list f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_list_one (a : A) : foldMap_list f [ a ] = f a.
  Proof.
    cbv. apply monoid_id_l.
  Qed.

  Lemma foldMap_list_ret : foldMap_list f ∘ ret = f.
  Proof.
    ext a; cbn. apply monoid_id_l.
  Qed.

  Lemma foldMap_list_app : forall (l1 l2 : list A),
      foldMap_list f (l1 ++ l2) = foldMap_list f l1 ● foldMap_list f l2.
  Proof.
    intros.
    unfold foldMap_list.
    unfold compose. autorewrite with tea_list.
    rewrite (fold_app M).
    reflexivity.
  Qed.

End foldMap_list_rw.

#[export] Hint Rewrite @foldMap_list_nil @foldMap_list_cons
  @foldMap_list_one @foldMap_list_app : tea_list.

Lemma foldMap_list_ret_id : forall A, foldMap_list (@ret list _ A) = id.
Proof.
  intros.
  ext l.
  induction l as [|x rest IHrest];
    autorewrite with tea_list.
  reflexivity.
  now rewrite IHrest.
Qed.

(** *** Monoids form list (monad-)algebras *)
(** In fact, list algebras are precisely monoids. *)
(******************************************************************************)
Section foldable_list.

  Context
    `{Monoid M}.

  Lemma fold_ret : forall (x : M),
      fold M (ret x : list M) = x.
  Proof.
    apply monoid_id_l.
  Qed.

  Lemma fold_join : forall (l : list (list M)),
      fold M (join l) = fold M (map (fold M) l).
  Proof.
    intro l. rewrite <- fold_equal_join.
    compose near l on left.
    now rewrite (fold_mon_hom (fold M)).
  Qed.

  Lemma fold_constant_unit : forall (l : list M),
      fold M (map (fun _ => Ƶ) l) = Ƶ.
  Proof.
    intro l. induction l.
    - reflexivity.
    - cbn. now simpl_monoid.
  Qed.

End foldable_list.

(** * <<map>> equality inversion lemmas *)
(** Some lemmas for reasoning backwards from equality between two
    similarly-concatenated lists.  *)
(******************************************************************************)
Lemma map_app_inv_l : forall {A B} {f g : A -> B} (l1 l2 : list A),
    map f (l1 ++ l2) = map g (l1 ++ l2) ->
    map f l1 = map g l1.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl_list in *. rewrite IHl1.
    + fequal. simpl in H. inversion H; auto.
    + simpl in H. inversion H. auto.
Qed.

Lemma map_app_inv_r : forall {A B} {f g : A -> B} (l1 l2 : list A),
    map f (l1 ++ l2) = map g (l1 ++ l2) ->
    map f l2 = map g l2.
Proof.
  intros.
  assert (heads_equal : map f l1 = map g l1).
  { eauto using map_app_inv_l. }
  simpl_list in *.
  rewrite heads_equal in H.
  eauto using List.app_inv_head.
Qed.

Lemma map_app_inv : forall {A B} {f g : A -> B} (l1 l2 : list A),
    map f (l1 ++ l2) = map g (l1 ++ l2) ->
    map f l1 = map g l1 /\ map f l2 = map g l2.
Proof.
  intros; split; eauto using map_app_inv_l, map_app_inv_r.
Qed.

#[local] Generalizable Variable F.

(** * Shapely instance for [list] *)
(** As a reasonability check, we prove that [list] is a listable functor. *)
(******************************************************************************)
Section ShapelyFunctor_list.

  Instance Tolist_list : Tolist list := fun A l => l.

  Instance: Natural (@tolist list _).
  Proof.
    constructor; try typeclasses eauto.
    reflexivity.
  Qed.

  Theorem shapeliness_list : shapeliness list.
  Proof.
    intros A t1 t2. intuition.
  Qed.

  Instance: ShapelyFunctor list :=
    {| shp_shapeliness := shapeliness_list; |}.

End ShapelyFunctor_list.

(** ** Rewriting [shape] on lists *)
(******************************************************************************)
Section list_shape_rewrite.

  Lemma shape_nil : forall A,
      shape (@nil A) = @nil unit.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_cons : forall A (a : A) (l : list A),
      shape (a :: l) = tt :: shape l.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_one : forall A (a : A),
      shape [ a ] = [ tt ].
  Proof.
    reflexivity.
  Qed.

  Lemma shape_app : forall A (l1 l2 : list A),
      shape (l1 ++ l2) = shape l1 ++ shape l2.
  Proof.
    intros. unfold shape. now rewrite map_list_app.
  Qed.

  Lemma shape_nil_iff : forall A (l : list A),
      shape l = @nil unit <-> l = [].
  Proof.
    induction l. intuition.
    split; intro contra; now inverts contra.
  Qed.

End list_shape_rewrite.

#[export] Hint Rewrite @shape_nil @shape_cons @shape_one @shape_app : tea_list.

(** ** Reasoning princples for <<shape>> on lists *)
(******************************************************************************)
Section list_shape_lemmas.

  Theorem list_shape_equal_iff : forall (A : Type) (l1 l2 : list A),
      shape l1 = shape l2 <->
        List.length l1 = List.length l2.
  Proof.
    intros. generalize dependent l2.
    induction l1.
    - destruct l2.
      + split; reflexivity.
      + split; inversion 1.
    - cbn. intro l2; destruct l2.
      + cbn. split; inversion 1.
      + cbn. split; inversion 1.
        * fequal. apply IHl1. auto.
        * fequal. apply IHl1. auto.
  Qed.

  Theorem shape_eq_app_r : forall A (l1 l2 r1 r2: list A),
      shape r1 = shape r2 ->
      (shape (l1 ++ r1) = shape (l2 ++ r2) <->
       shape l1 = shape l2).
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split. intros; eauto using List.app_inv_tail.
    intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_eq_app_l : forall A (l1 l2 r1 r2: list A),
      shape l1 = shape l2 ->
      (shape (l1 ++ r1) = shape (l2 ++ r2) <->
       shape r1 = shape r2).
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split. intros; eauto using List.app_inv_head.
    intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_eq_cons_iff : forall A (l1 l2 : list A) (x y : A),
      shape (x :: l1) = shape (y :: l2) <->
      shape l1 = shape l2.
  Proof.
    intros. rewrite 2(shape_cons).
    split; intros hyp. now inverts hyp.
    now rewrite hyp.
  Qed.

  Theorem inv_app_eq_ll : forall A (l1 l2 r1 r2 : list A),
      shape l1 = shape l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| ? ? IHl1 ];
                induction l2 as [| ? ? IHl2 ].
    - reflexivity.
    - introv shape_eq. now inverts shape_eq.
    - introv shape_eq. now inverts shape_eq.
    - introv shape_eq heq.
      rewrite shape_eq_cons_iff in shape_eq.
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem inv_app_eq_rl : forall A (l1 l2 r1 r2 : list A),
      shape r1 = shape r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| ? ? IHl1 ];
                induction l2 as [| ? ? IHl2 ].
    - reflexivity.
    - introv shape_eq heq. apply inv_app_eq_ll with (r1 := r1) (r2 := r2).
      + rewrite <- shape_eq_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq. apply inv_app_eq_ll with (r1 := r1) (r2 := r2).
      + rewrite <- shape_eq_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq.
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem inv_app_eq_lr : forall A (l1 l2 r1 r2 : list A),
      shape l1 = shape l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eauto using List.app_inv_head. }
    { eauto using inv_app_eq_ll. }
  Qed.

  Theorem inv_app_eq_rr : forall A (l1 l2 r1 r2 : list A),
      shape r1 = shape r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eauto using List.app_inv_head. }
    { eauto using inv_app_eq_rl. }
  Qed.

  Theorem inv_app_eq : forall A (l1 l2 r1 r2 : list A),
      shape l1 = shape l2 \/ shape r1 = shape r2 ->
      (l1 ++ r1 = l2 ++ r2) <-> (l1 = l2 /\ r1 = r2).
  Proof.
    introv [hyp | hyp]; split.
    - introv heq. split. eapply inv_app_eq_ll; eauto.
      eapply inv_app_eq_lr; eauto.
    - introv [? ?]. now subst.
    - introv heq. split. eapply inv_app_eq_rl; eauto.
      eapply inv_app_eq_rr; eauto.
    - introv [? ?]. now subst.
  Qed.

  Lemma list_app_inv_r : forall A (l l1 l2 : list A),
      l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    introv hyp. induction l.
    - cbn in hyp. auto.
    - inversion hyp. auto.
  Qed.

  Lemma list_app_inv_l : forall A (l l1 l2 : list A),
      l1 ++ l = l2 ++ l -> l1 = l2.
  Proof.
    introv hyp. eapply inv_app_eq_rl.
    2: eauto. reflexivity.
  Qed.

  Lemma list_app_inv_l2 : forall A (l1 l2 : list A) (a1 a2 : A),
      l1 ++ ret a1 = l2 ++ ret a2 ->
      l1 = l2.
  Proof.
    intros. eapply inv_app_eq_rl; [|eauto]; auto.
  Qed.

  Lemma list_app_inv_r2 : forall A (l1 l2 : list A) (a1 a2 : A),
      l1 ++ [a1] = l2 ++ [a2] ->
      a1 = a2.
  Proof.
    introv. introv hyp.
    apply inv_app_eq_rr in hyp.
    now inversion hyp. easy.
  Qed.

End list_shape_lemmas.

(** * Reasoning principles for <<shape>> on listable functors *)
(******************************************************************************)
Section listable_shape_lemmas.

  Context
    `{Functor F}
    `{Tolist F}
    `{! Natural (@tolist F _)}.

  (* Values with the same shape have equal-length contents *)
  Lemma shape_tolist : forall `(t : F A) `(u : F B),
      shape t = shape u ->
      shape (tolist t) = shape (tolist u).
  Proof.
    introv heq. compose near t. compose near u.
    unfold shape in *. rewrite 2(natural).
    unfold compose.
    fequal. apply heq.
  Qed.

  Corollary shape_l : forall A (l1 l2 : F A) (x y : list A),
      shape l1 = shape l2 ->
      (tolist l1 ++ x = tolist l2 ++ y) ->
      tolist l1 = tolist l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_ll, shape_tolist.
  Qed.

  Corollary shape_r : forall A (l1 l2 : F A) (x y : list A),
      shape l1 = shape l2 ->
      (x ++ tolist l1 = y ++ tolist l2) ->
      tolist l1 = tolist l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_rr, shape_tolist.
  Qed.

End listable_shape_lemmas.

(** * Container-like functor instance *)
(******************************************************************************)
#[export] Instance ToSubset_list : ToSubset list :=
  fun (A : Type) (l : list A) => (fun a : A => @List.In A a l).

(** ** <<tosubset>> and rewriting principles *)
(******************************************************************************)
Lemma tosubset_list_nil : forall (A : Type),
    tosubset (@nil A) = ∅.
Proof.
  intros. extensionality a. reflexivity.
Qed.

Lemma tosubset_list_one : forall (A : Type) (a : A),
    tosubset [a] = {{ a }}.
Proof.
  intros. solve_basic_subset.
Qed.

Lemma tosubset_list_ret : forall (A : Type) (a : A),
    tosubset (ret a) = {{ a }}.
Proof.
  intros. solve_basic_subset.
Qed.

Lemma tosubset_list_cons :
  forall (A : Type) (a : A) (l : list A),
    tosubset (a :: l) = {{ a }} ∪ tosubset l.
Proof.
  intros. extensionality a'. reflexivity.
Qed.

Lemma tosubset_list_app : forall (A : Type) (l1 l2 : list A),
    tosubset (l1 ++ l2) = tosubset l1 ∪ tosubset l2.
Proof.
  intros. induction l1.
  - cbn. rewrite tosubset_list_nil.
    solve_basic_subset.
  - cbn.
    do 2 rewrite tosubset_list_cons.
    rewrite IHl1. solve_basic_subset.
Qed.

#[export] Hint Rewrite
  tosubset_list_nil tosubset_list_one tosubset_list_ret
  tosubset_list_cons tosubset_list_app : tea_list.

(** ** Naturality of <<tosubset>> *)
(******************************************************************************)
#[export] Instance Natural_ToSubset_list : Natural (@tosubset list _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. ext l.
  unfold compose at 1 2.
  induction l.
  - solve_basic_subset.
  - rewrite tosubset_list_cons.
    autorewrite with tea_set tea_list.
    rewrite IHl.
    solve_basic_subset.
Qed.

(** ** [tosubset] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monoid_Morphism_tosubset_list (A : Type) :
  Monoid_Morphism (list A) (subset A) (tosubset (A := A)) :=
  {| monmor_unit := @tosubset_list_nil A;
    monmor_op := @tosubset_list_app A;
  |}.

(** ** <<∈>> for lists *)
(******************************************************************************)
Lemma element_of_list_nil {A} : forall (p : A), p ∈ @nil A <-> False.
Proof.
  reflexivity.
Qed.

Lemma element_of_list_one {A} (a1 a2 : A) : a1 ∈ [ a2 ] <-> a1 = a2.
Proof.
  intros. unfold element_of.
  simpl_list; simpl_subset.
  intuition congruence.
Qed.

Lemma element_of_list_cons {A} : forall (a1 a2 : A) (xs : list A),
    a1 ∈ (a2 :: xs) <-> a1 = a2 \/ a1 ∈ xs.
Proof.
  intros; unfold element_of.
  simpl_list; simpl_subset.
  intuition congruence.
Qed.

Lemma element_of_list_ret {A} (a1 a2 : A) : a1 ∈ ret a2 <-> a1 = a2.
Proof.
  intros. unfold element_of.
  simpl_list; simpl_subset.
  easy.
Qed.

Lemma element_of_list_app {A} : forall (a : A) (xs ys : list A),
    a ∈ (xs ++ ys) <-> a ∈ xs \/ a ∈ ys.
Proof.
  intros. unfold element_of.
  simpl_list; simpl_subset.
  easy.
Qed.

#[export] Hint Rewrite @element_of_list_nil
  @element_of_list_cons @element_of_list_one
  @element_of_list_ret @element_of_list_app : tea_list.

(** *** [x ∈] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monoid_Morphism_element_list (A : Type) (a : A) :
  Monoid_Morphism (list A) Prop
    (tgt_op := Monoid_op_or)
    (tgt_unit := Monoid_unit_false)
    (element_of a).
Proof.
  rewrite element_of_tosubset.
  eapply Monoid_Morphism_compose;
    typeclasses eauto.
Qed.

(** ** Respectfulness conditions *)
(******************************************************************************)
Theorem map_rigidly_respectful_list : forall A B (f g : A -> B) (l : list A),
    (forall (a : A), a ∈ l -> f a = g a) <-> map f l = map g l.
Proof.
  intros. induction l.
  - simpl_list.
    setoid_rewrite element_of_list_nil.
    tauto.
  - simpl_list.
    setoid_rewrite element_of_list_cons.
    destruct IHl. split.
    + intro; fequal; auto.
    + injection 1; intuition (subst; auto).
Qed.

Corollary map_respectful_list : forall A B (l : list A) (f g : A -> B),
    (forall (a : A), a ∈ l -> f a = g a) -> map f l = map g l.
Proof.
  intros. now rewrite <- map_rigidly_respectful_list.
Qed.

#[export] Instance ContainerFunctor_list : ContainerFunctor list :=
  {| cont_pointwise := map_respectful_list;
  |}.

(** ** <<tosubset>> as a monad homomorphism *)
(******************************************************************************)
Lemma tosubset_list_hom1 : forall (A : Type),
    tosubset ∘ ret (A := A) = ret (T := subset).
Proof.
  intros.
  ext a b. propext;
  cbv; intuition.
Qed.

Lemma tosubset_list_hom2 : forall (A B : Type) (f : A -> list B),
    tosubset ∘ bind f = bind (T := subset) (tosubset ∘ f) ∘ tosubset.
Proof.
  intros. unfold compose. ext l b.
  induction l.
  - propext; cbv.
    + intuition.
    + intros [a [absurd]]; contradiction.
  - autorewrite with tea_list tea_set.
    rewrite IHl.
    reflexivity.
Qed.

Lemma tosubset_list_map : forall (A B : Type) (f : A -> B),
    tosubset ∘ map f = map f ∘ tosubset.
Proof.
  intros.
  now rewrite <- (natural (ϕ := @tosubset list _)).
Qed.

#[export] Instance Monad_Hom_list_tosubset :
  MonadHom list subset (@tosubset list _) :=
  {| kmon_hom_ret := tosubset_list_hom1;
    kmon_hom_bind := tosubset_list_hom2;
  |}.

(** * Quantification over elements *)
(* TODO: There is no real purpose for this at this point is there? *)
(******************************************************************************)
Section quantification.

  Definition Forall_List `(P : A -> Prop) : list A -> Prop :=
    foldMap_list (op := Monoid_op_and) (unit := Monoid_unit_true) P.

  Definition Forany_List `(P : A -> Prop) : list A -> Prop :=
    foldMap_list (op := Monoid_op_or) (unit := Monoid_unit_false) P.

  Lemma forall_iff `(P : A -> Prop) (l : list A) :
    Forall_List P l <-> forall (a : A), a ∈ l -> P a.
  Proof.
    unfold Forall_List.
    induction l; autorewrite with tea_list tea_set.
    - split.
      + intros tt a contra. inversion contra.
      + intros. exact I.
    - setoid_rewrite element_of_list_cons.
      rewrite IHl. split.
      + intros [Hpa Hrest].
        intros x [Heq | Hin].
        now subst. auto.
      + intros H. split; auto.
  Qed.

  Lemma forany_iff `(P : A -> Prop) (l : list A) :
    Forany_List P l <-> exists (a : A), a ∈ l /\ P a.
  Proof.
    unfold Forany_List.
    induction l.
    - split.
      + intros [].
      + intros [x [contra Hrest]]. inversion contra.
    - autorewrite with tea_list tea_set.
      setoid_rewrite element_of_list_cons.
      unfold subset_one.
      rewrite IHl. split.
      + intros [Hpa | Hrest].
        exists a. auto.
        destruct Hrest as [x [H1 H2]].
        exists x. auto.
      + intros [x [[H1 | H2] H3]].
        subst. now left.
        right. eexists; eauto.
  Qed.

End quantification.

(** ** <<Element>> in terms of <<foldMap_list>> *)
(******************************************************************************)
Lemma element_to_foldMap_list1 : forall (A : Type),
    tosubset = foldMap_list (ret (T := subset) (A := A)).
Proof.
  intros. ext l. induction l.
  - reflexivity.
  - cbn. autorewrite with tea_list.
    rewrite IHl.
    reflexivity.
Qed.

Lemma element_to_foldMap_list2 : forall (A : Type) (l : list A) (a : A),
    tosubset l a = foldMap_list (op := or) (unit := False) (eq a) l.
Proof.
  intros. rewrite element_to_foldMap_list1.
  (*
    change_left ((evalAt a ∘ foldMap_list (ret (T := subset))) l).
   *)
  induction l.
  - reflexivity.
  - rewrite foldMap_list_cons.
    rewrite foldMap_list_cons.
    rewrite <- IHl.
    replace (a = a0) with (a0 = a) by (propext; auto).
    reflexivity.
Qed.

(** * Enumerating elements of listable functors *)
(******************************************************************************)
Section ToSubset_Tolist.
  #[local] Instance ToSubset_Tolist `{Tolist F} : ToSubset F :=
  fun A => tosubset ∘ tolist.
End ToSubset_Tolist.

Class Compat_ToSubset_Tolist
  (F : Type -> Type)
  `{H_tosubset : ToSubset F}
  `{H_tolist : Tolist F} : Prop :=
  compat_element_tolist :
    @tosubset F H_tosubset =
      @tosubset F (@ToSubset_Tolist F H_tolist).

Lemma tosubset_to_tolist `{Compat_ToSubset_Tolist F} :
  forall (A : Type),
    tosubset (F := F) (A := A) = tosubset (F := list) ∘ tolist.
Proof.
  now rewrite compat_element_tolist.
Qed.

Theorem in_iff_in_tolist `{Compat_ToSubset_Tolist F} :
  forall (A : Type) (t : F A) (a : A),
    a ∈ t <-> a ∈ tolist t.
Proof.
  intros. unfold element_of.
  now rewrite compat_element_tolist.
Qed.

#[export] Instance Natural_Element_Tolist :
  forall `{ShapelyFunctor F}, Natural (@tosubset F ToSubset_Tolist).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold tosubset, ToSubset_Tolist. ext t.
  reassociate <- on left. rewrite (natural (G := subset)).
  reassociate -> on left. now rewrite natural.
Qed.

(** * Shapely functors are container-like *)
(******************************************************************************)
Section ShapelyFunctor_setlike.

  Context
    `{ShapelyFunctor F}.

  Lemma shapeliness_iff :
    forall (A : Type) (t u : F A),
      t = u <-> shape t = shape u /\ tolist t = tolist u.
  Proof.
    intros. split.
    + intros; subst; auto.
    + apply (shp_shapeliness).
  Qed.

  Lemma shapely_map_eq_iff :
    forall (A B : Type) (t : F A) (f g : A -> B),
      map f t = map g t <->
      map f (tolist t) = map g (tolist t).
  Proof.
    intros.
    compose near t on right. rewrite 2(natural).
    unfold compose. split.
    - introv heq. now rewrite heq.
    - intros. apply (shp_shapeliness). rewrite 2(shape_map).
      auto.
  Qed.

  Context
    `{ToSubset F}
      `{! Compat_ToSubset_Tolist F}.

  Lemma compat_element_tolist_natural :
    `{Natural (@tosubset F _)}.
  Proof.
    constructor; try typeclasses eauto.
    intros.
    rewrite compat_element_tolist.
    rewrite (natural (Natural := Natural_Element_Tolist)).
    reflexivity.
  Qed.

  Theorem shapely_pointwise_iff :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) <-> map f t = map g t.
  Proof.
    introv.
    rewrite shapely_map_eq_iff.
    setoid_rewrite in_iff_in_tolist.
    rewrite map_rigidly_respectful_list.
    reflexivity.
  Qed.

  Corollary shapely_pointwise :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) -> map f t = map g t.
  Proof.
   introv. rewrite shapely_pointwise_iff. auto.
  Qed.

  #[export] Instance ContainerFunctor_Shapely :
    ContainerFunctor F :=
    {| cont_natural := compat_element_tolist_natural;
       cont_pointwise := shapely_pointwise; |}.

End ShapelyFunctor_setlike.

(** * Specification of <<Permutation>> *)
(******************************************************************************)
From Coq Require Import Sorting.Permutation.

Theorem permutation_spec : forall {A} {l1 l2 : list A},
    Permutation l1 l2 -> (forall a, a ∈ l1 <-> a ∈ l2).
Proof.
  introv perm. induction perm; firstorder.
Qed.


(** * SameSet *)

Inductive SameSetRight {A : Type} : list A -> list A -> Prop :=
| ssetr_nil : SameSetRight [] []
| ssetr_skip : forall (x : A) (l l' : list A), SameSetRight l l' -> SameSetRight (x :: l) (x :: l')
| ssetr_swap : forall (x y : A) (l : list A), SameSetRight (y :: x :: l) (x :: y :: l)
| ssetr_dup_r : forall (x : A) (l : list A), SameSetRight (x :: l) (x :: x :: l)
| ssetr_trans : forall l l' l'' : list A, SameSetRight l l' -> SameSetRight l' l'' -> SameSetRight l l''.


Inductive SameSet {A : Type} : list A -> list A -> Prop :=
| sset_nil : SameSet [] []
| sset_skip : forall (x : A) (l l' : list A), SameSet l l' -> SameSet (x :: l) (x :: l')
| sset_swap : forall (x y : A) (l : list A), SameSet (y :: x :: l) (x :: y :: l)
| sset_dup_r : forall (x : A) (l : list A), SameSet (x :: l) (x :: x :: l)
| sset_dup_l : forall (x : A) (l : list A), SameSet (x :: x :: l) (x :: l)
| sset_trans : forall l l' l'' : list A, SameSet l l' -> SameSet l' l'' -> SameSet l l''.

From Tealeaves Require Import Classes.EqDec_eq.

Lemma sameset_refl: forall (A: Type) (l: list A),
    SameSet l l.
Proof.
  intros. induction l.
  - apply sset_nil.
  - apply sset_skip.
    assumption.
Qed.

Lemma sameset_nil: forall (A: Type) (l: list A),
    SameSet [] l -> l = [].
Proof.
  intros. remember [] as l'.
  induction H; subst; try solve [inversion Heql'].
  - reflexivity.
  - specialize (IHSameSet1 ltac:(reflexivity)).
    subst. auto.
Qed.

Lemma sametset_dup_right: forall (A: Type) (a: A) (l: list A),
    SameSet (a :: l) (a :: a :: l).
Proof.
  intros. apply sset_dup_r.
Qed.

Example ex1: forall (A: Type) (a: A),
    SameSet [a; a] [a].
Proof.
  intros. apply sset_dup_l.
Qed.

Lemma sameset_sym: forall (A: Type) (l l': list A),
    SameSet l l' -> SameSet l' l.
Proof.
  intros. induction H.
  - apply sset_nil.
  - apply sset_skip. auto.
  - apply sset_swap.
  - apply sset_dup_l.
  - apply sset_dup_r.
  - eapply sset_trans; eauto.
Qed.

Lemma sameset_spec_one: forall (A: Type) `{EqDec_eq A} (l: list A) (a: A),
  (forall (a0 : A), a0 ∈ l <-> a0 = a) -> SameSet [a] l.
Proof.
  introv Heq Hsame. induction l.
  - specialize (Hsame a).
    autorewrite with tea_list in Hsame. tauto.
  - assert (a0 = a).
    { apply (Hsame a0). now left. }
    subst; clear Hsame.
    destruct l.
    + apply sameset_refl.
    + destruct_eq_args a a0.
      * admit.
      * admit.
Abort.

Theorem sameset_spec : forall {A} `{EqDec_eq A} {l1 l2 : list A},
    (forall a, a ∈ l1 <-> a ∈ l2) -> SameSet l1 l2.
Proof.
  introv Heqdec Hsame.
  assert (Hsame1: forall a : A, a ∈ l1 -> a ∈ l2).
  { intro a. apply Hsame. }
  assert (Hsame2: forall a : A, a ∈ l2 -> a ∈ l1).
  { intro a. apply Hsame. }
  clear Hsame.
  generalize dependent l2.
  induction l1; intros l2 Hsame1 Hsame2.
  - induction l2.
    + apply sset_nil.
    + false.
      apply (Hsame2 a).
      now left.
  - destruct l1.
    + clear IHl1.
Abort.

(** * Misc *)
(******************************************************************************)
Lemma map_preserve_length:
  forall (A B: Type) (f: A -> B) (l: list A),
    length (map f l) = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - cbn.
    rewrite <- IHl.
    reflexivity.
Qed.

Definition decide_length {A}: forall (n: nat) (l: list A),
    {length l = n} + { length l = n -> False}.
Proof.
  intros.
  remember (Nat.eqb (length l) n) as b.
  symmetry in Heqb.
  destruct b.
  - left.
    apply (PeanoNat.Nat.eqb_eq (length l) n).
    assumption.
  - right.
    apply (PeanoNat.Nat.eqb_neq (length l) n).
    assumption.
Defined.

(** * Un-con-sing non-empty lists *)
(******************************************************************************)
Lemma S_uncons {n m}: S n = S m -> n = m.
Proof.
  now inversion 1.
Defined.

Definition zero_not_S {n} {anything}:
  0 = S n -> anything :=
  fun pf => match pf with
         | eq_refl =>
             let false : False :=
               eq_ind 0 (fun e : nat => match e with
                           | 0 => True
                           | S _ => False
                           end) I (S n) pf
             in (False_rect anything false)
         end.

Lemma list_uncons_exists:
  forall (A: Type) (n: nat)
    (v: list A) (vlen: length v = S n),
    exists (a: A) (v': list A),
    v = cons a v'.
Proof.
  intros.
  destruct v.
  - inversion vlen.
  - exists a v. reflexivity.
Qed.

Definition list_uncons {n A} (l: list A) (vlen: length l = S n):
  A * list A :=
  match l return (length l = S n -> A * list A) with
  | nil => zero_not_S
  | cons a rest => fun vlen => (a, rest)
  end vlen.

Definition list_uncons_sigma {n A} (l: list A) (vlen: length l = S n):
  A * {l : list A | length l = n} :=
  match l return (length l = S n -> A * {l: list A | length l = n}) with
  | nil => zero_not_S
  | cons hd tl => fun vlen => (hd, exist _ tl (S_uncons vlen))
  end vlen.

Definition list_uncons_sigma2 {n A} (l: list A) (vlen: length l = S n):
  {p: A * list A | l = uncurry cons p} :=
  match l return (length l = S n -> {p: A * list A | l = uncurry cons p}) with
  | nil => zero_not_S
  | cons hd tl => fun vlen => exist _ (hd, tl) eq_refl
  end vlen.

(** ** Total list head and tail functions for non-empty lists *)
(******************************************************************************)
Definition list_hd {n A} :=
  fun (l: list A) (vlen: length l = S n) =>
  fst (list_uncons l vlen).

Definition list_tl {n A} :=
  fun (l: list A) (vlen: length l = S n) =>
    snd (list_uncons l vlen).

(** *** Proof independence and rewriting laws *)
(******************************************************************************)
Lemma list_hd_proof_irrelevance
        {n m A}
        (l: list A)
        (vlen1: length l = S n)
        (vlen2: length l = S m):
  list_hd l vlen1 = list_hd l vlen2.
Proof.
  induction l.
  - inversion vlen1.
  - reflexivity.
Qed.

Lemma list_tl_proof_irrelevance
        {n m A}
        (l: list A)
        (vlen1: length l = S n)
        (vlen2: length l = S m):
  list_tl l vlen1 = list_tl l vlen2.
Proof.
  induction l.
  - inversion vlen1.
  - reflexivity.
Qed.

(** Rewrite a [list_hd] subterm by pushing a type coercion into the
    length proof *)
Lemma list_hd_rw
        {n A}
        {l1 l2: list A}
        (Heq: l1 = l2)
        {vlen: length l1 = S n}:
  list_hd l1 vlen = list_hd l2 (rew [fun l1 => length l1 = S n] Heq in vlen).
Proof.
  subst.
  apply list_hd_proof_irrelevance.
Qed.

(** Rewrite a [list_tl] subterm by pushing a type coercion into the
    length proof *)
Lemma list_tl_rw
        {n A}
        {l1 l2: list A}
        (Heq: l1 = l2)
        {vlen: length l1 = S n}:
  list_tl l1 vlen = list_tl l2 (rew [fun l1 => length l1 = S n] Heq in vlen).
Proof.
  subst.
  apply list_tl_proof_irrelevance.
Qed.

Lemma list_tl_length {n} `(l: list A) (vlen: length l = S n):
  length (list_tl l vlen) = n.
Proof.
  destruct l.
  - inversion vlen.
  - cbn. now inversion vlen.
Qed.

(** *** Surjective pairing properties *)
(******************************************************************************)
Lemma list_surjective_pairing {n} `(l: list A) `(vlen: length l = S n):
  list_uncons l vlen = (list_hd l vlen, list_tl l vlen).
Proof.
  destruct l.
  - inversion vlen.
  - reflexivity.
Qed.

Lemma list_surjective_pairing2 {n} `(l: list A) `(vlen: length l = S n):
  l = cons (list_hd l vlen) (list_tl l vlen).
Proof.
  destruct l.
  - inversion vlen.
  - reflexivity.
Qed.
