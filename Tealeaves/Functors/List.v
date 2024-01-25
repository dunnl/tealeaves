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

Lemma list_bind_compat : forall (A B : Type),
    bind =
      @TraversableMonad.MakeFull.Bind_Bindt list _ A B.
Proof.
  intros. ext f l. induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

Lemma list_traverse_compat :
  forall (G : Type -> Type) `{Mult G} `{Map G} `{Pure G}
    `{! Applicative G} (A B : Type) (f : A -> G B),
    traverse f =
      @TraversableMonad.MakeFull.Traverse_Bindt list _ _ G _ _ _ A B f.
Proof.
  intros. ext l. induction l as [| a rest IHrest].
  - reflexivity.
  - cbn. rewrite IHrest.
    unfold compose at 1.
    rewrite pure_ap_map.
    rewrite map_to_ap.
    reflexivity.
Qed.

Lemma list_map_compat : forall (A B : Type) (f : A -> B),
    map (F := list) f =
      @TraversableMonad.MakeFull.Map_Bindt list _ _ A B f.
Proof.
  intros. ext l. induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

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
      now rewrite List.app_assoc.
  Qed.

End bindt_rewriting_lemmas.

#[export] Hint Rewrite bindt_list_nil bindt_list_cons bindt_list_one bindt_list_app :
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

#[export] Instance TM_list : TraversableMonad list :=
  {| ktm_bindt0 := list_bindt0;
    ktm_bindt1 := list_bindt1;
    ktm_bindt2 := @list_bindt2;
    ktm_morph := @list_morph;
  |}.

(** ** Derived typeclass instances *)
(******************************************************************************)
#[program, export]
  Instance TraversableMonadFull_list : TraversableMonadFull list :=
  {| ktmf_map_to_bindt := list_map_compat;
    ktmf_bind_to_bindt := @list_bind_compat;
    ktmf_traverse_to_bindt := @list_traverse_compat;
  |}.

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

(** ** <<foldMap>> *)
(******************************************************************************)
Definition foldMap {M : Type} `{op : Monoid_op M} `{unit : Monoid_unit M}
  {A : Type} (f : A -> M) : list A -> M :=
  fold M ∘ map f.

(** <<foldMap>> is a monoid homomorphism *)
#[export] Instance Monoid_Morphism_foldMap
  `{Monoid M} {A : Type}
  `(f : A -> M) : Monoid_Morphism (list A) M (foldMap f).
Proof.
  unfold foldMap.
  eapply Monoid_Morphism_compose;
    typeclasses eauto.
Qed.

(** <<foldMap>> commutes with monoid homomorphisms *)
Lemma foldMap_morphism `{Monoid_Morphism M1 M2 ϕ}
  : forall `(f : A -> M1),
    ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
Proof.
  intros. unfold foldMap.
  reassociate <- on left.
  rewrite (fold_mon_hom ϕ).
  reassociate -> on left.
  rewrite fun_map_map.
  reflexivity.
Qed.

(** *** Rewriting with <<foldMap>> *)
(******************************************************************************)
Section foldMap_list_rw.

  Context
    {A M : Type}
    `{Monoid M}
    (f : A -> M).

  Lemma foldMap_list_nil : foldMap f (@nil A) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_list_cons : forall (x : A) (xs : list A),
      foldMap f (x :: xs) = f x ● foldMap f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_list_one (a : A) : foldMap f [ a ] = f a.
  Proof.
    cbv. apply monoid_id_l.
  Qed.

  Lemma foldMap_list_ret : foldMap f ∘ ret = f.
  Proof.
    ext a; cbn. apply monoid_id_l.
  Qed.

  Lemma foldMap_list_app : forall (l1 l2 : list A),
      foldMap f (l1 ++ l2) = foldMap f l1 ● foldMap f l2.
  Proof.
    intros.
    unfold foldMap.
    unfold compose. autorewrite with tea_list.
    rewrite (fold_app M).
    reflexivity.
  Qed.

End foldMap_list_rw.

#[export] Hint Rewrite @foldMap_list_nil @foldMap_list_cons
  @foldMap_list_one @foldMap_list_app : tea_list.

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
#[export] Instance Elements_list : Elements list :=
  fun (A : Type) (l : list A) => (fun a : A => @List.In A a l).

(** ** <<element_of>> and rewriting principles *)
(******************************************************************************)
Lemma elements_list_nil : forall (A : Type),
    element_of (@nil A) = ∅.
Proof.
  intros. extensionality a. reflexivity.
Qed.

Lemma elements_list_one : forall (A : Type) (a : A),
    element_of [a] = {{ a }}.
Proof.
  intros. solve_basic_subset.
Qed.

Lemma elements_list_ret : forall (A : Type) (a : A),
    element_of (ret a) = {{ a }}.
Proof.
  intros. solve_basic_subset.
Qed.

Lemma elements_list_cons :
  forall (A : Type) (a : A) (l : list A),
    element_of (a :: l) = {{ a }} ∪ element_of l.
Proof.
  intros. extensionality a'. reflexivity.
Qed.

Lemma elements_list_app : forall (A : Type) (l1 l2 : list A),
    element_of (l1 ++ l2) = element_of l1 ∪ element_of l2.
Proof.
  intros. induction l1.
  - cbn. rewrite elements_list_nil.
    solve_basic_subset.
  - cbn.
    do 2 rewrite elements_list_cons.
    rewrite IHl1. solve_basic_subset.
Qed.

#[export] Hint Rewrite
  elements_list_nil elements_list_one elements_list_ret
  elements_list_cons elements_list_app : tea_list.

(** ** Naturality of <<element_of>> *)
(******************************************************************************)
#[export] Instance Natural_Elements_list : Natural (@element_of list _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. ext l.
  unfold compose at 1 2.
  induction l.
  - solve_basic_subset.
  - rewrite elements_list_cons.
    autorewrite with tea_set tea_list.
    rewrite IHl.
    solve_basic_subset.
Qed.

(** ** [element_of] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monoid_Morphism_elements_list (A : Type) :
  Monoid_Morphism (list A) (subset A) (element_of (A := A)) :=
  {| monmor_unit := @elements_list_nil A;
    monmor_op := @elements_list_app A;
  |}.

(** ** <<∈>> for lists *)
(******************************************************************************)
Lemma in_list_nil {A} : forall (p : A), p ∈ @nil A <-> False.
Proof.
  reflexivity.
Qed.

Lemma in_list_cons {A} : forall (a1 a2 : A) (xs : list A),
    a1 ∈ (a2 :: xs) <-> a1 = a2 \/ a1 ∈ xs.
Proof.
  intros; simpl_list; simpl_subset.
  intuition congruence.
Qed.

Lemma in_list_one {A} (a1 a2 : A) : a1 ∈ [ a2 ] <-> a1 = a2.
Proof.
  intros. simpl_list. simpl_subset. intuition congruence.
Qed.

Lemma in_list_ret {A} (a1 a2 : A) : a1 ∈ ret a2 <-> a1 = a2.
Proof.
  intros. simpl_list; simpl_subset. intuition.
Qed.

Lemma in_list_app {A} : forall (a : A) (xs ys : list A),
    a ∈ (xs ++ ys) <-> a ∈ xs \/ a ∈ ys.
Proof.
  intros. simpl_list. simpl_subset. reflexivity.
Qed.

#[export] Hint Rewrite @in_list_nil @in_list_cons
  @in_list_one @in_list_ret @in_list_app : tea_list.

(** *** [x ∈] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monoid_Morphism_element_list (A : Type) (a : A) :
  Monoid_Morphism (list A) Prop (tgt_op := or) (tgt_unit := False)
    (fun l => element_of l a).
Proof.
  change (fun l => element_of l a) with
    (evalAt a ∘ element_of).
  eapply Monoid_Morphism_compose;
    typeclasses eauto.
Qed.

(** ** Respectfulness conditions *)
(******************************************************************************)
Theorem map_rigidly_respectful_list : forall A B (f g : A -> B) (l : list A),
    (forall (a : A), a ∈ l -> f a = g a) <-> map f l = map g l.
Proof.
  intros. induction l.
  - simpl_list. setoid_rewrite subset_in_empty. tauto.
  - simpl_list. setoid_rewrite subset_in_add.
    setoid_rewrite set_in_ret.
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

(** ** <<element_of>> as a monad homomorphism *)
(******************************************************************************)
Lemma element_of_list_hom1 : forall (A : Type),
    element_of ∘ ret (A := A) = ret (T := subset).
Proof.
  intros.
  ext a b. propext;
  cbv; intuition.
Qed.

Lemma element_of_list_hom2 : forall (A B : Type) (f : A -> list B),
    element_of ∘ bind f = bind (T := subset) (element_of ∘ f) ∘ element_of.
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

Lemma element_of_list_map : forall (A B : Type) (f : A -> B),
    element_of ∘ map f = map f ∘ element_of.
Proof.
  intros.
  now rewrite <- (natural (ϕ := @element_of list _)).
Qed.

#[export] Instance Monad_Hom_list_elements :
  MonadHom list subset (@element_of list _) :=
  {| kmon_hom_ret := element_of_list_hom1;
    kmon_hom_bind := element_of_list_hom2;
  |}.

(** * Quantification over elements *)
(* TODO: There is no real purpose for this at this point is there? *)
(******************************************************************************)
Section quantification.

  Definition Forall_List `(P : A -> Prop) : list A -> Prop :=
    foldMap (op := Monoid_op_and) (unit := Monoid_unit_true) P.

  Definition Forany_List `(P : A -> Prop) : list A -> Prop :=
    foldMap (op := Monoid_op_or) (unit := Monoid_unit_false) P.

  Lemma forall_iff `(P : A -> Prop) (l : list A) :
    Forall_List P l <-> forall (a : A), a ∈ l -> P a.
  Proof.
    unfold Forall_List.
    induction l; autorewrite with tea_list tea_set.
    - split.
      + intros tt a contra. inversion contra.
      + intros. exact I.
    - setoid_rewrite subset_in_add.
      unfold subset_one.
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
      setoid_rewrite subset_in_add.
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

(** ** <<Element>> in terms of <<foldMap>> *)
(******************************************************************************)
Lemma element_to_foldMap1 : forall (A : Type),
    element_of = foldMap (ret (T := subset) (A := A)).
Proof.
  intros. ext l. induction l.
  - reflexivity.
  - cbn. autorewrite with tea_list.
    rewrite IHl.
    reflexivity.
Qed.

Lemma element_to_foldMap2 : forall (A : Type) (l : list A) (a : A),
    element_of l a = foldMap (op := or) (unit := False) (eq a) l.
Proof.
  intros. rewrite element_to_foldMap1.
  (*
    change_left ((evalAt a ∘ foldMap (ret (T := subset))) l).
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
Section element_of_via_tolist.

  Context
    `{Functor F}
    `{Tolist F}
    `{! Natural (@tolist F _)}.

  #[export] Instance Elements_Tolist `{Tolist F} : Elements F :=
    fun A => element_of ∘ tolist.

  #[export] Instance Natural_Element_Tolist:
    forall `{ShapelyFunctor F}, Natural (@element_of F _).
  Proof.
    constructor; try typeclasses eauto.
    intros A B f. unfold element_of, Elements_Tolist. ext t.
    reassociate <- on left. rewrite (natural (G := subset)).
    reassociate -> on left. now rewrite natural.
  Qed.

  Theorem in_iff_in_list `{Tolist F} : forall (A : Type) (t : F A) (a : A),
      a ∈ t <-> a ∈ tolist t.
  Proof.
    reflexivity.
  Qed.

End element_of_via_tolist.

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

  Theorem shapely_pointwise_iff :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) <-> map f t = map g t.
  Proof.
    introv.
    rewrite shapely_map_eq_iff.
    setoid_rewrite in_iff_in_list.
    rewrite map_rigidly_respectful_list.
    reflexivity.
  Qed.

  Corollary shapely_pointwise :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) -> map f t = map g t.
  Proof.
   introv. rewrite shapely_pointwise_iff. auto.
 Qed.

  #[export] Instance ContainerFunctor_Shapely : ContainerFunctor F :=
    {| cont_pointwise := shapely_pointwise; |}.

  Corollary shapely_map_id_iff :
    forall (A : Type) (t : F A) (f : A -> A),
      (forall (a : A), a ∈ t -> f a = a) <-> map f t = t.
  Proof.
    intros.
    replace t with (map id t) at 2
      by now rewrite (fun_map_id (F := F)).
    now rewrite shapely_pointwise_iff.
  Qed.

End ShapelyFunctor_setlike.

(** * Specification of <<Permutation>> *)
(******************************************************************************)
From Coq Require Import Sorting.Permutation.

Theorem permutation_spec : forall {A} {l1 l2 : list A},
    Permutation l1 l2 -> (forall a, a ∈ l1 <-> a ∈ l2).
Proof.
  introv perm. induction perm; firstorder.
Qed.
