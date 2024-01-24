From Tealeaves Require Export
  Classes.Categorical.Monad
  Classes.Kleisli.TraversableMonad
  Functors.Subset
  Misc.List.

Import TraversableMonad.Notations.
Import List.ListNotations.
Import Monoid.Notations.
Import Subset.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables M A B G ϕ.

(** * Automation: <<simpl_list>> *)
(******************************************************************************)
Create HintDb tea_list.
Tactic Notation "simpl_list" := (autorewrite with tea_list).
Tactic Notation "simpl_list" "in" hyp(H) := (autorewrite with tea_list H).
Tactic Notation "simpl_list" "in" "*" := (autorewrite with tea_list in *).

(** * The [list] monad, categorically *)
(******************************************************************************)

(** ** [Functor] instance *)
(******************************************************************************)
#[export] Instance Map_list : Map list :=
  fun A B => @List.map A B.

(** *** Rewriting lemmas for <<map>> *)
(******************************************************************************)
Section map_list_rw.

  Context
    {A B : Type}
    (f : A -> B).

  Lemma map_list_nil : map f (@nil A) = @nil B.
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_cons : forall (x : A) (xs : list A),
      map f (x :: xs) = f x :: map f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_one (a : A) : map f [ a ] = [f a].
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_app : forall (l1 l2 : list A),
      map f (l1 ++ l2) = map f l1 ++ map f l2.
  Proof.
    intros.
    unfold transparent tcs.
    now rewrites List.map_app.
  Qed.

End map_list_rw.

#[export] Hint Rewrite @map_list_nil @map_list_cons
     @map_list_one @map_list_app : tea_list.

(** *** Functor laws *)
(******************************************************************************)
Theorem map_id_list {A} : map (F := list) (@id A) = id.
Proof.
  ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

Theorem map_map_list {A B C} : forall (f : A -> B) (g : B -> C),
    map g ∘ map f = map (F := list) (g ∘ f).
Proof.
  intros. unfold compose. ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

#[export] Instance Functor_list : Functor list :=
  {| fun_map_id := @map_id_list;
     fun_map_map := @map_map_list;
  |}.

(** ** Monad instance *)
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
      @TraversableMonad.DerivedOperations.Bind_Bindt list _ A B.
Proof.
  intros. ext f l. induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

Lemma list_traverse_compat :
  forall (G : Type -> Type) `{Mult G} `{Map G} `{Pure G}
    `{! Applicative G} (A B : Type) (f : A -> G B),
    traverse f =
      @TraversableMonad.DerivedOperations.Traverse_Bindt list _ _ G _ _ _ A B f.
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
      @TraversableMonad.DerivedOperations.Map_Bindt list _ _ A B f.
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

  About kc3.
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

(** * The [shape] operation *)
(******************************************************************************)
Definition shape `{Map F} {A : Type} : F A -> F unit :=
  map (const tt).

(** ** Basic reasoning principles for <<shape>> *)
(******************************************************************************)
Theorem shape_map `{Functor F} : forall (A B : Type) (f : A -> B) (t : F A),
    shape (F := F) (map f t) =
      shape (F := F) t.
Proof.
  intros. compose near t on left.
  unfold shape. now rewrite fun_map_map.
Qed.

Theorem shape_shape `{Functor F} : forall (A : Type) (t : F A),
    shape (shape t) = shape t.
Proof.
  intros.  compose near t on left.
  unfold shape. now rewrite fun_map_map.
Qed.


Lemma shape_map_eq `{Functor F} : forall (A1 A2 B : Type) (f : A1 -> B) (g : A2 -> B) t u,
    map f t = map g u -> shape t = shape u.
Proof.

  introv hyp. cut (shape (map f t) = shape (map g u)).
  - now rewrite 2(shape_map).
  - now rewrite hyp.
Qed.

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

(** * Tolist operation *)
(******************************************************************************)
Import Classes.Functor.Notations.

Class Tolist (F : Type -> Type) :=
  tolist : F ⇒ list.

Class Tolist_ctx (F : Type -> Type) (W : Type) :=
  tolist_ctx : forall (A : Type), F A -> list (W * A).

#[global] Arguments tolist {F}%function_scope {Tolist} {A}%type_scope _.
