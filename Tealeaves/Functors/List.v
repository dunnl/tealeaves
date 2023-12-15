From Tealeaves Require Export
  Classes.Categorical.Monad
  Classes.Kleisli.TraversableMonad
  Functors.Subset
  Misc.List.

Import List.ListNotations.
Import Monoid.Notations.
Import Subset.Notations.
Import Applicative.Notations.

#[local] Generalizable Variables M A B G ϕ.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.
#[local] Arguments ret T%function_scope {Return} (A)%type_scope _.
#[local] Arguments pure F%function_scope {Pure} {A}%type_scope _.
#[local] Arguments mult F%function_scope {Mult} {A B}%type_scope _.
#[local] Arguments bindt {U} (T)%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

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

  Lemma map_list_nil : map list f (@nil A) = @nil B.
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_cons : forall (x : A) (xs : list A),
      map list f (x :: xs) = f x :: map list f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_one (a : A) : map list f [ a ] = [f a].
  Proof.
    reflexivity.
  Qed.

  Lemma map_list_app : forall (l1 l2 : list A),
      map list f (l1 ++ l2) = map list f l1 ++ map list f l2.
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
Theorem map_id_list {A} : map list (@id A) = id.
Proof.
  ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

Theorem map_map_list {A B C} : forall (f : A -> B) (g : B -> C),
    map list g ∘ map list f = map list (g ∘ f).
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
  `(join list ([ ] : list (list A)) = []).
Proof.
  reflexivity.
Qed.

Lemma join_list_cons : forall A (l : list A) (ll : list (list A)),
    join list (l :: ll) = l ++ join list ll.
Proof.
  reflexivity.
Qed.

Lemma join_list_one : forall A (l : list A),
    join list [ l ] = l.
Proof.
  intros. cbn. now List.simpl_list.
Qed.

Lemma join_list_app : forall A (l1 l2 : list (list A)),
    join list (l1 ++ l2) = join list l1 ++ join list l2.
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
  join list ∘ ret list (list A) = @id (list A).
Proof.
  ext l. unfold compose. destruct l.
  - reflexivity.
  - cbn. now List.simpl_list.
Qed.

Theorem join_map_ret_list {A} :
  join list ∘ map list (ret list A) = @id (list A).
Proof.
  ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

Theorem join_join_list {A} :
  join list ∘ join list (A:=list A) =
  join list ∘ map list (join list).
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
  | nil => pure G (@nil B)
  | x :: xs =>
      pure G (@List.app B) <⋆> f x <⋆> bindt_list G A B f xs
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
  | nil => pure G (@nil B)
  | x :: xs =>
      pure G (@List.cons B) <⋆> f x <⋆> (traverse_list G A B f xs)
  end.

#[export] Instance Bindt_list : Bindt list list := @bindt_list.
#[export] Instance Bind_list : Bind list list := @bind_list.
#[export] Instance Traverse_list : Traverse list := @traverse_list.

Lemma list_bind_compat : forall (A B : Type),
    bind = @TraversableMonad.DerivedOperations.Bind_Bindt list _ A B.
Proof.
  intros. ext f l. induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

Lemma list_traverse_compat : forall (G : Type -> Type) `{Mult G} `{Map G} `{Pure G} `{! Applicative G} (A B : Type) (f : A -> G B),
    traverse f = @TraversableMonad.DerivedOperations.Traverse_Bindt list _ _ G _ _ _ A B f.
Proof.
  intros. ext l. induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. rewrite IHrest.
    unfold compose at 1.
    rewrite pure_ap_map.
    rewrite map_to_ap.
    reflexivity.
Qed.

Lemma list_map_compat : forall (A B : Type) (f : A -> B),
    map list f = @TraversableMonad.DerivedOperations.Map_Bindt list _ _ A B f.
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
      bindt list G A B f (@nil A) = pure G (@nil B).
  Proof.
    reflexivity.
  Qed.

  Lemma bindt_list_one : forall (f : A -> G (list B)) (a : A),
      bindt list G A B f (ret list A a) = f a.
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
      bindt list G A B f (cons a l) =
        pure G (@app B) <⋆> f a <⋆> bindt list G A B f l.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma bindt_list_app : forall (f : A -> G (list B)) (l1 l2 : list A),
      bindt list G A B f (l1 ++ l2) =
        pure G (@app B) <⋆> (bindt list G A B f l1) <⋆> (bindt list G A B f l2).
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
      now rewrite (List.app_assoc).
  Qed.

End bindt_rewriting_lemmas.

(** ** Traversable monad instance *)
(******************************************************************************)
Section bindt_laws.

  Context
    (G : Type -> Type)
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    (A B C : Type).

  Lemma list_bindt0 : forall (f : A -> G (list B)), bindt list G A B f ∘ ret list A = f.
  Proof.
    intros. ext a.
    apply (bindt_list_one G).
  Qed.

  Lemma list_bindt1 : bindt (U := list) list (fun A => A) A A (ret list A) = id.
  Proof.
    ext l. induction l.
    - reflexivity.
    - cbn. rewrite IHl.
      reflexivity.
  Qed.

  Lemma list_bindt2 :
    forall (g : B -> G2 (list C)) (f : A -> G1 (list B)),
      map G1 (bindt list G2 B C g) ∘ bindt list G1 A B f =
        bindt list (G1 ∘ G2) A C (kc3 g f).
  Proof.
    intros. ext l. induction l.
    - unfold compose; cbn.
      rewrite (app_pure_natural).
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
      repeat rewrite ap2.
      unfold kc3.
      unfold compose at 8.
      rewrite map_to_ap.
      rewrite <- ap4.
      repeat rewrite ap2.
      rewrite ap3.
      rewrite <- ap4.
      repeat rewrite ap2.
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
    ϕ (list B) ∘ bindt list G1 A B f = bindt list G2 A B (ϕ (list B) ∘ f).
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

#[export] Hint Rewrite bindt_list_nil bindt_list_cons bindt_list_one bindt_list_app :
  tea_list.

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
  Monoid_Morphism (list A) (list B) (map list f) :=
  {| monmor_op := map_list_app f; |}.

(** *** [join] is a monoid homomorphism *)
(** The <<join>> operation is a monoid homomorphism from <<list (list A)>> to
    <<list A>>. This is just a special case of the fact that monoid homomorphisms
    on free monoids are precisely of the form <<foldMap f>> for any <<f : A -> M>>,
    specialized to <<f = id>> case, but we don't need that much generality. *)
(******************************************************************************)
#[export] Instance Monmor_join (A : Type) :
  Monoid_Morphism (list (list A)) (list A) (join list (A := A)) :=
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
    ϕ ∘ fold M1 = fold M2 ∘ map list ϕ.
Proof.
  intros ? ? ϕ ? ? ? ? ?. unfold compose. ext l.
  induction l as [| ? ? IHl].
  - cbn. apply monmor_unit.
  - cbn. now rewrite (monmor_op (ϕ := ϕ)), IHl.
Qed.

(** In the special case that we fold a list of lists, the result is equivalent
    to joining the list of lists. *)
Lemma fold_equal_join : forall {A},
    fold (list A) = join list (A:=A).
Proof.
  intros. ext l. induction l as [| ? ? IHl].
  - reflexivity.
  - cbn. now rewrite IHl.
Qed.

(** ** <<foldMap>> *)
(******************************************************************************)
Definition foldMap {M : Type} `{op : Monoid_op M} `{unit : Monoid_unit M}
  {A : Type} (f : A -> M) : list A -> M :=
  fold M ∘ map list f.

(** <<foldMap>> is a monoid homomorphism *)
#[export] Instance foldMap_list_morphism
  `{Monoid M} {A : Type}
  `(f : A -> M) : Monoid_Morphism (list A) M (foldMap f).
Proof.
  unfold foldMap.
  eapply Monoid_Morphism_compose;
    typeclasses eauto.
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
      fold M (ret list _ x : list M) = x.
  Proof.
    apply monoid_id_l.
  Qed.

  Lemma fold_join : forall (l : list (list M)),
      fold _ (join list l) = fold _ (map list (fold _) l).
  Proof.
    intro l. rewrite <- fold_equal_join.
    compose near l on left.
    now rewrite (fold_mon_hom (fold _)).
  Qed.

  Lemma fold_constant_unit : forall (l : list M),
      fold M (map list (fun _ => Ƶ) l) = Ƶ.
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
    map list f (l1 ++ l2) = map list g (l1 ++ l2) ->
    map list f l1 = map list g l1.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl_list in *. rewrite IHl1.
    + fequal. simpl in H. inversion H; auto.
    + simpl in H. inversion H. auto.
Qed.

Lemma map_app_inv_r : forall {A B} {f g : A -> B} (l1 l2 : list A),
    map list f (l1 ++ l2) = map list g (l1 ++ l2) ->
    map list f l2 = map list g l2.
Proof.
  intros.
  assert (heads_equal : map list f l1 = map list g l1).
  { eauto using map_app_inv_l. }
  simpl_list in *.
  rewrite heads_equal in H.
  eauto using List.app_inv_head.
Qed.

Lemma map_app_inv : forall {A B} {f g : A -> B} (l1 l2 : list A),
    map list f (l1 ++ l2) = map list g (l1 ++ l2) ->
    map list f l1 = map list g l1 /\ map list f l2 = map list g l2.
Proof.
  intros; split; eauto using map_app_inv_l, map_app_inv_r.
Qed.

#[local] Generalizable Variable F.

(** * The [shape] operation *)
(******************************************************************************)
Definition shape (F : Type -> Type) `{Map F} {A} : F A -> F unit :=
  map F (const tt).

(** ** Basic reasoning principles for <<shape>> *)
(******************************************************************************)
Theorem shape_map `{Functor F} : forall (A B : Type) (f : A -> B) (t : F A),
    shape F (map F f t) = shape F t.
Proof.
  intros. compose near t on left.
  unfold shape. now rewrite fun_map_map.
Qed.

Theorem shape_shape `{Functor F} : forall A (t : F A),
    shape F (shape F t) = shape F t.
Proof.
  intros.  compose near t on left.
  unfold shape. now rewrite fun_map_map.
Qed.

Lemma shape_map_eq `{Functor F} : forall A1 A2 B (f : A1 -> B) (g : A2 -> B) t u,
    map F f t = map F g u -> shape F t = shape F u.
Proof.
  introv hyp. cut (shape F (map F f t) = shape F (map F g u)).
  - now rewrite 2(shape_map).
  - now rewrite hyp.
Qed.

(** ** Rewriting [shape] on lists *)
(******************************************************************************)
Section list_shape_rewrite.

  Lemma shape_nil : forall A,
      shape list (@nil A) = @nil unit.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_cons : forall A (a : A) (l : list A),
      shape list (a :: l) = tt :: shape list l.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_one : forall A (a : A),
      shape list [ a ] = [ tt ].
  Proof.
    reflexivity.
  Qed.

  Lemma shape_app : forall A (l1 l2 : list A),
      shape list (l1 ++ l2) = shape list l1 ++ shape list l2.
  Proof.
    intros. unfold shape. now rewrite map_list_app.
  Qed.

  Lemma shape_nil_iff : forall A (l : list A),
      shape list l = @nil unit <-> l = [].
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
      shape list l1 = shape list l2 <->
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
      shape list r1 = shape list r2 ->
      (shape list (l1 ++ r1) = shape list (l2 ++ r2) <->
       shape list l1 = shape list l2).
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split. intros; eauto using List.app_inv_tail.
    intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_eq_app_l : forall A (l1 l2 r1 r2: list A),
      shape list l1 = shape list l2 ->
      (shape list (l1 ++ r1) = shape list (l2 ++ r2) <->
       shape list r1 = shape list r2).
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split. intros; eauto using List.app_inv_head.
    intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_eq_cons_iff : forall A (l1 l2 : list A) (x y : A),
      shape list (x :: l1) = shape list (y :: l2) <->
      shape list l1 = shape list l2.
  Proof.
    intros. rewrite 2(shape_cons).
    split; intros hyp. now inverts hyp.
    now rewrite hyp.
  Qed.

  Theorem inv_app_eq_ll : forall A (l1 l2 r1 r2 : list A),
      shape list l1 = shape list l2 ->
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
      shape list r1 = shape list r2 ->
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
      shape list l1 = shape list l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eauto using List.app_inv_head. }
    { eauto using inv_app_eq_ll. }
  Qed.

  Theorem inv_app_eq_rr : forall A (l1 l2 r1 r2 : list A),
      shape list r1 = shape list r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eauto using List.app_inv_head. }
    { eauto using inv_app_eq_rl. }
  Qed.

  Theorem inv_app_eq : forall A (l1 l2 r1 r2 : list A),
      shape list l1 = shape list l2 \/ shape list r1 = shape list r2 ->
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
      l1 ++ ret list A a1 = l2 ++ ret list A a2 ->
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

#[global] Arguments tolist F%function_scope {Tolist} {A}%type_scope _.
