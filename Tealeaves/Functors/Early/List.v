From Tealeaves Require Export
  Classes.Functor
  Classes.Monoid.

From Tealeaves Require Import
  Classes.Categorical.Monad
  Classes.Kleisli.Monad
  Classes.Kleisli.TraversableMonad
  Classes.Kleisli.TraversableFunctor.

Import Kleisli.TraversableMonad.Notations.
Import Kleisli.TraversableFunctor.Notations.
Import Kleisli.Monad.Notations.
Import List.ListNotations.
Import Monoid.Notations.
Import Applicative.Notations.
Open Scope list_scope.

#[local] Generalizable Variables A B M ϕ G.

(** * Automation: <<simpl_list>> *)
(******************************************************************************)
Create HintDb tea_list.
Tactic Notation "simpl_list" := (autorewrite with tea_list).
Tactic Notation "simpl_list" "in" hyp(H) := (autorewrite with tea_list H).
Tactic Notation "simpl_list" "in" "*" := (autorewrite with tea_list in *).

(** * [list] monoid *)
(******************************************************************************)
#[export] Instance Monoid_op_list {A}: Monoid_op (list A) := @app A.

#[export] Instance Monoid_unit_list {A}: Monoid_unit (list A) := nil.

#[export, program] Instance Monoid_list {A} :
  @Monoid (list A) (@Monoid_op_list A) (@Monoid_unit_list A).

Solve Obligations with (intros; unfold transparent tcs; auto with datatypes).

(** * The list [Functor] instance *)
(******************************************************************************)
#[export] Instance Map_list : Map list :=
  fun A B => @List.map A B.

(** ** Rewriting lemmas for <<map>> *)
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

(** ** Functor laws *)
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

(** ** <<map>> is a monoid homomorphism *)
(******************************************************************************)
#[export, program] Instance Monmor_list_map `(f: A -> B) :
  Monoid_Morphism (list A) (list B) (map f) :=
  {| monmor_op := map_list_app f; |}.

(** * The [list] monad, categorically *)
(******************************************************************************)

(** ** Monad operations *)
(******************************************************************************)
#[export] Instance Return_list: Return list := fun A a => cons a nil.

#[export] Instance Join_list: Join list := @List.concat.

(** *** Rewriting lemmas for <<join>> *)
(******************************************************************************)
Lemma join_list_nil :
  `(join ([]: list (list A)) = []).
Proof.
  reflexivity.
Qed.

Lemma join_list_cons: forall A (l: list A) (ll: list (list A)),
    join (l :: ll) = l ++ join ll.
Proof.
  reflexivity.
Qed.

Lemma join_list_one: forall A (l: list A),
    join [ l ] = l.
Proof.
  intros. cbn. now List.simpl_list.
Qed.

Lemma join_list_app: forall A (l1 l2: list (list A)),
    join (l1 ++ l2) = join l1 ++ join l2.
Proof.
  apply List.concat_app.
Qed.

#[export] Hint Rewrite join_list_nil join_list_cons join_list_one join_list_app :
  tea_list.

(** ** Monad instance *)
(******************************************************************************)
#[export] Instance Natural_ret_list: Natural (@ret list _).
Proof.
  constructor; try typeclasses eauto.
  introv. now ext l.
Qed.

#[export] Instance Natural_join_list: Natural (@join list _).
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

(** ** [join] is a monoid homomorphism *)
(** The <<join>> operation is a monoid homomorphism from <<list (list A)>> to
    <<list A>>. This is just a special case of the fact that monoid homomorphisms
    on free monoids are precisely of the form <<foldMap f>> for any <<f: A -> M>>,
    specialized to <<f = id>> case, but we don't need that much generality. *)
(******************************************************************************)
#[export] Instance Monmor_join (A: Type) :
  Monoid_Morphism (list (list A)) (list A) (join (A := A)) :=
  {| monmor_unit := @join_list_nil A;
     monmor_op := @join_list_app A;
  |}.

(** * The [list] Traversable Monad (Kleisli) *)
(******************************************************************************)

(** ** The <<bindt>> Operation *)
(******************************************************************************)
Fixpoint bindt_list (G: Type -> Type)
  `{Map G} `{Pure G} `{Mult G} (A B: Type) (f: A -> G (list B)) (l: list A)
 : G (list B) :=
  match l with
  | nil => pure (@nil B)
  | x :: xs =>
      pure (@List.app B) <⋆> f x <⋆> bindt_list G A B f xs
  end.

#[export] Instance Bindt_list: Bindt list list := @bindt_list.

#[export] Instance Compat_Map_Bindt_list:
  Compat_Map_Bindt list list.
Proof.
  hnf. ext A B f l.
  induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

(** ** Rewriting lemmas for <<bindt>> *)
(******************************************************************************)
Section bindt_rewriting_lemmas.

  Context
    (G: Type -> Type)
    `{Applicative G}
    (A B: Type).

  Lemma bindt_list_nil: forall (f: A -> G (list B)),
      bindt f (@nil A) = pure (@nil B).
  Proof.
    reflexivity.
  Qed.

  Lemma bindt_list_one: forall (f: A -> G (list B)) (a: A),
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

  Lemma bindt_list_cons: forall (f: A -> G (list B)) (a: A) (l: list A),
      bindt f (a :: l) = pure (@app B) <⋆> f a <⋆> bindt f l.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma bindt_list_app: forall (f: A -> G (list B)) (l1 l2: list A),
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

#[export] Hint Rewrite bindt_list_nil bindt_list_cons
  bindt_list_one bindt_list_app :
  tea_list.

(** ** Traversable Monad Instance *)
(******************************************************************************)
Section bindt_laws.

  Context
    (G: Type -> Type)
    `{Applicative G}
    `{Applicative G1}
    `{Applicative G2}
    (A B C: Type).

  Lemma list_bindt0: forall (f: A -> G (list B)),
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
    forall (g: B -> G2 (list C)) (f: A -> G1 (list B)),
      map (F := G1) (bindt g) ∘ bindt f =
        bindt (G := G1 ∘ G2) (g ⋆6 f).
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
      unfold kc6.
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
  forall `(morph: ApplicativeMorphism G1 G2 ϕ),
  forall (A B: Type) (f: A -> G1 (list B)),
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
  DerivedInstances.TraversableRightModule_TraversableMonad.

(** * <<list>> is a Traversable Functor *)
(******************************************************************************)
Fixpoint traverse_list (G: Type -> Type) `{Map G} `{Pure G} `{Mult G} (A B: Type) (f: A -> G B) (l: list A)
 : G (list B) :=
  match l with
  | nil => pure (@nil B)
  | x :: xs =>
      pure (@List.cons B) <⋆> f x <⋆> (traverse_list G A B f xs)
  end.

#[export] Instance Traverse_list: Traverse list := @traverse_list.

#[export] Instance Compat_Traverse_Bindt_list:
  Compat_Traverse_Bindt list list.
Proof.
  hnf. intros.
  ext A B f l.
  unfold DerivedOperations.Traverse_Bindt.
  induction l as [| a rest IHrest].
  - reflexivity.
  - cbn.
    rewrite IHrest.
    unfold compose at 2.
    rewrite pure_ap_map.
    rewrite map_to_ap.
    reflexivity.
Qed.

#[export] Instance Compat_Map_Traverse_list:
  Compat_Map_Traverse list :=
  Compat_Map_Traverse_Bindt.

(** ** Rewriting lemmas for <<traverse>> *)
(******************************************************************************)
Section traverse_rewriting_lemmas.

  Context
    (G: Type -> Type)
    `{Applicative G}
    (A B: Type).

  Lemma traverse_list_nil: forall (f: A -> G B),
      traverse f (@nil A) = pure (@nil B).
  Proof.
    reflexivity.
  Qed.

  Lemma traverse_list_one: forall (f: A -> G B) (a: A),
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

  Lemma traverse_list_cons: forall (f: A -> G B) (a: A) (l: list A),
      traverse f (a :: l) = pure (@cons B) <⋆> f a <⋆> traverse f l.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma traverse_list_app: forall (f: A -> G B) (l1 l2: list A),
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

  Lemma traverse_list_snoc: forall (f: A -> G B) (l: list A) (a: A),
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

#[export] Instance TraversableFunctor_list:
  TraversableFunctor list :=
  DerivedInstances.TraversableFunctor_TraversableMonad.

(** * The List Monad, Kleisli *)
(******************************************************************************)
Fixpoint bind_list (A B: Type) (f: A -> list B) (l: list A): list B :=
  match l with
  | nil => @nil B
  | x :: xs =>
      f x ● bind_list A B f xs
  end.

#[export] Instance Bind_list: Bind list list := @bind_list.

#[export] Instance Compat_Bind_Bindt_list:
  Compat_Bind_Bindt list list.
Proof.
  hnf. ext A B f l.
  induction l as [|a rest IHrest].
  - reflexivity.
  - cbn. now rewrite IHrest.
Qed.

#[export] Instance Compat_Map_Bind_list:
  Compat_Map_Bind list list
  := ltac:(typeclasses eauto).

(** ** Rewriting lemmas for <<bind>> *)
(******************************************************************************)
Section bind_rewriting_lemmas.

  Context
    (A B: Type).

  Lemma bind_list_nil: forall (f: A -> list B),
      bind f (@nil A) = @nil B.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_list_one: forall (f: A -> list B) (a: A),
      bind f (ret a) = f a.
  Proof.
    intros.
    cbn. change (@nil B) with (Ƶ: list B).
    now simpl_monoid.
  Qed.

  Lemma bind_list_cons: forall (f: A -> list B) (a: A) (l: list A),
      bind f (a :: l) = f a ++ bind f l.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_list_app: forall (f: A -> list B) (l1 l2: list A),
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

(** ** [bind] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_bind (A B: Type) (f: A -> list B) :
  Monoid_Morphism (list A) (list B) (bind f).
Proof.
  constructor; try typeclasses eauto.
  - reflexivity.
  - intros. induction a1.
    + reflexivity.
    + cbn. rewrite IHa1.
      now rewrite monoid_assoc.
Qed.

(** * Folding over lists *)
(******************************************************************************)
Fixpoint crush_list
  `{op: Monoid_op M}
  `{unit: Monoid_unit M} (l: list M): M :=
  match l with
  | nil => Ƶ
  | cons x l' => x ● crush_list l'
  end.

(** ** Rewriting lemmas for [crush_list] *)
(******************************************************************************)
Section crush_list_rewriting_lemmas.

  Context
    `{Monoid M}.

  Lemma crush_list_nil: crush_list (@nil M) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma crush_list_cons: forall (m: M) (l: list M),
      crush_list (m :: l) = m ● crush_list l.
  Proof.
    reflexivity.
  Qed.

  Lemma crush_list_one: forall (m: M), crush_list [ m ] = m.
  Proof.
    intro. cbn. now simpl_monoid.
  Qed.

  Lemma crush_list_app: forall (l1 l2: list M),
      crush_list (l1 ++ l2) = crush_list l1 ● crush_list l2.
  Proof.
    intros l1 ?. induction l1 as [| ? ? IHl].
    - cbn. now simpl_monoid.
    - cbn. rewrite IHl. now simpl_monoid.
  Qed.

End crush_list_rewriting_lemmas.

(** ** <<crush_list>> is a Monoid Morphismx *)
(** <<crush_list: list M -> M>> is homomorphism of monoids. *)
(******************************************************************************)
#[export] Instance Monmor_crush_list (M: Type) `{Monoid M} :
  Monoid_Morphism (list M) M crush_list :=
  {| monmor_unit := crush_list_nil;
    monmor_op := crush_list_app;
  |}.

(** ** Misc properties *)
(******************************************************************************)
(** <<crush_list>> commutes with monoid homomorphisms *)
Lemma crush_list_mon_hom:
  forall `(ϕ: M1 -> M2) `{Monoid_Morphism M1 M2 ϕ},
    ϕ ∘ crush_list = crush_list ∘ map ϕ.
Proof.
  intros ? ? ϕ ? ? ? ? ?. unfold compose. ext l.
  induction l as [| ? ? IHl].
  - cbn. apply monmor_unit.
  - cbn. now rewrite (monmor_op (ϕ := ϕ)), IHl.
Qed.

(** In the special case that we crush_list a list of lists, the result is equivalent
    to joining the list of lists. *)
Lemma crush_list_equal_join: forall {A},
    crush_list (M := list A) = join (T := list) (A:=A).
Proof.
  intros. ext l. induction l as [| ? ? IHl].
  - reflexivity.
  - cbn. now rewrite IHl.
Qed.

(** ** The <<foldMap_list>> Operation *)
(******************************************************************************)
Definition foldMap_list {M: Type} `{op: Monoid_op M} `{unit: Monoid_unit M}
  {A: Type} (f: A -> M): list A -> M :=
  crush_list ∘ map f.

(** <<foldMap_list>> is a monoid homomorphism *)
#[export] Instance Monoid_Morphism_foldMap_list
  `{Monoid M} {A: Type}
  `(f: A -> M): Monoid_Morphism (list A) M (foldMap_list f).
Proof.
  unfold foldMap_list.
  eapply Monoid_Morphism_compose.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
Qed.

(** <<foldMap_list>> commutes with monoid homomorphisms *)
Lemma foldMap_list_morphism `{Monoid_Morphism M1 M2 ϕ}
 : forall `(f: A -> M1),
    ϕ ∘ foldMap_list f = foldMap_list (ϕ ∘ f).
Proof.
  intros. unfold foldMap_list.
  reassociate <- on left.
  rewrite (crush_list_mon_hom ϕ).
  reassociate -> on left.
  rewrite fun_map_map.
  reflexivity.
Qed.

(** ** Rewriting with <<foldMap_list>> *)
(******************************************************************************)
Section foldMap_list_rw.

  Context
    {A M: Type}
    `{Monoid M}
    (f: A -> M).

  Lemma foldMap_list_nil: foldMap_list f (@nil A) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_list_cons: forall (x: A) (xs: list A),
      foldMap_list f (x :: xs) = f x ● foldMap_list f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma foldMap_list_one (a: A): foldMap_list f [ a ] = f a.
  Proof.
    cbv. apply monoid_id_l.
  Qed.

  Lemma foldMap_list_ret: foldMap_list f ∘ ret = f.
  Proof.
    ext a; cbn. apply monoid_id_l.
  Qed.

  Lemma foldMap_list_app: forall (l1 l2: list A),
      foldMap_list f (l1 ++ l2) = foldMap_list f l1 ● foldMap_list f l2.
  Proof.
    intros.
    unfold foldMap_list.
    unfold compose. autorewrite with tea_list.
    rewrite crush_list_app.
    reflexivity.
  Qed.

End foldMap_list_rw.

#[export] Hint Rewrite @foldMap_list_nil @foldMap_list_cons
  @foldMap_list_one @foldMap_list_app: tea_list.

Lemma foldMap_list_ret_id: forall A, foldMap_list (@ret list _ A) = id.
Proof.
  intros.
  ext l.
  induction l as [|x rest IHrest];
    autorewrite with tea_list.
  reflexivity.
  now rewrite IHrest.
Qed.

(** ** Monoids form list (monad-)algebras *)
(** In fact, list algebras are precisely monoids. *)
(******************************************************************************)
Section foldable_list.

  Context
    `{Monoid M}.

  Lemma crush_list_ret: forall (x: M),
      crush_list (ret x: list M) = x.
  Proof.
    apply monoid_id_l.
  Qed.

  Lemma crush_list_join: forall (l: list (list M)),
      crush_list (join l) = crush_list (map crush_list l).
  Proof.
    intro l. rewrite <- crush_list_equal_join.
    compose near l on left.
    now rewrite (crush_list_mon_hom crush_list).
  Qed.

  Lemma crush_list_constant_unit: forall (l: list M),
      crush_list (map (fun _ => Ƶ) l) = Ƶ.
  Proof.
    intro l. induction l.
    - reflexivity.
    - cbn. now simpl_monoid.
  Qed.

End foldable_list.
