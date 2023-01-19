From Tealeaves Require Import
  Classes.Monoid
  Functors.Sets
  Classes.Algebraic.Traversable.Monad
  Classes.Algebraic.Setlike.Monad.

From Coq Require Import
  Sorting.Permutation.

Import List.ListNotations.
#[local] Open Scope list_scope.

Import Monoid.Notations.
Import Sets.Notations.
Import Setlike.Functor.Notations.
Import Applicative.Notations.

Create HintDb tea_list.

#[local] Generalizable Variables M A B G ϕ.

(** * [list] monoid *)
(******************************************************************************)
#[export] Instance Monoid_op_list {A} : Monoid_op (list A) := @app A.

#[export] Instance Monoid_unit_list {A} : Monoid_unit (list A) := nil.

#[export, program] Instance Monoid_list {A} :
  @Monoid (list A) (@Monoid_op_list A) (@Monoid_unit_list A).

Solve Obligations with (intros; unfold transparent tcs; auto with datatypes).

(** * [list] functor *)
(******************************************************************************)
#[export] Instance Fmap_list : Fmap list :=
  fun A B f => List.map f.

(** ** Rewriting lemmas for <<fmap>> *)
(******************************************************************************)
Section fmap_list_rw.

  Context
    {A B : Type}
    (f : A -> B).

  Lemma fmap_list_nil : fmap list f (@nil A) = @nil B.
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_list_cons : forall (x : A) (xs : list A),
      fmap list f (x :: xs) = f x :: fmap list f xs.
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_list_one (a : A) : fmap list f [ a ] = [f a].
  Proof.
    reflexivity.
  Qed.

  Lemma fmap_list_app : forall (l1 l2 : list A),
      fmap list f (l1 ++ l2) = fmap list f l1 ++ fmap list f l2.
  Proof.
    unfold transparent tcs. now rewrites List.map_app.
  Qed.

End fmap_list_rw.

#[export] Hint Rewrite @fmap_list_nil @fmap_list_cons
     @fmap_list_one @fmap_list_app : tea_list.

Tactic Notation "simpl_list" := (autorewrite with tea_list).
Tactic Notation "simpl_list" "in" hyp(H) := (autorewrite with tea_list H).
Tactic Notation "simpl_list" "in" "*" := (autorewrite with tea_list in *).

(** ** [fmap] is a monoid homomorphism *)
(******************************************************************************)
#[export, program] Instance Monmor_list_fmap `(f : A -> B) :
  Monoid_Morphism (fmap list f) :=
  {| monmor_op := fmap_list_app f; |}.

(** ** Functor instance *)
(******************************************************************************)
Theorem fmap_id_list {A} : fmap list (@id A) = id.
Proof.
  ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

Theorem fmap_fmap_list {A B C} : forall (f : A -> B) (g : B -> C),
    fmap list g ∘ fmap list f = fmap list (g ∘ f).
Proof.
  intros. unfold compose. ext l. induction l as [| ? ? IH]; simpl_list.
  trivial. now rewrite IH.
Qed.

#[export] Instance Functor_list : Functor list :=
  {| fun_fmap_id := @fmap_id_list;
     fun_fmap_fmap := @fmap_fmap_list;
  |}.

(** * [list] monad *)
(******************************************************************************)
#[export] Instance Return_list : Return list := fun A a => cons a nil.

#[export] Instance Join_list : Join list := @List.concat.

(** ** Rewriting lemmas for <<join>> *)
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

(** ** [join] is a monoid homomorphism *)
(** The <<join>> operation is a monoid homomorphism from <<list (list A)>> to
    <<list A>>. This is just a special case of the fact that monoid homomorphisms
    on free monoids are precisely of the form <<foldMap f>> for any <<f : A -> M>>,
    specialized to <<f = id>> case, but we don't need that much generality. *)
(******************************************************************************)
#[export] Instance Monmor_join (A : Type) : Monoid_Morphism (join list (A := A)) :=
  {| monmor_unit := @join_list_nil A;
     monmor_op := @join_list_app A;
  |}.

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
  join list ∘ ret list = @id (list A).
Proof.
  ext l. unfold compose. destruct l.
  - reflexivity.
  - cbn. now List.simpl_list.
Qed.

Theorem join_fmap_ret_list {A} :
  join list ∘ fmap list (ret list) = @id (list A).
Proof.
  ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

Theorem join_join_list {A} :
  join list ∘ join list (A:=list A) =
  join list ∘ fmap list (join list).
Proof.
  ext l. unfold compose. induction l as [| ? ? IHl].
  - reflexivity.
  - simpl_list. now rewrite IHl.
Qed.

#[export] Instance Monad_list : Monad list :=
  {| mon_join_ret := @join_ret_list;
     mon_join_fmap_ret := @join_fmap_ret_list;
     mon_join_join := @join_join_list;
  |}.

(** * [list] is set-like *)
(** A [list] can be reduced to a [set] by discarding the ordering, or more
    concretely by applying [List.In]. This makes [list] into a quantifiable
    monad. The lemmas involved in proving this fact form a key step in proving
    that all listables are quantifiable, below. *)
(******************************************************************************)
#[export] Instance Toset_list : Toset list :=
  fun _ l a => List.In a l.

(** ** Rewriting lemmas for <<toset>>\<<∈>>*)
(******************************************************************************)
Lemma toset_list_nil : forall A, toset list (@nil A) = ∅.
Proof.
  reflexivity.
Qed.

Lemma toset_list_cons : forall A (x : A) (xs : list A),
    toset list (x :: xs) = ret set x ∪ toset list xs.
Proof.
  reflexivity.
Qed.

Lemma toset_list_one : forall A (a : A), toset list [ a ] = ret set a.
Proof.
  intros. ext b; propext; cbv; intuition.
Qed.

Lemma toset_list_ret : forall A (a : A), toset list (ret list a) = ret set a.
Proof.
  intros. ext b; propext; cbv; intuition.
Qed.

Lemma toset_list_app : forall A (l1 l2 : list A),
    toset list (l1 ++ l2) = toset list l1 ∪ toset list l2.
Proof.
  intros. ext b. change (toset list ?l b) with (List.In b l).
  propext; rewrite -> List.in_app_iff; auto.
Qed.

#[export] Hint Rewrite toset_list_nil toset_list_cons
     toset_list_one toset_list_ret toset_list_app : tea_list.

Lemma in_list_nil {A} : forall (p : A), p ∈ @nil A <-> False.
Proof.
  reflexivity.
Qed.

Lemma in_list_cons {A} : forall (a1 a2 : A) (xs : list A),
    a1 ∈ (a2 :: xs) <-> a1 = a2 \/ a1 ∈ xs.
Proof.
  intros; simpl_list. unfold_set. intuition congruence.
Qed.

Lemma in_list_one {A} (a1 a2 : A) : a1 ∈ [ a2 ] <-> a1 = a2.
Proof.
  intros. simpl_list. simpl_set. intuition congruence.
Qed.

Lemma in_list_ret {A} (a1 a2 : A) : a1 ∈ ret list a2 <-> a1 = a2.
Proof.
  intros. simpl_list. intuition.
Qed.

Lemma in_list_app {A} : forall (a : A) (xs ys : list A),
    a ∈ (xs ++ ys) <-> a ∈ xs \/ a ∈ ys.
Proof.
  intros. simpl_list. simpl_set. reflexivity.
Qed.

#[export] Hint Rewrite @in_list_nil @in_list_cons
     @in_list_one @in_list_ret @in_list_app : tea_list.

Theorem perm_set_eq : forall {A} {l1 l2 : list A},
    Permutation l1 l2 -> (forall a, a ∈ l1 <-> a ∈ l2).
Proof.
  introv perm. induction perm; firstorder.
Qed.

(** ** [toset] is a monoid homomorphism *)
(******************************************************************************)
#[export] Instance Monmor_toset_list (A : Type) : Monoid_Morphism (toset list (A := A)) :=
  {| monmor_unit := @toset_list_nil A;
     monmor_op := @toset_list_app A;
  |}.

(** ** Respectfulness conditions *)
(******************************************************************************)
#[export] Instance Natural_toset_list: Natural (@toset list _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold compose. ext l. induction l.
  - simpl_list; simpl_set. trivial.
  - simpl_list; simpl_set. now rewrite IHl.
Qed.

Theorem fmap_rigidly_respectful_list : forall A B (f g : A -> B) (l : list A),
    (forall (a : A), a ∈ l -> f a = g a) <-> fmap list f l = fmap list g l.
Proof.
  intros. induction l.
  - simpl_list. setoid_rewrite set_in_empty. tauto.
  - simpl_list. setoid_rewrite set_in_add.
    setoid_rewrite set_in_ret.
    destruct IHl. split.
    + intro; fequal; auto.
    + injection 1; intuition (subst; auto).
Qed.

Corollary fmap_respectful_list : forall A B (l : list A) (f g : A -> B),
    (forall (a : A), a ∈ l -> f a = g a) -> fmap list f l = fmap list g l.
Proof.
  intros. now rewrite <- fmap_rigidly_respectful_list.
Qed.

#[export] Instance SetlikeFunctor_list : SetlikeFunctor list :=
  {| xfun_respectful := fmap_respectful_list; |}.

(** ** Set-like monad instance *)
(******************************************************************************)
Theorem toset_ret_list :
  `(toset list ∘ ret list (A:=A) = ret set).
Proof.
  intros. unfold compose. ext a.
  now simpl_list.
Qed.

Theorem toset_join_list :
  `(toset (A:=A) list ∘ join list = join set ∘ toset list ∘ fmap list (toset list)).
Proof.
  intros. unfold compose. ext l. induction l.
  - simpl_list; simpl_set; trivial.
  - simpl_list. simpl_set. rewrite IHl. trivial.
Qed.

Theorem return_injective_list : forall A (a b : A),
    [a] = [b] -> a = b.
Proof.
  introv hyp. now inverts hyp.
Qed.

#[export] Instance SetlikeMonad_list : SetlikeMonad list :=
  {| xmon_ret := toset_ret_list;
     xmon_join := toset_join_list;
     xmon_ret_injective := return_injective_list;
  |}.

(** * Traversable instance for [list] *)
(******************************************************************************)
#[export] Instance Dist_list : Dist list :=
  fun G map mlt pur A =>
    (fix dist (l : list (G A)) :=
       match l with
       | nil => pure G nil
       | cons x xs =>
         (pure G (@cons A) <⋆> x) <⋆> (dist xs)
       end).

(** ** Rewriting lemmas for <<dist>> *)
(******************************************************************************)
Section list_dist_rewrite.

  Context
    `{Applicative G}.

  Variable (A : Type).

  Lemma dist_list_nil :
    dist list G (@nil (G A)) = pure G nil.
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_1 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      (pure G cons <⋆> x) <⋆> (dist list G xs).
  Proof.
    reflexivity.
  Qed.

  Lemma dist_list_cons_2 : forall (x : G A) (xs : list (G A)),
      dist list G (x :: xs) =
      (fmap G (@cons A) x) <⋆> (dist list G xs).
  Proof.
    intros. rewrite dist_list_cons_1.
    now rewrite fmap_to_ap.
  Qed.

  Lemma dist_list_one (a : G A) : dist list G [ a ] = fmap G (ret list) a.
  Proof.
    cbn. rewrite fmap_to_ap. rewrite ap3.
    rewrite <- ap4. now do 2 rewrite ap2.
  Qed.

  Lemma dist_list_app : forall (l1 l2 : list (G A)),
      dist list G (l1 ++ l2) = pure G (@app _) <⋆> dist list G l1 <⋆> dist list G l2.
  Proof.
    intros. induction l1.
    - cbn. rewrite ap2. change (app []) with (@id (list A)).
      now rewrite ap1.
    - cbn [app]. rewrite dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl1; clear IHl1.
      rewrite <- fmap_to_ap.
      rewrite <- fmap_to_ap.
      rewrite <- ap4. rewrite <- fmap_to_ap.
      fequal. rewrite <- ap7.
      rewrite ap6. fequal.
      compose near a.
      rewrite (fun_fmap_fmap G).
      rewrite (fun_fmap_fmap G).
      compose near a on left.
      now rewrite (fun_fmap_fmap G).
  Qed.

End list_dist_rewrite.

#[export] Hint Rewrite @dist_list_nil @dist_list_cons_1
     @dist_list_one @dist_list_app : tea_list.

Section dist_list_properties.

  #[local] Arguments dist _%function_scope {Dist} _%function_scope {H H0 H1}
   A%type_scope _.

  Lemma dist_list_1 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      fmap G (fmap list f) ((fmap G (@cons A) a) <⋆> dist list G A l) =
      (fmap G (@cons B ○ f) a) <⋆> fmap G (fmap list f) (dist list G A l).
  Proof.
    intros. rewrite ap6. rewrite <- ap7.
    fequal. compose near a. now rewrite 2(fun_fmap_fmap G).
  Qed.

  Lemma dist_list_2 : forall `{Applicative G} `(f : A -> B) (a : G A) (l : list (G A)),
      fmap G (fmap list f) ((pure G (@cons A) <⋆> a) <⋆> dist list G A l) =
      (pure G cons <⋆> fmap G f a) <⋆> fmap G (fmap list f) (dist list G A l).
  Proof.
    intros. rewrite <- fmap_to_ap.
    rewrite ap6.
    compose near a on left.
    rewrite (fun_fmap_fmap G).
    rewrite ap5.
    unfold ap. rewrite (app_mult_natural G).
    rewrite (app_mult_natural_1 G).
    compose near ((a ⊗ dist list G A l)) on right.
    rewrite (fun_fmap_fmap G). fequal. ext [? ?].
    reflexivity.
  Qed.

  Lemma dist_natural_list : forall `{Applicative G} `(f : A -> B),
      fmap (G ∘ list) f ∘ dist list G A =
      dist list G B ∘ fmap (list ∘ G) f.
  Proof.
    intros; cbn. unfold_ops @Fmap_compose. unfold compose.
    ext l. induction l.
    + cbn. now rewrite (app_pure_natural G).
    + rewrite dist_list_cons_2.
      rewrite fmap_list_cons, dist_list_cons_2.
      rewrite <- IHl. rewrite dist_list_1.
      compose near a on right. now rewrite (fun_fmap_fmap G).
  Qed.

  Instance dist_natural_list_ : forall `{Applicative G}, Natural (@dist list _ G _ _ _).
  Proof.
    constructor; try typeclasses eauto.
    intros. eapply (dist_natural_list f).
  Qed.

  Lemma dist_morph_list : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist list G2 A ∘ fmap list (ϕ A) = ϕ (list A) ∘ dist list G1 A.
  Proof.
    intros. ext l. unfold compose. induction l.
    - cbn. now rewrite (appmor_pure G1 G2).
    - specialize (appmor_app_F G1 G2);
        specialize (appmor_app_G G1 G2);
        intros.
      rewrite fmap_list_cons, dist_list_cons_2.
      rewrite dist_list_cons_2.
      rewrite IHl. rewrite ap_morphism_1.
      fequal. now rewrite (appmor_natural G1 G2 A).
  Qed.

  Lemma dist_unit_list : forall (A : Type),
      dist list (fun A => A) A = @id (list A).
  Proof.
    intros. ext l. induction l.
    - reflexivity.
    - cbn. now rewrite IHl.
  Qed.

  #[local] Set Keyed Unification.
  Lemma dist_linear_list
    : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist list (G1 ∘ G2) A =
      fmap G1 (dist list G2 A) ∘ dist list G1 (G2 A).
  Proof.
    intros. unfold compose. ext l. induction l.
    - cbn. unfold_ops @Pure_compose.
      rewrite fmap_to_ap. now rewrite ap2.
    - rewrite (dist_list_cons_2 (G := G1 ○ G2)).
      rewrite (dist_list_cons_2 (G := G1)).
      rewrite IHl; clear IHl.
      unfold_ops @Mult_compose @Pure_compose @Fmap_compose.
      rewrite (ap_compose2 G2 G1).
      rewrite (app_mult_natural G1).
      unfold ap at 2. rewrite (app_mult_natural_1 G1).
      fequal. compose near (a ⊗ dist list G1 (G2 A) l).
      repeat rewrite (fun_fmap_fmap G1). fequal.
      ext [? ?]. cbn. now rewrite fmap_to_ap.
  Qed.
  #[local] Unset Keyed Unification.

End dist_list_properties.

#[export] Instance Traversable_list : TraversableFunctor list :=
  {| dist_natural := @dist_natural_list_;
     dist_morph := @dist_morph_list;
     dist_unit := @dist_unit_list;
     dist_linear := @dist_linear_list;
  |}.

(** ** Traversable monad instance for [list] *)
(******************************************************************************)
Section TraversableMonad_list.

  Section with_context.
    
  Context
    `{Applicative G}
    {A : Type}.

  Theorem trvmon_ret_list :
    `(dist list G ∘ ret list (A := G A) = fmap G (ret list)).
  Proof.
    ext x. unfold compose.
    unfold_ops @Return_list.
    rewrite dist_list_cons_2.
    rewrite dist_list_nil.
    rewrite ap3, ap5.
    reflexivity.
  Qed.

  #[local] Set Keyed Unification.
  Theorem trvmon_join_list :
    `(dist list G ∘ join list = fmap G (join list) ∘ dist (list ∘ list) G (A := A)).
  Proof.
    ext l. unfold compose. induction l.
    - rewrite join_list_nil. rewrite dist_list_nil.
      unfold_ops @Dist_compose. unfold compose.
      rewrite fmap_list_nil, dist_list_nil.
      now rewrite (app_pure_natural G).
    - rewrite join_list_cons.
      unfold_ops @Dist_compose. unfold compose.
      rewrite (fmap_list_cons). rewrite dist_list_cons_2.
      rewrite dist_list_app. rewrite IHl; clear IHl.
      unfold_ops @Dist_compose. unfold compose.
      rewrite <- (fmap_to_ap).
      rewrite ap6. compose near (dist list G a) on right.
      rewrite (fun_fmap_fmap G).
      rewrite <- ap7.
      compose near (dist list G a) on left.
      now rewrite (fun_fmap_fmap G).
  Qed.
  #[local] Set Keyed Unification.

  End with_context.

  #[export] Instance: TraversableMonad list :=
    {| trvmon_ret := @trvmon_ret_list;
       trvmon_join := @trvmon_join_list;
    |}.

End TraversableMonad_list.

(** * Folding over lists *)
(******************************************************************************)
Fixpoint fold `{op : Monoid_op M} `{unit : Monoid_unit M} (l : list M) : M :=
  match l with
  | nil => Ƶ
  | cons x l' => x ● fold l'
  end.

(** ** Rewriting lemmas for [fold] *)
(******************************************************************************)
Section fold_rewriting_lemmas.

  Context
    `{Monoid M}.

  Lemma fold_nil : fold (@nil M) = Ƶ.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_cons : forall (m : M) (l : list M),
      fold (m :: l) = m ● fold l.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_one : forall (m : M), fold [ m ] = m.
  Proof.
    intro. cbn. now simpl_monoid.
  Qed.

  Lemma fold_app : forall (l1 l2 : list M),
      fold (l1 ++ l2) = fold l1 ● fold l2.
  Proof.
    intros l1 ?. induction l1 as [| ? ? IHl].
    - cbn. now simpl_monoid.
    - cbn. rewrite IHl. now simpl_monoid.
  Qed.

End fold_rewriting_lemmas.

(** ** Folding a list is a monoid homomorphism *)
(** <<fold : list M -> M>> is homomorphism of monoids. *)
(******************************************************************************)
#[export] Instance Monmor_fold `{Monoid M} : Monoid_Morphism fold :=
  {| monmor_unit := fold_nil;
     monmor_op := fold_app |}.

(** ** Other properties of <<fold>> *)
(******************************************************************************)

(** In the special case that we fold a list of lists, the result is equivalent
    to joining the list of lists. *)
Lemma fold_equal_join : forall {A},
    fold = join list (A:=A).
Proof.
  intros. ext l. induction l as [| ? ? IHl].
  - reflexivity.
  - cbn. now rewrite IHl.
Qed.

(** Folding across a list of monoidal values commutes with applying a monoid
    homomorphism to the elements. *)
Theorem fold_mon_hom : forall `(ϕ : M1 -> M2) `{Monoid_Morphism M1 M2 ϕ},
    ϕ ∘ fold = fold ∘ fmap list ϕ.
Proof.
  intros ? ? ϕ ? ? ? ? ?. unfold compose. ext l.
  induction l as [| ? ? IHl].
  - cbn. apply (monmor_unit ϕ).
  - cbn. now rewrite (monmor_op ϕ), IHl.
Qed.

Corollary fold_nat {A B : Type} (f : A -> B) :
  fmap list f ∘ fold = fold ∘ fmap list (fmap list f).
Proof.
  now rewrite (fold_mon_hom (fmap list f)).
Qed.

(** ** Monoids form list (monad-)algebras *)
(** In fact, list algebras are precisely monoids. *)
(******************************************************************************)
Section foldable_list.

  Context
    `{Monoid M}.

  Lemma fold_ret : forall (x : M),
      fold (ret list x : list M) = x.
  Proof.
    apply monoid_id_l.
  Qed.

  Lemma fold_join : forall (l : list (list M)),
      fold (join list l) = fold (fmap list fold l).
  Proof.
    intro l. rewrite <- fold_equal_join.
    compose near l on left.
    now rewrite (fold_mon_hom fold).
  Qed.

  Lemma fold_constant_unit : forall (l : list M),
      fold (fmap list (fun _ => Ƶ) l) = Ƶ.
  Proof.
    intro l. induction l.
    - reflexivity.
    - cbn. now simpl_monoid.
  Qed.

End foldable_list.

(** * Filtering lists *)
(******************************************************************************)
Fixpoint filter `(P : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons a rest =>
    if P a then a :: filter P rest else filter P rest
  end.

(** ** Rewriting lemmas for [filter] *)
(******************************************************************************)
Section filter_lemmas.

  Context
    `(P : A -> bool).

  Lemma filter_nil :
    filter P nil = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_cons : forall (a : A) (l : list A),
      filter P (a :: l) = if P a then a :: filter P l else filter P l.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_one : forall (a : A),
      filter P [a] = if P a then [a] else nil.
  Proof.
    reflexivity.
  Qed.

  Lemma filter_app : forall (l1 l2 : list A),
      filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
  Proof.
    intros. induction l1.
    - reflexivity.
    - cbn. rewrite IHl1. now destruct (P a).
  Qed.

End filter_lemmas.

#[export] Hint Rewrite @filter_nil @filter_cons @filter_app @filter_one : tea_list.

(** * <<fmap>> equality inversion lemmas *)
(** Some lemmas for reasoning backwards from equality between two
    similarly-concatenated lists.  *)
(******************************************************************************)
Lemma fmap_app_inv_l : forall {A B} {f g : A -> B} (l1 l2 : list A),
    fmap list f (l1 ++ l2) = fmap list g (l1 ++ l2) ->
    fmap list f l1 = fmap list g l1.
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl_list in *. rewrite IHl1.
    + fequal. simpl in H. inversion H; auto.
    + simpl in H. inversion H. auto.
Qed.

Lemma fmap_app_inv_r : forall {A B} {f g : A -> B} (l1 l2 : list A),
    fmap list f (l1 ++ l2) = fmap list g (l1 ++ l2) ->
    fmap list f l2 = fmap list g l2.
Proof.
  intros.
  assert (heads_equal : fmap list f l1 = fmap list g l1).
  { eauto using fmap_app_inv_l. }
  simpl_list in *.
  rewrite heads_equal in H.
  eauto using List.app_inv_head.
Qed.

Lemma fmap_app_inv : forall {A B} {f g : A -> B} (l1 l2 : list A),
    fmap list f (l1 ++ l2) = fmap list g (l1 ++ l2) ->
    fmap list f l1 = fmap list g l1 /\ fmap list f l2 = fmap list g l2.
Proof.
  intros; split; eauto using fmap_app_inv_l, fmap_app_inv_r.
Qed.
