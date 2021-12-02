From Tealeaves Require Export
     Classes.Monoid
     Classes.Monad
     Functors.List
     Functors.Sets
     Classes.SetlikeFunctor.

Import Functor.Notations.
Import Sets.Notations.
Import SetlikeFunctor.Notations.
Import List.Notations.
#[local] Open Scope list_scope.
#[local] Open Scope tealeaves_scope.

(** * The [shape] operation *)
(******************************************************************************)
Definition shape F `{Fmap F} {A} : F A -> F unit :=
  fmap F (const tt).

(** ** Basic reasoning principles for <<shape>> *)
(******************************************************************************)
Theorem shape_fmap `{Functor F} : forall (A B : Type) (f : A -> B) (t : F A),
    shape F (fmap F f t) = shape F t.
Proof.
  intros. compose near t on left.
  unfold shape. now rewrite (fun_fmap_fmap F).
Qed.

Theorem shape_shape `{Functor F} : forall A (t : F A),
    shape F (shape F t) = shape F t.
Proof.
  intros.  compose near t on left.
  unfold shape. now rewrite (fun_fmap_fmap F).
Qed.

(** * Listable functors *)
(** A [ListableFunctor] <<F>> is an endofunctor with a natural transformation to
    [list]. This is closely related to the typeclass <<Foldable>> of the GHC
    standard library for Haskell
    (https://wiki.haskell.org/Foldable_and_Traversable), but Haskell's typeclass
    is not a subset of functors for technical reasons. Furthermore Haskell's
    typeclass is based on a "fold" operation while we take [tolist] as the
    primary class method. *)
(******************************************************************************)
Section ListableFunctor_operations.

  Context
    (F : Type -> Type).

  Class Tolist :=
    tolist : F ⇒ list.

  Definition shapeliness `{Fmap F} `{Tolist} := forall A (t1 t2 : F A),
      shape F t1 = shape F t2 /\ tolist _ t1 = tolist _ t2 -> t1 = t2.

End ListableFunctor_operations.

Arguments tolist F%function_scope {Tolist} {A}%type_scope _.

Section ListableFunctor.

  Context
    (F : Type -> Type)
    `{Fmap F} `{Tolist F}.

  Class ListableFunctor :=
    { lfun_natural :> Natural (@tolist F _);
      lfun_functor :> Functor F;
      lfun_shapeliness : shapeliness F;
    }.

End ListableFunctor.

(** ** <<tolist>>-preserving natural transformations *)
(** A [ListPreservingTransformation] is a natural transformation
    between two listable functors that commutes with [tolist]. This is
    an operation that modifies the shape and type of a container without
    changing its leaves or their order. *)
(******************************************************************************)
Class ListPreservingTransformation
      {F G : Type -> Type}
      `{! Fmap F} `{Tolist F}
      `{! Fmap G} `{Tolist G}
      (η : F ⇒ G) :=
  { ltrans_commute : `(tolist F = tolist G ∘ η A);
    ltrans_natural : Natural η;
  }.

(** ** Instance for [list] *)
(** As a reasonability check, we prove that [list] is a listable functor. *)
(******************************************************************************)
Instance Tolist_list : Tolist list := fun A l => l.

Section ListableFunctor_list.

  Instance: Natural (@tolist list _).
  Proof.
    constructor; try typeclasses eauto.
    reflexivity.
  Qed.

  Theorem shapeliness_list : shapeliness list.
  Proof.
    intros A t1 t2. intuition.
  Qed.

  #[program] Instance: ListableFunctor list :=
    {| lfun_shapeliness := shapeliness_list; |}.

End ListableFunctor_list.

(** * Properties of <<shape>> *)
(******************************************************************************)

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
    intros. unfold shape. now rewrite fmap_list_app.
  Qed.

  Lemma shape_nil_iff : forall A (l : list A),
      shape list l = @nil unit <-> l = [].
  Proof.
    induction l. intuition.
    split; intro contra; now inverts contra.
  Qed.

End list_shape_rewrite.

Hint Rewrite @shape_nil @shape_cons @shape_one @shape_app : tea_rw_list.

(** ** Reasoning princples for <<shape>> on lists *)
(******************************************************************************)
Section list_shape_lemmas.

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
    - introv shape_eq heq. apply (inv_app_eq_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- shape_eq_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq. apply (inv_app_eq_ll) with (r1 := r1) (r2 := r2).
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

End list_shape_lemmas.

(** ** Reasoning principles for <<shape>> on listable functors *)
(** These principles are predicated just on <<tolist>> being a natural
    transformation and can be used to prove [shapeliness] for a given
    functor. *)
(******************************************************************************)
Section listable_shape_lemmas.

  Context
    (F : Type -> Type)
    `{Functor F}
    `{Tolist F} `{! Natural (@tolist F _)}.

  Lemma shape_fmap_1 : forall A1 A2 B (f : A1 -> B) (g : A2 -> B) t u,
      fmap F f t = fmap F g u ->
      shape F t = shape F u.
  Proof.
    introv hyp. cut (shape F (fmap F f t) = shape F (fmap F g u)).
    - now rewrite 2(shape_fmap).
    - now rewrite hyp.
  Qed.

  Lemma shape_tolist_1 : forall `(t : F A) `(u : F B),
      shape F t = shape F u ->
      shape list (tolist F t) = shape list (tolist F u).
  Proof.
    introv heq. compose near t. compose near u.
    unfold shape in *. rewrite 2(natural). unfold compose.
    now rewrite heq.
  Qed.

  Theorem shape_eq_impl_tolist : forall A (t s : F A),
      shape F t = shape F s ->
      shape list (tolist F t) = shape list (tolist F s).
  Proof.
    introv heq. compose near t on left; compose near s on right.
    unfold shape in *. rewrite natural.
    unfold compose. now rewrite heq.
  Qed.

  Corollary shape_l : forall A (l1 l2 : F A) (x y : list A),
      shape F l1 = shape F l2 ->
      (tolist F l1 ++ x = tolist F l2 ++ y) ->
      tolist F l1 = tolist F l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_ll, shape_eq_impl_tolist.
  Qed.

  Corollary shape_r : forall A (l1 l2 : F A) (x y : list A),
      shape F l1 = shape F l2 ->
      (x ++ tolist F l1 = y ++ tolist F l2) ->
      tolist F l1 = tolist F l2.
  Proof.
    introv shape_eq heq.
    eauto using inv_app_eq_rr, shape_eq_impl_tolist.
  Qed.

End listable_shape_lemmas.

(** * Listable functors form a monoidal category *)
(******************************************************************************)

(** ** The identity functor is listable *)
(******************************************************************************)
Instance Tolist_I : Tolist (fun x => x) := fun A x => [x].

Instance: Natural (@tolist (fun x => x) _).
Proof.
  constructor; try typeclasses eauto.
  reflexivity.
Qed.

Theorem shapeliness_I : shapeliness (fun x => x).
Proof.
  intros A t1 t2. cbv. intros [? heq]. now inversion heq.
Qed.

Instance ListableFunctor_I : ListableFunctor (fun x => x) :=
  {| lfun_shapeliness := shapeliness_I; |}.

(** ** Listable functors are closed under composition *)
(******************************************************************************)
Section listable_compose.

  Context
    `{ListableFunctor F}
    `{ListableFunctor G}.

  #[global] Instance Tolist_compose : Tolist (F ∘ G) :=
    fun A => join list ∘ tolist F ∘ fmap F (tolist G).

  #[local] Unset Keyed Unification.

  Lemma Tolist_compose_natural : Natural (F := F ∘ G) Tolist_compose.
  Proof.
    constructor; try typeclasses eauto.
    introv. unfold Tolist_compose.
    repeat reassociate <- on left. rewrite natural.
    repeat reassociate -> on left;
      reassociate <- near (fmap (list ∘ list) f).
    unfold_ops @Fmap_compose; unfold_compose_in_compose;
      rewrite (natural).
    repeat reassociate -> on left. rewrite (fun_fmap_fmap F).
    repeat reassociate -> on right. rewrite (fun_fmap_fmap F).
    now rewrite natural.
  Qed.

  Lemma shape_compose_spec {A} :
    shape (F ∘ G) (A := A) = fmap F (shape G).
  Proof.
    reflexivity.
  Qed.

  Lemma shape_compose_1 : forall A (t u : F (G A)),
      shape (F ∘ G) t = shape (F ∘ G) u ->
      shape F t = shape F u.
  Proof.
    introv hyp. rewrite shape_compose_spec in hyp.
    now apply (shape_fmap_1 F) in hyp.
  Qed.

  Lemma shape_compose_2 : forall A (t u : F (G A)),
      shape (F ∘ G) t = shape (F ∘ G) u ->
      fmap list (shape G) (tolist F t) = fmap list (shape G) (tolist F u).
  Proof.
    intros. compose near t. compose near u.
    rewrite natural. unfold compose.
    fequal. assumption.
  Qed.

  Lemma shapeliness_compose_1 : forall A (l1 l2 : list (G A)),
      fmap list (shape G) l1 = fmap list (shape G) l2 ->
      bind list (tolist G) l1 = bind list (tolist G) l2 ->
      l1 = l2.
  Proof.
    intros. generalize dependent l2.
    induction l1; intros l2 hshape hcontents.
    - destruct l2.
      + reflexivity.
      + inversion hshape.
    - destruct l2.
      + inversion hshape.
      + autorewrite with tea_list in *.
        inversion hshape.
        assert (heq : tolist G a = tolist G g)
          by eauto using (shape_l G).
        rewrite heq in hcontents. fequal.
        * auto using (lfun_shapeliness G).
        * eauto using list_app_inv_r.
  Qed.

  Theorem shapeliness_compose : shapeliness (F ∘ G).
  Proof.
    intros A t1 t2 [hshape hcontents].
      unfold tolist, Tolist_compose in hcontents.
      reassociate -> in hcontents.
      #[local] Set Keyed Unification.
      rewrite <- (natural (F := F) (G := list)) in hcontents.
      #[local] Unset Keyed Unification.
      unfold compose in hcontents.
      apply (lfun_shapeliness F); split.
      + auto using shape_compose_1.
      + auto using shapeliness_compose_1, shape_compose_2.
  Qed.

  #[global] Instance ListableFunctor_compose : ListableFunctor (F ∘ G) :=
    {| lfun_natural := Tolist_compose_natural;
       lfun_functor := Functor_compose;
       lfun_shapeliness := shapeliness_compose;
    |}.

End listable_compose.

(** * Respectfulness conditions for listable functors *)
(******************************************************************************)
Section listable_functor_respectful_definitions.

  Context
    (F : Type -> Type)
    `{Fmap F} `{Tolist F}.

  Definition tolist_fmap_injective := forall A B (t1 t2 : F A) (f g : A -> B),
      fmap F f t1 = fmap F g t2 ->
      shape F t1 = shape F t2 /\
      fmap list f (tolist F t1) = fmap list g (tolist F t2).

  Definition tolist_fmap_respectful := forall A B (t1 t2 : F A) (f g : A -> B),
      shape F t1 = shape F t2 ->
      fmap list f (tolist F t1) = fmap list g (tolist F t2) ->
      fmap F f t1 = fmap F g t2.

  Definition tolist_fmap_respectful_iff := forall A B (t1 t2 : F A) (f g : A -> B),
      shape F t1 = shape F t2 /\
      fmap list f (tolist F t1) = fmap list g (tolist F t2) <->
      fmap F f t1 = fmap F g t2.

End listable_functor_respectful_definitions.

Ltac unfold_list_properness :=
  unfold shapeliness,
  tolist_fmap_respectful,
  tolist_fmap_respectful_iff in *.

(** ** Equivalence with shapeliness *)
(******************************************************************************)
Section tolist_respectfulness_characterizations.

  Context
    `{ListableFunctor F}.

  Theorem tolist_fmap_injective_proof : tolist_fmap_injective F.
  Proof.
    introv heq. split.
    - cut (shape F (fmap F f t1) = shape F (fmap F g t2)).
      + now rewrite 2(shape_fmap).
      + now rewrite heq.
    - compose near t1; compose near t2.
      rewrite 2natural.
      unfold compose; now rewrite heq.
  Qed.

  Lemma shapeliness_equiv_1 : shapeliness F -> tolist_fmap_respectful F.
  Proof.
    unfold tolist_fmap_respectful.
    introv hyp hshape hcontents.
    apply hyp. split.
    - now rewrite 2(shape_fmap).
    - compose near t1 on left; compose near t2 on right.
      now rewrite <- 2(natural).
  Qed.

  Lemma shapeliness_equiv_2: tolist_fmap_respectful F -> tolist_fmap_respectful_iff F.
  Proof.
    unfold tolist_fmap_respectful, tolist_fmap_respectful_iff.
    intros. split.
    - introv [? ?]. auto.
    - apply tolist_fmap_injective_proof.
  Qed.

  Lemma shapeliness_equiv_3: tolist_fmap_respectful_iff F -> shapeliness F.
  Proof.
    unfold shapeliness, tolist_fmap_respectful_iff.
    introv hyp1 hyp2.
    replace t1 with (fmap F id t1) by (now rewrite (fun_fmap_id F)).
    replace t2 with (fmap F id t2) by (now rewrite (fun_fmap_id F)).
    apply hyp1. now rewrite (fun_fmap_id list).
  Qed.

End tolist_respectfulness_characterizations.

(** * Properties of listable functors *)
(******************************************************************************)

(** ** Listable functors are set-like *)
(******************************************************************************)
Instance Toset_Tolist `{Tolist F} : Toset F :=
  fun A => toset list ∘ tolist F.

#[global] Instance: forall `{ListableFunctor F}, Natural (@toset F _).
Proof.
  constructor; try typeclasses eauto.
  intros A B f. unfold toset, Toset_Tolist. ext t.
  reassociate <- on left. rewrite (natural (G:=set)).
  reassociate -> on left. now rewrite natural.
Qed.

Theorem in_iff_in_list `{Tolist F} : forall (A : Type) (t : F A) (a : A),
    a ∈ t <-> a ∈ tolist F t.
Proof.
  reflexivity.
Qed.

Section ListableFunctor_setlike.

  Context
    `{ListableFunctor F}.

  Lemma listable_equal_iff :
    forall (A : Type) (t u : F A),
      t = u <-> shape F t = shape F u /\ tolist F t = tolist F u.
  Proof.
    intros. split.
    + intros; subst; auto.
    + apply (lfun_shapeliness F).
  Qed.

  (** Two maps over [t] are equal when they're equal on t's contents. *)
  Lemma listable_fmap_equal :
    forall (A B : Type) (t : F A) (f g : A -> B),
      fmap F f t = fmap F g t <->
      fmap list f (tolist F t) = fmap list g (tolist F t).
  Proof.
    unfold_list_properness. intros.
    compose near t on right. rewrite 2(natural).
    unfold compose. split.
    - introv heq. now rewrite heq.
    - intros. apply (lfun_shapeliness F). rewrite 2(shape_fmap).
      auto.
  Qed.

  (** Listable functors satisfy the "rigid" version of the respectfulness property. *)
  Theorem listable_rigidly_respectful :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) <-> fmap F f t = fmap F g t.
  Proof.
    introv. rewrite listable_fmap_equal.
    setoid_rewrite in_iff_in_list.
    now rewrite fmap_rigidly_respectful_list.
  Qed.

  Corollary listable_respectful :
    forall (A B : Type) (t : F A) (f g : A -> B),
      (forall (a : A), a ∈ t -> f a = g a) -> fmap F f t = fmap F g t.
  Proof.
   intros. now rewrite <- listable_rigidly_respectful.
 Qed.

  #[global] Instance SetlikeFunctor_Listable : SetlikeFunctor F :=
    {| xfun_respectful := listable_respectful; |}.

End ListableFunctor_setlike.

(** ** Miscellaneous properties of listable functors *)
(******************************************************************************)
Section ListableFunctor_theory.

  Context
    (F : Type -> Type)
    `{ListableFunctor F}.

  Corollary tolist_fmap `(t : F A) `(f : A -> B) (a : A) :
    tolist F (fmap F f t) = fmap list f (tolist F t).
  Proof.
    intros. compose near t on left.
    now rewrite <- natural.
  Qed.

  Corollary tolist_fmap_rigidly_respectful_id :
    forall (A : Type) (t : F A) (f : A -> A),
      (forall (a : A), a ∈ t -> f a = a) <-> fmap F f t = t.
  Proof.
    introv. replace t with (fmap F id t) at 2
      by now rewrite (fun_fmap_id F).
    now rewrite listable_rigidly_respectful.
  Qed.

End ListableFunctor_theory.

(** * [fold] and [foldMap] operations *)
(******************************************************************************)
Section fold.

  Context
    `{ListableFunctor F}.

  Definition fold `{Monoid_op M} `{Monoid_unit M} : F M -> M :=
    List.fold ∘ tolist F.

  Definition foldMap {A} `{Monoid_op M} `{Monoid_unit M} (f : A -> M) : F A -> M :=
    fold ∘ fmap F f.

  Lemma fold_mon_hom : forall `(ϕ : M -> N) `{Hϕ : Monoid_Morphism M N ϕ},
      ϕ ∘ fold = fold ∘ fmap F ϕ.
  Proof.
    intros ? ? ϕ; intros.
    change left (ϕ ∘ List.fold ∘ tolist F).
    change right (List.fold ∘ (tolist F ∘ fmap F ϕ)).
    rewrite <- natural.
    now rewrite (List.fold_mon_hom ϕ).
  Qed.

  Lemma foldMap_fmap {A B} `{Monoid M} {f : A -> B} {g : B -> M} :
    foldMap g ∘ fmap F f = foldMap (g ∘ f).
  Proof.
    intros. unfold foldMap.
    now rewrite <- (fun_fmap_fmap F).
  Qed.

  Theorem foldMap_hom {A} `{Monoid_Morphism M N ϕ} {f : A -> M} :
    ϕ ∘ foldMap f = foldMap (ϕ ∘ f).
  Proof.
    intros. unfold foldMap.
    reassociate <- on left.
    rewrite (fold_mon_hom ϕ).
    now rewrite <- (fun_fmap_fmap F).
  Qed.

End fold.

(** ** Folding over identity and composition functors *)
(******************************************************************************)
Section fold_monoidal_structure.

  Theorem fold_I (A : Type) `(Monoid A) : forall (a : A),
      fold a = a.
  Proof.
    intros. cbn. now rewrite (monoid_id_l).
  Qed.

End fold_monoidal_structure.

(** * Decorated listable functors *)
(******************************************************************************)

(** ** Derived operation [tolistd] *)
(******************************************************************************)
Definition tolistd F `{Decorate W F} `{Tolist F} {A} : F A -> list (W * A)
  := tolist F ∘ dec F.

(** ** General properties *)
(******************************************************************************)
Section ListableFunctor_decorated_theory.

  Context
    `{Monoid W}
    `{Fmap F} `{Decorate W F} `{Tolist F}
    `{! DecoratedFunctor W F}
    `{! ListableFunctor F}.

  #[local] Set Keyed Unification.

  (** ** Interaction between [tolistd] and [fmapd] *)
  (******************************************************************************)
  Theorem tolistd_fmapd {A B} : forall (f : W * A -> B),
      tolistd F ∘ fmapd F f = fmap list (cobind (prod W) f) ∘ tolistd F.
  Proof.
    intros. unfold fmapd, tolistd.
    reassociate <- on left; reassociate <- on right.
    change_left (tolist F ∘ (dec F ∘ fmap F f ∘ dec F)).
    rewrite <- (natural (G := F ∘ prod W)).
    reassociate <- on left. unfold_ops @Fmap_compose.
    reassociate <- on left. rewrite <- (natural (F := F)).
    reassociate -> on left. rewrite (dfun_dec_dec W F).
    change_left (fmap list (fmap (prod W) f) ∘ (tolist F ∘ fmap F (cojoin (prod W))) ∘ dec F).
    rewrite <- natural.
    reassociate <- on left. rewrite (fun_fmap_fmap list).
    reflexivity.
  Qed.

  (** ** Corollaries: [tolist] and [fmapd] *)
  (******************************************************************************)
  Theorem tolist_fmapd {A B} : forall (f : W * A -> B),
      tolist F ∘ fmapd F f = fmap list f ∘ tolistd F.
  Proof.
    intros. unfold fmapd, tolistd.
    reassociate <- on left; reassociate <- on right.
    now rewrite <- natural.
  Qed.

  (** ** Corollaries: [tolistd] and [fmap] *)
  (******************************************************************************)
  Theorem tolistd_fmap {A B} : forall (f : W * A -> B),
      tolistd F ∘ fmap F f = fmap list (fmap (prod W) f) ∘ tolistd F.
  Proof.
    intros. unfold fmapd, tolistd.
    reassociate -> on left. rewrite <- (natural (G := F ∘ prod W)).
    reassociate <- on left. unfold_ops @Fmap_compose.
    now rewrite <- (natural (F := F) (G := list)).
  Qed.

  #[local] Unset Keyed Unification.

End ListableFunctor_decorated_theory.
