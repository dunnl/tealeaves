From Tealeaves Require Export
  Classes.Traversable.Monad
  Functors.Sets
  Definitions.List.

Import List.ListNotations.
Import Monoid.Notations.
Import Sets.Notations.
Import Applicative.Notations.

Create HintDb tea_list.

#[local] Generalizable Variables M A B G ϕ.
#[local] Arguments bindt T {U}%function_scope {Bindt} G%function_scope {H H0 H1} (A B)%type_scope _%function_scope _.

(** * [list] traversable monad *)
(******************************************************************************)
#[export] Instance Return_list : Return list := fun A a => cons a nil.

Fixpoint bindt_list (G : Type -> Type) `{Map G} `{Pure G} `{Mult G} (A B : Type) (f : A -> G (list B)) (l : list A)
  : G (list B) :=
  match l with
  | nil => pure G (@nil B)
  | x :: xs =>
      pure G (@List.app B) <⋆> (f x) <⋆> (bindt_list G A B f xs)
  end.

#[export] Instance Bindt_list : Bindt list list := @bindt_list.

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
    rewrite (ap3).
    rewrite <- (ap4).
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
      repeat rewrite (ap2).
      rewrite ap3.
      repeat rewrite <- ap4.
      repeat rewrite ap2.
      repeat fequal.
      ext x y z. unfold compose.
      now rewrite (List.app_assoc).
  Qed.

End bindt_rewriting_lemmas.

Section bindt_laws.

  Context
    (G : Type -> Type)
    `{Applicative G}
    (G1 G2 : Type -> Type)
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
        bindt list (G1 ∘ G2) A C (kc3 list G1 G2 g f).
  Proof.
    intros. ext l. induction l.
    - unfold compose; cbn.
      rewrite (app_pure_natural G1).
      rewrite (bindt_list_nil).
      reflexivity.
    - unfold compose at 1.
      rewrite (bindt_list_cons).
      rewrite map_to_ap.
      do 3 rewrite <- ap4.
      do 4 rewrite (ap2).
      rewrite (bindt_list_cons).
      rewrite <- IHl.
      unfold compose at 7.
      do 2 rewrite (ap_compose1 G2 G1).
      unfold_ops @Pure_compose.
      rewrite map_to_ap.
      rewrite <- ap4.
      rewrite <- ap4.
      rewrite <- ap4.
      rewrite <- ap4.
      repeat rewrite (ap2).
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

  Lemma list_morph : forall (ϕ : forall A : Type, G1 A -> G2 A)
                       (morph : ApplicativeMorphism G1 G2 ϕ),
      forall (A B : Type) (f : A -> G1 (list B)),
        ϕ (list B) ∘ bindt list G1 A B f = bindt list G2 A B (ϕ (list B) ∘ f).
  Proof.
    intros. unfold compose at 1 2. ext l.
    inversion morph.
    induction l.
    - cbn. rewrite appmor_pure. reflexivity.
    - cbn. do 2 rewrite ap_morphism_1.
      rewrite appmor_pure.
      rewrite IHl.
      reflexivity.
  Qed.

End bindt_laws.

  #[export] Instance TM_list : TraversableMonad list :=
  {| ktm_bindt0 := list_bindt0;
    ktm_bindt1 := list_bindt1;
    ktm_bindt2 := list_bindt2;
    ktm_morph := list_morph;
  |}.

#[export] Hint Rewrite bindt_list_nil bindt_list_cons bindt_list_one bindt_list_app :
  tea_list.

#[export] Instance Map_list : Map list := Traversable.Monad.DerivedInstances.Map_Bindt list.
#[export] Instance Bind_list : Bind list list := Traversable.Monad.DerivedInstances.Bind_Bindt list.
#[export] Instance Traverse_list : Traverse list := Traversable.Monad.DerivedInstances.Traverse_Bindt list.
#[export] Instance Functor_list : Functor list := Traversable.Monad.DerivedInstances.Functor_TM list.
#[export] Instance Monad_list : Bind list list := Traversable.Monad.DerivedInstances.Bind_Bindt list.
#[export] Instance TraversableFunctor_list : Traverse list := Traversable.Monad.DerivedInstances.Traverse_Bindt list.

(** ** Rewriting lemmas for <<map>> *)
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
    unfold Map_list.
    rewrite (DerivedInstances.map_to_bindt list).
    rewrite (bindt_list_app (fun A => A)).
    reflexivity.
  Qed.

End map_list_rw.

#[export] Hint Rewrite @map_list_nil @map_list_cons
     @map_list_one @map_list_app : tea_list.

Tactic Notation "simpl_list" := (autorewrite with tea_list).
Tactic Notation "simpl_list" "in" hyp(H) := (autorewrite with tea_list H).
Tactic Notation "simpl_list" "in" "*" := (autorewrite with tea_list in *).

(** ** [map] is a monoid homomorphism *)
(******************************************************************************)
#[export, program] Instance Monmor_list_fmap `(f : A -> B) :
  Monoid_Morphism (map list f) := {| monmor_op := map_list_app f; |}.

(** ** Other properties of <<fold>> *)
(******************************************************************************)

Lemma fold_mon_hom : forall `(ϕ : M1 -> M2) `{Monoid_Morphism M1 M2 ϕ},
    ϕ ∘ fold M1 = fold M2 ∘ map list ϕ.
Proof.
  intros ? ? ϕ ? ? ? ? ?. unfold compose. ext l.
  induction l as [| ? ? IHl].
  - cbn. apply (monmor_unit ϕ).
  - cbn. now rewrite (monmor_op ϕ), IHl.
Qed.

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
  unfold shape. now rewrite (fun_map_map F).
Qed.

Theorem shape_shape `{Functor F} : forall A (t : F A),
    shape F (shape F t) = shape F t.
Proof.
  intros.  compose near t on left.
  unfold shape. now rewrite (fun_map_map F).
Qed.

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
    intros. unfold shape. now rewrite map_list_app.
  Qed.

  Lemma shape_nil_iff : forall A (l : list A),
      shape list l = @nil unit <-> l = [].
  Proof.
    induction l. intuition.
    split; intro contra; now inverts contra.
  Qed.

End list_shape_rewrite.

#[export] Hint Rewrite @shape_nil @shape_cons @shape_one @shape_app : tea_rw_list.

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

Section ops.

  Context
    (F : Type -> Type).

  Class Tolist :=
    tolist : F ⇒ list.

  Class Tolist_ctx (W : Type) :=
    tolist_ctx : forall (A : Type), F A -> list (W * A).

End ops.
