From Tealeaves Require Export
     Singlesorted.Theory.Product
     LN.Leaf LN.Atom LN.AtomSet LN.AssocList
     LN.Singlesorted.Operations
     LN.Singlesorted.Theory
     Singlesorted.Classes.DecoratedTraversableModule.

Export List.ListNotations.
Open Scope list_scope.
Export DecoratedTraversableMonad.Notations.
Open Scope tealeaves_scope.
Export LN.AtomSet.Notations.
Open Scope set_scope.
Export LN.AssocList.Notations.

Set Implicit Arguments.

(** * Language definition *)
(******************************************************************************)
Parameter base_typ : Type.

Inductive typ :=
| base : base_typ -> typ
| arr : typ -> typ -> typ.

Coercion base : base_typ >-> typ.

(* we suggest more informative names for [Lam]'s arguments
than Coq otherwise infers *)
Inductive term (A : Type) :=
| Var : A -> term A
| Lam : forall (X : typ) (t : term A), term A
| Ap : term A -> term A -> term A.

(** ** Notations and automation *)
(******************************************************************************)
Module Notations.
  Notation "'λ' X ⋅ body" := (Lam X body) (at level 45).
  Notation "[ t1 ] [ t2 ]" := (Ap t1 t2) (at level 40).
  Notation "A ⟹ B" := (arr A B) (at level 40).
End Notations.

Ltac basic t :=
  induction t;
  [ reflexivity |
    simpl; match goal with H : _ |- _ => rewrite H end; reflexivity |
    simpl; do 2 match goal with H : _ |- _ => rewrite H end; reflexivity ].

(** * Functor instance *)
(******************************************************************************)
Fixpoint fmap_term {A B : Type} (f : A -> B) (t : term A) : term B :=
  match t with
  | Var a => Var (f a)
  | Lam X t => Lam X (fmap_term f t)
  | Ap t1 t2 => Ap (fmap_term f t1) (fmap_term f t2)
  end.

Instance Fmap_term : Fmap term := @fmap_term.

Theorem fmap_id : forall A, fmap term id = @id (term A).
Proof.
  intros. ext t. unfold transparent tcs. basic t.
Qed.

Theorem fmap_fmap : forall A B C (f : A -> B) (g : B -> C),
    fmap term g ∘ fmap term f = fmap term (g ∘ f).
Proof.
  intros. ext t. unfold transparent tcs.
  unfold compose. basic t.
Qed.

Instance Functor_term : Functor term :=
  {| fun_fmap_id := @fmap_id;
     fun_fmap_fmap := @fmap_fmap;
  |}.

(** ** Rewriting rules for <<fmap>> *)
(******************************************************************************)
Section fmap_term_rewrite.

  Context
    `{f : A -> B}.

  Lemma fmap_term_ap : forall (t1 t2 : term A),
      fmap term f (@Ap A t1 t2) = @Ap B (fmap term f t1) (fmap term f t2).
  Proof.
    reflexivity.
  Qed.

End fmap_term_rewrite.

(** * Monad instance *)
(******************************************************************************)
Definition ret_term {A} : A -> term A := fun a => Var a.

Fixpoint join_term {A : Type} (t : term (term A)) : term A :=
  match t with
  | Var t' => t'
  | Lam X t => Lam X (join_term t)
  | Ap t1 t2 => Ap (join_term t1) (join_term t2)
  end.

Instance Ret_term : Return term := @ret_term.

Instance Join_term : Join term := @join_term.

Theorem join_natural : forall A B (f : A -> B),
    fmap term f ∘ join term = join term ∘ fmap term (fmap term f).
Proof.
  intros. ext t. unfold transparent tcs.
  unfold compose. basic t.
Qed.

Instance: Natural (@join term _).
Proof.
  constructor.
  - apply Functor_compose.
  - typeclasses eauto.
  - apply join_natural.
Qed.

Theorem ret_natural : forall A B (f : A -> B),
    fmap term f ∘ ret term = ret term ∘ f.
Proof.
  reflexivity.
Qed.

Instance: Natural (@ret term _).
Proof.
  constructor; try typeclasses eauto.
  apply ret_natural.
Qed.

Theorem join_ret : forall A,
    join term ∘ ret term = @id (term A).
Proof.
  reflexivity.
Qed.

Theorem join_fmap_ret : forall A,
    join term ∘ fmap term (ret term) = @id (term A).
Proof.
  intros. unfold compose. unfold transparent tcs.
  ext t. basic t.
Qed.

Theorem join_join : forall A,
    join term ∘ join term = join term (A := A) ∘ fmap term (join term).
Proof.
  intros. unfold compose. unfold transparent tcs.
  ext t. basic t.
Qed.

Instance Monad_term : Monad term :=
  {| mon_join_ret := join_ret;
     mon_join_fmap_ret := join_fmap_ret;
     mon_join_join := join_join |}.

(** * Decorated instance *)
(******************************************************************************)
Fixpoint dec_term {A} (t : term A) : term (nat * A) :=
  match t with
  | Var a => Var (Ƶ, a)
  | Lam τ t => Lam τ (shift term (1, dec_term t))
  | Ap t1 t2 => Ap (dec_term t1) (dec_term t2)
  end.

Instance Decorate_term : Decorate nat term := @dec_term.

Theorem dec_natural : forall A B (f : A -> B),
    fmap term (fmap (prod nat) f) ∘ dec term = dec term ∘ fmap term f.
Proof.
  intros. unfold compose. ext t. induction t.
  - now cbn.
  - cbn -[shift]. fequal. now rewrite dec_helper_1.
  - cbn. now fequal.
Qed.

Instance: Natural (@dec nat term _).
Proof.
  constructor.
  - typeclasses eauto.
  - apply Functor_compose.
  - apply dec_natural.
Qed.

Theorem dec_extract : forall A,
    fmap term (extract (prod nat)) ∘ dec term = @id (term A).
Proof.
  intros. unfold compose. ext t. induction t.
  - reflexivity.
  - cbn -[shift]. now rewrite dec_helper_2.
  - unfold id. cbn. now fequal.
Qed.

Theorem dec_dec : forall A,
    dec term ∘ dec term = fmap term (cojoin (prod nat)) ∘ dec term (A := A).
Proof.
  intros. unfold compose. ext t. induction t.
  - reflexivity.
  - cbn -[shift]. fequal. now rewrite dec_helper_3.
  - cbn. fequal; auto.
Qed.

Instance DecoratedFunctor_term : DecoratedFunctor nat term.
Proof.
  constructor.
  - typeclasses eauto.
  - apply Monoid_Nat.
  - typeclasses eauto.
  - apply dec_dec.
  - apply dec_extract.
Qed.

Theorem dec_ret : forall A,
    dec term ∘ ret term (A := A) = ret term ∘ pair Ƶ.
Proof.
  reflexivity.
Qed.

Theorem dec_join : forall A,
    dec term ∘ join term (A := A) =
    join term ∘ fmap term (shift term) ∘ dec term ∘ fmap term (dec term).
Proof.
  intros. unfold compose. ext t. induction t.
  - cbn -[shift]. now rewrite shift_zero.
  - cbn -[shift]. fequal. now rewrite (dec_helper_4).
  - cbn. fequal; auto.
Qed.

Instance DecoratedMonad_term : DecoratedMonad nat term.
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply dec_ret.
  - apply dec_join.
Qed.

(** ** Rewriting rules for <<dec>> *)
(******************************************************************************)
Section dec_term_rewrite.

  Context
    `{f : A -> B}.

  Lemma dec_term1 : forall (x : A),
      dec term (Var x) = Var (0, x).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term21 : forall (X : typ) (t : term A),
      dec term (Lam X t) = shift term (1, Lam X (dec term t)).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term22 : forall (X : typ) (t : term A),
      dec term (Lam X t) = Lam X (shift term (1, dec term t)).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term3 : forall (t1 t2 : term A),
      dec term (Ap t1 t2) = Ap (dec term t1) (dec term t2).
  Proof.
    reflexivity.
  Qed.

End dec_term_rewrite.

(** * Traversable instance *)
(******************************************************************************)
Import Applicative.Notations.

Fixpoint dist_term `{Fmap F} `{Pure F} `{Mult F} {A : Type}
         (t : term (F A)) : F (term A) :=
  match t with
  | Var a => fmap F (@Var A) a
  | Lam X t => fmap F (Lam X) (dist_term t)
  | Ap t1 t2 => (pure F (@Ap A))
                 <⋆> dist_term t1
                 <⋆> dist_term t2
  end.

Instance: Dist term := @dist_term.

(** ** Rewriting lemmas for <<dist>> *)
(******************************************************************************)
Section term_dist_rewrite.

  Context
    `{Applicative G}.

  Variable (A : Type).

  Lemma dist_term_var_1 : forall (x : G A),
    dist term G (@Var (G A) x) = pure G (@Var A) <⋆> x.
  Proof.
    intros. cbn. now rewrite fmap_to_ap.
  Qed.

  Lemma dist_term_var_2 : forall (x : G A),
    dist term G (@Var (G A) x) = fmap G (@Var A) x.
  Proof.
    reflexivity.
  Qed.

  Lemma dist_term_lam_1 : forall (X : typ) (t : term (G A)),
      dist term G (Lam X t) = pure G (Lam X) <⋆> (dist term G t).
  Proof.
    intros. cbn. now rewrite fmap_to_ap.
  Qed.

  Lemma dist_term_lam_2 : forall (X : typ) (t : term (G A)),
      dist term G (Lam X t) = fmap G (Lam X) (dist term G t).
  Proof.
    reflexivity.
  Qed.

  Lemma dist_term_ap_1 : forall (t1 t2 : term (G A)),
      dist term G (Ap t1 t2) =
      (pure G (@Ap A))
        <⋆> dist term G t1
        <⋆> dist term G t2.
  Proof.
    reflexivity.
  Qed.

  Lemma dist_term_ap_2 : forall (t1 t2 : term (G A)),
      dist term G (Ap t1 t2) =
      (fmap G (@Ap A) (dist term G t1)
            <⋆> dist term G t2).
  Proof.
    intros. rewrite dist_term_ap_1.
    now rewrite fmap_to_ap.
  Qed.

End term_dist_rewrite.

Section dist_term_properties.

  Context
    `{Applicative G}.

  Lemma dist_natural_term : forall `(f : A -> B),
      fmap (G ∘ term) f ∘ dist term G =
      dist term G ∘ fmap (term ∘ G) f.
  Proof.
    intros; cbn. ext t.
    unfold_ops @Fmap_compose. unfold compose. induction t.
    + cbn. compose near a. now rewrite 2(fun_fmap_fmap G).
    + cbn. rewrite <- IHt.
      compose near (dist term G t).
      now rewrite 2(fun_fmap_fmap G).
    + rewrite (dist_term_ap_2).
      rewrite (fmap_term_ap).
      rewrite (dist_term_ap_2).
      rewrite <- IHt1, <- IHt2.
      rewrite <- ap7.
      rewrite ap6. fequal.
      compose near (dist term G t1).
      rewrite (fun_fmap_fmap G).
      rewrite (fun_fmap_fmap G).
      compose near (dist term G t1) on right.
      rewrite (fun_fmap_fmap G).
      reflexivity.
  Qed.

  Lemma dist_morph_term : forall `{ApplicativeMorphism G1 G2 ϕ} A,
      dist term G2 ∘ fmap term (ϕ A) = ϕ (term A) ∘ dist term G1.
  Proof.
    intros. ext t. unfold compose. induction t.
    - cbn. now rewrite <- (appmor_natural G1 G2).
    - cbn. rewrite IHt.
      now rewrite (appmor_natural G1 G2).
    - rewrite fmap_term_ap. inversion H9.
      rewrite dist_term_ap_2.
      rewrite IHt1. rewrite IHt2.
      rewrite dist_term_ap_2. rewrite (ap_morphism_1).
      fequal. now rewrite <- (appmor_natural).
  Qed.

  Lemma dist_unit_term : forall (A : Type),
      dist term (fun A => A) = @id (term A).
  Proof.
    intros. ext t. induction t.
    - reflexivity.
    - cbn. rewrite IHt. reflexivity.
    - cbn. rewrite IHt1, IHt2.
      reflexivity.
  Qed.

  #[local] Set Keyed Unification.
  Lemma dist_linear_term : forall `{Applicative G1} `{Applicative G2} (A : Type),
      dist term (G1 ∘ G2) =
      fmap G1 (dist term G2) ∘ dist term G1 (A := G2 A).
  Proof.
    intros. unfold compose. ext t. induction t.
    - cbn. compose near a on right. now rewrite (fun_fmap_fmap G1).
    - cbn. rewrite IHt. compose near (dist term G1 t).
      change (fmap (G1 ○ G2) (Lam X)) with (fmap G1 (fmap G2 (@Lam A X))).
      rewrite (fun_fmap_fmap G1).
      now rewrite (fun_fmap_fmap G1).
    - rewrite dist_term_ap_2.
      rewrite (dist_term_ap_2 (G := G1 ○ G2)).
      rewrite ap6.
      compose near ((dist term G1 t1)).
      rewrite (fun_fmap_fmap G1).
      rewrite (ap_compose_3 G2 G1).
      rewrite IHt1, IHt2.
      rewrite <- ap7. fequal.
      repeat (compose near (dist term G1 t1) on left;
              rewrite (fun_fmap_fmap G1)).
      fequal. ext s1 s2. unfold compose; cbn.
      unfold precompose. now rewrite (fmap_to_ap).
  Qed.
  #[local] Unset Keyed Unification.

  Theorem trvmon_ret_term `{Applicative G} :
    `(dist term G ∘ ret term (A := G A) = fmap G (ret term)).
  Proof.
    intros. ext x. reflexivity.
  Qed.

  #[local] Set Keyed Unification.
  Theorem trvmon_join_term :
    `(dist term G ∘ join term = fmap G (join term) ∘ dist (term ∘ term) G (A := A)).
  Proof.
    intros. ext t. unfold compose. induction t.
    - cbn. compose near (dist term G a).
      rewrite (fun_fmap_fmap G).
      replace (join term ∘ Var (A := term A)) with (@id (term A)).
      now rewrite (fun_fmap_id G).
      apply (join_ret).
    - cbn. rewrite IHt.
      unfold_ops @Dist_compose. unfold compose.
      compose near (dist term G (fmap term (dist term G) t)).
      rewrite (fun_fmap_fmap G).
      rewrite (fun_fmap_fmap G).
      reflexivity.
    - cbn. rewrite IHt1, IHt2.
      unfold_ops @Dist_compose. unfold compose.
      rewrite <- fmap_to_ap.
      rewrite <- fmap_to_ap.
      rewrite <- ap7. rewrite ap6.
      fequal. compose near ((dist term G (fmap term (dist term G) t1))).
      repeat rewrite (fun_fmap_fmap G).
      compose near ((dist term G (fmap term (dist term G) t1))) on left.
      rewrite (fun_fmap_fmap G).
      fequal.
  Qed.
  #[local] Set Keyed Unification.

End dist_term_properties.

Instance TraversableFunctor_term : TraversableFunctor term :=
  {| dist_natural := @dist_natural_term;
     dist_morph := @dist_morph_term;
     dist_linear := @dist_linear_term;
     dist_unit := @dist_unit_term;
  |}.

Instance TraversableMonad_term : TraversableMonad term :=
  {| trvmon_ret := @trvmon_ret_term;
     trvmon_join := @trvmon_join_term;
  |}.

(** * Listable instance (redundant) *)
(******************************************************************************)
Section term_listable_instance.

  Fixpoint tolist_term {A} (t : term A) : list A :=
    match t with
    | Var a => [ a ]
    | Lam X t => tolist_term t
    | Ap t1 t2 => tolist_term t1 ++ tolist_term t2
    end.

  Instance Tolist_term : Tolist term := @tolist_term.

  Theorem tolist_natural : forall (A B : Type) (f : A -> B),
      fmap list f ∘ tolist term = tolist term ∘ fmap term f.
  Proof.
    intros. unfold compose. ext t. induction t.
    - reflexivity.
    - cbn. now rewrite IHt.
    - cbn. rewrite <- IHt1, <- IHt2.
      now autorewrite with tea_list.
  Qed.

  Instance: Natural (@tolist _ _).
  Proof.
    constructor; try typeclasses eauto.
    apply tolist_natural.
  Qed.

  (** ** Shapeliness *)
  (******************************************************************************)
  Theorem tolist_equal : forall {A B : Type} {f g : A -> B} (t : term A),
      List.map f (tolist term t) = List.map g (tolist term t) ->
      fmap term f t = fmap term g t.
  Proof.
    intros.
    induction t.
    - cbn in *. inversion H. reflexivity.
    - cbn in *. f_equal; auto.
    - cbn in *. apply List.fmap_app_inv in H. destruct H.
      f_equal; auto.
  Qed.

  Theorem shapeliness_term : forall {A : Type} (t1 t2 : term A),
      shape term t1 = shape term t2 /\
      tolist term t1 = tolist term t2 ->
      t1 = t2.
  Proof.
    introv [Hyp1 Hyp2]. generalize dependent t2.
    induction t1; intros t2; destruct t2; try discriminate; intros.
    - now preprocess.
    - preprocess. erewrite IHt1; eauto.
    - preprocess. cbn in *.
      assert (t1_1 = t2_1).
      { apply IHt1_1; auto. eauto using (shape_l term). }
      assert (t1_2 = t2_2).
      { apply IHt1_2; auto. eauto using (shape_r term). }
      now subst.
  Qed.

  Instance ListableFunctor_term : ListableFunctor term :=
    {| lfun_shapeliness := @shapeliness_term; |}.

  Theorem tolist_ret : forall (A : Type),
      tolist term ∘ ret term (A := A) = one.
  Proof.
    reflexivity.
  Qed.

  Theorem tolist_join : forall (A : Type),
      tolist term ∘ join term =
      join list (A := A) ∘ tolist term ∘ fmap term (tolist term).
  Proof.
    intros. unfold compose. ext t. induction t.
    - cbn. auto with datatypes.
    - cbn. now rewrite IHt.
    - cbn. rewrite IHt1, IHt2.
      now autorewrite with tea_list.
  Qed.

  Instance ListableMonad_term : ListableMonad term :=
    {| lmon_ret := tolist_ret;
       lmon_join := tolist_join; |}.

End term_listable_instance.

(** ** Rewriting lemmas for <<tolist>>, <<toset>> *)
(******************************************************************************)
Section term_list_rewrite.

  Variable (A : Type).

  Lemma tolist_term_spec : forall (t : term A),
      tolist term t = tolist_term t.
  Proof.
    intros. induction t.
    + reflexivity.
    + cbn. rewrite <- IHt.
      reflexivity.
    + cbn. rewrite <- IHt1, <- IHt2. reflexivity.
  Qed.

  Lemma tolist_term_1 : forall (x : A),
    tolist_term (Var x) = [x].
  Proof.
    reflexivity.
  Qed.

  Lemma tolist_term_2 : forall (X : typ) (t : term A),
    tolist_term (Lam X t) = tolist_term t.
  Proof.
    reflexivity.
  Qed.

  Lemma tolist_term_3 : forall (t1 t2 : term A),
      tolist_term (Ap t1 t2) = tolist_term t1 ++ tolist_term t2.
  Proof.
    reflexivity.
  Qed.

  Lemma in_term_1 : forall (x y : A),
      x ∈ Var y <-> x = y.
  Proof.
    intros; cbn. intuition.
  Qed.

  Lemma in_term_2 : forall (y : A) (X : typ) (t : term A),
    y ∈ (Lam X t) = y ∈ t.
  Proof.
    reflexivity.
  Qed.

  Lemma in_term_3 : forall (t1 t2 : term A) (y : A),
      y ∈ (Ap t1 t2) <-> y ∈ t1 \/ y ∈ t2.
  Proof.
    intros. unfold_ops @Toset_Tolist.
    unfold compose. rewrite 3(tolist_term_spec).
    rewrite tolist_term_3. now simpl_list.
  Qed.

End term_list_rewrite.

(** * Compatibility between decoration and traversal *)
(******************************************************************************)
Lemma dtfun_compat_term1 : forall `{Applicative G} (X : typ) {A},
    fmap G (dec term ∘ Lam X) ∘ δ term G (A := A) =
    fmap G (curry (shift term) 1 ∘ Lam X) ∘ fmap G (dec term) ∘ δ term G.
Proof.
  intros. rewrite (fun_fmap_fmap G). reflexivity.
Qed.

Theorem dtfun_compat_term :
        `(forall {A : Type} `{Applicative G},
             dist term G ∘ fmap term (strength G) ∘ dec term (A := G A) =
             fmap G (dec term) ∘ dist term G).
Proof.
  intros. ext t. unfold compose. induction t.
  - cbn. compose near a. now rewrite 2(fun_fmap_fmap G).
  - cbn. do 2 (compose near (dec term t) on left;
               rewrite (fun_fmap_fmap term)).
    reassociate <-. rewrite (strength_shift_1).
    rewrite <- (fun_fmap_fmap term); unfold compose.
    change (fmap term (fmap G ?f)) with (fmap (term ∘ G) f).
    compose near ((fmap term (σ G) (dec term t))).
    rewrite <- (dist_natural term); unfold compose.
    rewrite IHt. compose near (δ term G t).
    rewrite (fun_fmap_fmap G).
    compose near (δ term G t) on left.
    unfold_ops @Fmap_compose; rewrite 2(fun_fmap_fmap G).
    fequal. ext t'; unfold compose; cbn.
    compose near (dec term t') on right; now rewrite (fun_fmap_fmap term).
  - cbn. rewrite IHt1, IHt2. rewrite ap6. rewrite ap6.
    rewrite ap5. rewrite <- ap7.
    rewrite (app_pure_natural G). rewrite <- (fmap_to_ap).
    compose near (δ term G t1) on left. rewrite (fun_fmap_fmap G).
    reflexivity.
Qed.

Instance : DecoratedTraversableFunctor nat term :=
  {| dtfun_compat := @dtfun_compat_term |}.

Instance : DecoratedTraversableMonad nat term := {}.

Existing Instance RightAction_Join.
Instance : DecoratedTraversableModule nat term term
  := DecoratedTraversableModule_Monad term.

(** * Locally nameless operations *)
(******************************************************************************)
Import Notations.
Import LN.Singlesorted.Operations.Notations.

Definition Vb x := Var (Bd x) : term leaf.
Definition Vf n := Var (Fr n) : term leaf.

Coercion Vb : nat >-> term.
Coercion Vf : atom >-> term.

Section test_notations.

  Context
    (x y z : atom)
    (X : typ).

  Check 1.
  Check (Vb 1 : term leaf).
  Check Vb 1.
  Check (λ X ⋅ Vb 1).
  Check (λ X ⋅ (Vb 1 : term leaf)).
  Check (λ X ⋅ 1).
  Check (λ X ⋅ x).
  Check [λ X ⋅ x][0].
  Check (λ X ⋅ [x][0]).
  Check [λ X ⋅ [0] [y]] [2].
  Check [λ X ⋅ x ][λ X ⋅ 0 ].
  Check [ x ][ λ X ⋅ 0 ].
  Check [ λ X ⋅ [y][2] ][ λ X ⋅ 1 ].
  Check [1][x].
  Check (λ X ⋅ [1][x]).
  Check [λ X ⋅ 0][λ X ⋅ [1][x]].
  Check (λ X ⋅ 0) '{x ~> (λ X ⋅ x)}.
  (* Fail Timeout 1 Check (λ X ⋅ 0) '( Fr x ).
  Fail Timeout 1 Check (λ X ⋅ 0) '( x ). *)
  Check (λ X ⋅ 0) '( Var (Fr x) ).
  Check (λ X ⋅ 0) '( Vf x ).
  Check (λ X ⋅ 0) '( λ X ⋅ x ).

  Compute (λ X ⋅ 0).
  Check (λ X ⋅ 0) '{x ~> (λ X ⋅ x)}.
  Compute (λ X ⋅ 0) '{x ~> (λ X ⋅ x)}.
  Compute (λ X ⋅ x) '{x ~> (λ X ⋅ [1][y])}.
  Goal (λ X ⋅ x) '{x ~> (λ X ⋅ [1][y])} = (λ X ⋅ λ X ⋅ [1][y]).
  Proof.
    cbn. compare values x and x.
  Qed.

  Compute (λ X ⋅ 0).
  Check (λ X ⋅ 0) '(λ X ⋅ x).
  Compute (λ X ⋅ 0) '(λ X ⋅ x).
  Compute (λ X ⋅ 1) '(λ X ⋅ x).
  Compute (λ X ⋅ 2) '(λ X ⋅ x).
  Compute (λ X ⋅ x) '(λ X ⋅ [1][y]).
  Compute ([0] [λ X ⋅ [x][1]]) '(λ X ⋅ z).
  Compute ([0] [λ X ⋅ [x][0]]) '(λ X ⋅ z).
  Compute ('[x] λ X ⋅ x).
  Compute ('[x] λ X ⋅ y).

  Goal ('[x] (Var (Fr x)) = Var (Bd 0) ).
  Proof. cbn. unfold compose. cbn. compare values x and x. Qed.
  Goal ( ('[x] λ X ⋅ x) = (λ X ⋅ 1)).
  Proof. cbn. unfold compose. simpl. compare values x and x. Qed.
  Goal (x <> y -> ('[x] λ X ⋅ y) = (λ X ⋅ y)).
  Proof. intro. cbn. unfold compose. simpl. compare values x and y. Qed.

End test_notations.

(** * Rewriting lemmas for high-level operations *)
(******************************************************************************)

(** ** Rewriting lemmas for <<free>>, <<freeset>> *)
(******************************************************************************)
Section term_free_rewrite.

  Variable (A : Type).

  Lemma term_free11 : forall (b : nat) (x : atom),
      x ∈ free term (Var (Bd b)) <-> False.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma term_free12 : forall (y : atom) (x : atom),
      x ∈ free term (Var (Fr y)) <-> x = y.
  Proof.
    intros. cbn. intuition.
  Qed.

  Lemma term_free2 : forall (x : atom) (t : term leaf) (X : typ),
      x ∈ free term (Lam X t) <-> x ∈ free term t.
  Proof.
    intros. rewrite in_free_iff. rewrite in_term_2.
    now rewrite <- in_free_iff.
  Qed.

  Lemma term_free3 : forall (x : atom) (t1 t2 : term leaf),
      x ∈ free term (Ap t1 t2) <-> x ∈ free term t1 \/ x ∈ free term t2.
  Proof.
    intros. rewrite in_free_iff. rewrite in_term_3.
    now rewrite <- 2(in_free_iff).
  Qed.

  Lemma term_in_freeset11 : forall (b : nat) (x : atom),
      AtomSet.In x (freeset term (Var (Bd b))) <-> False.
  Proof.
    intros. rewrite <- free_iff_freeset.
    now rewrite term_free11.
  Qed.

  Lemma term_in_freeset12 : forall (y : atom) (x : atom),
      AtomSet.In x (freeset term (Var (Fr y))) <-> x = y.
  Proof.
    intros. rewrite <- free_iff_freeset.
    now rewrite term_free12.
  Qed.

  Lemma term_in_freeset2 : forall (x : atom) (t : term leaf) (X : typ),
      AtomSet.In x (freeset term (Lam X t)) <-> AtomSet.In x (freeset term t).
  Proof.
    intros. rewrite <- 2(free_iff_freeset). now rewrite term_free2.
  Qed.

  Lemma term_in_freeset3 : forall (x : atom) (t1 t2 : term leaf),
      AtomSet.In x (freeset term (Ap t1 t2)) <-> AtomSet.In x (freeset term t1) \/ AtomSet.In x (freeset term t2).
  Proof.
    intros. rewrite <- 3(free_iff_freeset). now rewrite term_free3.
  Qed.

  Lemma term_freeset11 : forall (b : nat) (x : atom),
      freeset term (Var (Bd b)) [=] ∅.
  Proof.
    intros. fsetdec.
  Qed.

  Lemma term_freeset12 : forall (y : atom),
      freeset term (Var (Fr y)) [=] {{ y }}.
  Proof.
    intros. cbn. fsetdec.
  Qed.

  Lemma term_freeset2 : forall (t : term leaf) (X : typ),
      freeset term (Lam X t) [=] freeset term t.
  Proof.
    intros. cbn. fsetdec.
  Qed.

  Lemma term_freeset3 : forall (t1 t2 : term leaf),
      freeset term (Ap t1 t2) [=] freeset term t1 ∪ freeset term t2.
  Proof.
    intros. unfold AtomSet.Equal; intro x.
    rewrite term_in_freeset3. fsetdec.
  Qed.

End term_free_rewrite.

(** ** Rewriting lemmas for <<∈d>> *)
(******************************************************************************)
Section term_ind_rewrite.

  Lemma term_ind1 : forall (l1 l2 : leaf) (n : nat),
      (n, l1) ∈d (Var l2) <-> n = Ƶ /\ l1 = l2.
  Proof.
    introv. unfold tosetd, compose. rewrite dec_term1.
    rewrite in_term_1. split; intros; now preprocess.
  Qed.

  Lemma term_ind21 : forall (t : term leaf) (l : leaf) (n : nat) (X : typ),
      (n, l) ∈d (λ X ⋅ t) <-> (n - 1, l) ∈d t /\ n <> 0.
  Proof.
    introv. unfold tosetd, compose.
    rewrite dec_term22. rewrite in_term_2.
    rewrite (in_shift_iff term). unfold_ops @Monoid_op_plus.
    split.
    + intros [w2 [hyp1 hyp2]]. subst.
      now replace (1 + w2 - 1) with w2 by lia.
    + intros [hyp1 hyp2]. exists (n - 1). split; now try lia.
  Qed.

  Lemma term_ind22 : forall (t : term leaf) (l : leaf) (n : nat) (X : typ),
      (n, l) ∈d (λ X ⋅ t) <-> exists m, (m, l) ∈d t /\ n = S m.
  Proof.
    introv. rewrite term_ind21. split.
    + introv [hyp1 hyp2]. exists (n - 1). split; now try lia.
    + intros [m [hyp1 hyp2]]. split; try lia. subst.
      now replace (S m - 1) with m by lia.
  Qed.

  Lemma term_ind3 : forall (t1 t2 : term leaf) (n : nat) (l : leaf),
      (n, l) ∈d ([t1][t2]) <-> (n, l) ∈d t1 \/ (n, l) ∈d t2.
  Proof.
    introv. unfold tosetd, compose. rewrite dec_term3.
    now rewrite in_term_3.
  Qed.

End term_ind_rewrite.

(** ** Rewriting lemmas for <<open>>, <<∈ open>> *)
(******************************************************************************)
Section term_open_rewrite.

  Lemma term_in_open11 : forall (n : nat) (l : leaf) (x : atom) (t : term leaf),
    (n, l) ∈d (t '(Var (Fr x))) <-> exists (n1 : nat) (l1 : leaf),
      (n1, l1) ∈d t /\ ( (is_opened (n1, l1) /\ l1 = Fr x)
                        \/ (~ is_opened (n1, l1) /\ n = n1) ).
  Proof.
    intros. rewrite ind_open_iff. split.
    - intros [l1 [n1 [n2 [G1 [G2 G3]]]]].
      exists n1 l1. subst. splits; auto.
      right. split.
      + cbn in G2. destruct l1. cbn. auto.
        compare naturals n and n1.
  Abort.

End term_open_rewrite.

(** ** Rewriting lemmas for <<subst>> *)
(******************************************************************************)

(** ** Rewriting lemmas for <<locally_closed>> *)
(******************************************************************************)
Theorem term_lc_gap11 : forall (n : nat) (m : nat),
    locally_closed_gap term m (Var (Bd n)) <-> n < m.
Proof.
  intros. unfold locally_closed_gap. split.
  - intros. specialize (H 0 (Bd n)).
    rewrite term_ind1 in H. specialize (H (ltac:(intuition))).
    apply H.
  - intros. cbn. rewrite term_ind1 in H0. destruct H0; subst.
    now simpl_monoid.
Qed.

Theorem term_lc_gap12 : forall (x : atom) (m : nat),
    locally_closed_gap term m (Var (Fr x)) <-> True.
Proof.
  intros. unfold locally_closed, locally_closed_gap.
  setoid_rewrite term_ind1. intuition.
  now subst.
Qed.

Theorem term_lc_gap2 : forall (X : typ) (t : term leaf) (m : nat),
    locally_closed_gap term m (Lam X t) <-> locally_closed_gap term (S m) t.
Proof.
  intros. unfold locally_closed, locally_closed_gap.
  setoid_rewrite term_ind22. split.
  - intros. destruct l; cbn; auto.
    cbn. specialize (H (S w) (Bd n)). cbn in H.
    assert (exists m : nat, (m, Bd n) ∈d t /\ S w = S m) by
        (now exists w).
    specialize (H H1). unfold_monoid. lia.
  - introv hyp1 [m' [hyp2 hyp3]]. destruct l; subst; cbn. auto.
    specialize (hyp1 m' (Bd n) hyp2). cbn in hyp1. unfold_monoid. lia.
Qed.

Theorem term_lc_gap3 : forall (t1 t2 : term leaf) (m : nat),
    locally_closed_gap term m ([t1][t2]) <-> locally_closed_gap term m t1 /\ locally_closed_gap term m t2.
Proof.
  intros. unfold locally_closed, locally_closed_gap.
  setoid_rewrite term_ind3. intuition.
Qed.

Theorem term_lc11 : forall (n : nat),
    locally_closed term (Var (Bd n)) <-> False.
Proof.
  intros. unfold locally_closed. now (rewrite term_lc_gap11).
Qed.

Theorem term_lc12 : forall (x : atom),
    locally_closed term (Var (Fr x)) <-> True.
Proof.
  intros. unfold locally_closed. now (rewrite term_lc_gap12).
Qed.

Theorem term_lc2 : forall (X : typ) (t : term leaf),
    locally_closed term (Lam X t) <-> locally_closed_gap term 1 t.
Proof.
  intros. unfold locally_closed. now (rewrite term_lc_gap2).
Qed.

Theorem term_lc3 : forall (t1 t2 : term leaf),
    locally_closed term ([t1][t2]) <-> locally_closed term t1 /\ locally_closed term t2.
Proof.
  intros. unfold locally_closed.
  now setoid_rewrite term_lc_gap3.
Qed.

(** * Typing judgments for STLC *)
(******************************************************************************)
Definition ctx := list (atom * typ).

Reserved Notation "Γ ⊢ t : S" (at level 90, t at level 99).

Inductive Judgment : ctx -> term leaf -> typ -> Prop :=
| j_var :
    forall Γ (x : atom) (A : typ),
      uniq Γ ->
      (x, A) ∈ Γ ->
      Γ ⊢ Var (Fr x) : A
| j_abs :
    forall (L : AtomSet.t) Γ (A B : typ) (t : term leaf),
      (forall x : atom, ~ AtomSet.In x L -> Γ ++ x ~ A ⊢ t '(Var (Fr x)) : B) ->
      Γ ⊢ λ A ⋅ t : A ⟹ B
| j_app :
    forall Γ (t1 t2 : term leaf) (A B : typ),
      Γ ⊢ t1 : A ⟹ B ->
      Γ ⊢ t2 : A ->
      Γ ⊢ [t1][t2] : B
where "Γ ⊢ t : A" := (Judgment Γ t A).
