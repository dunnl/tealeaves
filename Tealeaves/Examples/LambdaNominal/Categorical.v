From Tealeaves Require Export
  Examples.LambdaNominal.Syntax
  Classes.Categorical.DecoratedMonad (shift).

From Tealeaves Require
  Classes.Categorical.DecoratedTraversableMonadPoly
  Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly
  Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly
  Adapters.CategoricalToKleisli.DecoratedTraversableMonad
  Adapters.PolyToMono.Kleisli.DecoratedTraversableMonad
  Adapters.PolyToMono.Kleisli.DecoratedTraversableFunctor
  Adapters.PolyToMono.Kleisli.DecoratedFunctor.

Import List.ListNotations.

#[local] Generalizable Variables G.

(*|
============================================
Decomposition into categorical components
============================================
|*)

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Map
+++++++++++++++++++++++++++++++++++++++++++++++
|*)
Fixpoint map2_term {B1 V1 B2 V2: Type} (ρ: B1 -> B2) (σ: V1 -> V2)
  (t: term B1 V1): term B2 V2 :=
  match t with
  | tvar v => (@tvar B2 V2) (σ v)
  | lam v body => lam (ρ v) (map2_term ρ σ body)
  | tap t1 t2 => tap (map2_term ρ σ t1) (map2_term ρ σ t2)
  end.

Lemma map2_id_term: forall (B1 V1: Type),
    map2_term (@id B1) (@id V1) = @id (term B1 V1).
Proof.
  intros. ext t. induction t.
  - reflexivity.
  - cbn. now rewrite IHt.
  - cbn. now rewrite IHt1, IHt2.
Qed.

Lemma map2_map2_term: forall (B1 V1 B2 V2 b3 v3: Type)
                      (ρ1: B1 -> B2) (σ1: V1 -> V2) (ρ2: B2 -> b3) (σ2: V2 -> v3),
    map2_term ρ2 σ2 ∘ map2_term ρ1 σ1 = map2_term (ρ2 ∘ ρ1) (σ2 ∘ σ1).
Proof.
  intros. ext t. induction t.
  - reflexivity.
  - cbn. compose near t on left. now rewrite IHt.
  - cbn.
    compose near t1 on left. rewrite IHt1.
    compose near t2 on left. rewrite IHt2.
    reflexivity.
Qed.

#[export] Instance Map2_term: Map2 term.
Proof.
  intros A1 B1 A2 B2 f1 f2.
  apply (map2_term f1 f2).
Defined.

Section map_term_rewriting.

  Context
    {B1 V1 B2 V2: Type}
      (ρ: B1 -> B2)
      (σ: V1 -> V2).

  Lemma map2_term_rw1: forall (v: V1),
      map2 ρ σ (tvar (B := B1) v) = tvar (σ v).
  Proof.
    reflexivity.
  Qed.

  Lemma map2_term_rw2: forall (b: B1) (body: term B1 V1),
      map2 ρ σ (lam b body) = lam (ρ b) (map2 ρ σ body).
  Proof.
    reflexivity.
  Qed.

  Lemma map2_term_rw3: forall (t1 t2: term B1 V1),
      map2 ρ σ (tap t1 t2) = tap (map2 ρ σ t1) (map2 ρ σ t2).
  Proof.
    reflexivity.
  Qed.

End map_term_rewriting.


#[export] Instance Functor2_term: Functor2 term.
Proof.
  constructor.
  - intros. ext t. induction t.
    + reflexivity.
    + rewrite map2_term_rw2.
      now rewrite IHt.
    + rewrite map2_term_rw3.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  - intros. unfold compose. ext t.
    induction t.
    + reflexivity.
    + rewrite map2_term_rw2.
      rewrite map2_term_rw2.
      rewrite IHt.
      reflexivity.
    + rewrite map2_term_rw3.
      rewrite map2_term_rw3.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
Defined.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Decoration
+++++++++++++++++++++++++++++++++++++++++++++++
|*)
Fixpoint dec_term_rec {B V: Type} (ctx: list B)
  (t: term B V): term (list B * B) (list B * V) :=
  match t with
  | tvar v => tvar (ctx, v)
  | lam b body => lam (ctx, b) (dec_term_rec (ctx ++ [b]) body)
  | tap t1 t2 => tap (dec_term_rec ctx t1) (dec_term_rec ctx t2)
  end.

Definition dec_term {B V: Type}:
  term B V ->
  term (list B * B) (list B * V) :=
  dec_term_rec nil.

Lemma dec_term_shift1 {B V: Type}:
  forall (ctx1 ctx2: list B) (t: term B V),
    dec_term_rec (ctx1 ++ ctx2) t =
      shift2 (ctx1, dec_term_rec ctx2 t).
Proof.
  intros.
  generalize dependent ctx1.
  generalize dependent ctx2.
  induction t; intros.
  - cbn.
    reflexivity.
  - cbn.
    fequal.
    rewrite <- List.app_assoc.
    rewrite IHt.
    compose near (dec_term_rec (ctx2 ++ [b]) t).
    rewrite (fun2_map_map).
    rewrite IHt.
    unfold shift2.
    unfold compose at 6.
    compose near (strength2 (ctx2, dec_term_rec [b] t)).
    rewrite fun2_map_map.
    unfold compose at 3.
    cbn.
    compose near ((map2 (pair ctx2) (pair ctx2) (dec_term_rec [b] t))) on left.
    rewrite fun2_map_map.
    compose near ((map2 (pair ctx2) (pair ctx2) (dec_term_rec [b] t))) on left.
    rewrite fun2_map_map.
    fequal.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Lemma dec_term_shift {B V: Type}:
  forall (ctx: list B) (t: term B V),
    dec_term_rec ctx t =
      shift2 (ctx, dec_term t).
Proof.
  intros.
  rewrite <- (List.app_nil_r ctx) at 1.
  rewrite dec_term_shift1.
  reflexivity.
Qed.

#[export] Instance DecoratePoly_term: DecoratePoly term := @dec_term.

Section dec_term_rewriting.

  Context (B V: Type) (ctx: list B).

  Lemma dec_term_rec_rw1: forall (v: V),
      dec_term_rec ctx (tvar v) = tvar (ctx, v).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term_rec_rw2: forall (b: B) (body: term B V),
      dec_term_rec ctx (lam b body) =
        lam (ctx, b) (dec_term_rec (ctx ++ [b]) body).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term_rec_rw3: forall (t1 t2: term B V),
      dec_term_rec ctx (tap t1 t2) = tap (dec_term_rec ctx t1) (dec_term_rec ctx t2).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term_rw1: forall (v: V),
      decp (tvar (B := B) v) = tvar ([], v).
  Proof.
    cbn.
    reflexivity.
  Qed.

  Lemma dec_term_rw2: forall (b: B) (body: term B V),
      decp (lam b body) = lam ([], b) (shift2 ([b], decp body)).
  Proof.
    intros. cbn.
    rewrite dec_term_shift.
    reflexivity.
  Qed.

  Lemma dec_term_rw2': forall (b: B) (body: term B V),
      decp (lam b body) = lam ([], b) (dec_term_rec [b] body).
  Proof.
    reflexivity.
  Qed.

  Lemma dec_term_rw3: forall (t1 t2: term B V),
      decp (tap t1 t2) = tap (decp t1) (decp t2).
  Proof.
    reflexivity.
  Qed.

End dec_term_rewriting.

(* Naturality, rec case *)
Lemma map_dec_rec:
  forall (B1 V1 B2 V2: Type)
    (ρ: list B1 * B1 -> B2) (σ: list B1 * V1 -> V2) (ctx: list B1),
    map2 ρ σ ∘ dec_term_rec ctx =
      map2 (ρ ⦿ ctx) (σ ⦿ ctx) ∘ dec_term.
Proof.
  intros. ext t. unfold compose.
  generalize dependent ctx.
  generalize dependent σ.
  generalize dependent ρ.
  induction t; intros ρ σ ctx.
  - cbn. unfold preincr, compose, incr.
    change (@nil B1) with (Ƶ: list B1).
    rewrite monoid_id_l.
    reflexivity.
  - cbn.
    rewrite IHt.
    rewrite IHt.
    fequal.
    + unfold preincr, incr, compose, monoid_op, Monoid_op_list.
      rewrite List.app_nil_r.
      reflexivity.
    + rewrite preincr_preincr.
      rewrite preincr_preincr.
      reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Lemma dec_rec_spec:
  forall (B V: Type) (ctx: list B),
    dec_term_rec ctx =
      map2 (incr ctx) (incr ctx) ∘ dec_term (V := V).
Proof.
  intros.
  change_left (id ∘ dec_term_rec ctx (V := V)).
  rewrite <- fun2_map_id.
  rewrite map_dec_rec.
  reflexivity.
Qed.

(* Counit law *)
Lemma dec_rec_extract_term: forall (B V: Type) (ctx: list B),
    map2 (extract_Z2) (extract_Z2) ∘ dec_term_rec ctx = @id (term B V).
Proof.
  intros. ext t. unfold compose.
  generalize dependent ctx. induction t; intro ctx.
  - reflexivity.
  - cbn. now rewrite IHt.
  - cbn. now rewrite IHt1, IHt2.
Qed.

Lemma dec_extract_term: forall (B V: Type),
    map2 (extract_Z2) (extract_Z2) ∘ dec_term = @id (term B V).
Proof.
  intros. unfold dec_term. apply dec_rec_extract_term.
Qed.

(* cojoin law *)
Lemma dec_rec_dec_rec_term: forall (B V: Type) (ctx: list B),
    dec_term_rec (decorate_prefix_list ctx) ∘ dec_term_rec ctx =
      map2 (cojoin_Z2) (cojoin_Z2) ∘ dec_term_rec ctx (B := B) (V := V).
Proof.
  intros. ext t. unfold compose.
  generalize dependent ctx.
  induction t; intro ctx.
  - reflexivity.
  - cbn.
    rewrite <- IHt.
    rewrite decorate_prefix_list_rw_app.
    cbn. change (@nil B) with (Ƶ: list B).
    rewrite monoid_id_l.
    reflexivity.
  - cbn. now rewrite IHt1, IHt2.
Qed.

Lemma dec_dec_term: forall (B V: Type),
    dec_term ∘ dec_term (B := B) (V := V) =
      map2 (cojoin_Z2) (cojoin_Z2) ∘ dec_term.
Proof.
  intros. unfold dec_term.
  change (@nil (list B * B)) with (decorate_prefix_list (@nil B)).
  apply dec_rec_dec_rec_term.
Qed.

Section naturality.

  Context {B1 V1 B2 V2: Type}
    (ρ: B1 -> B2) (σ: V1 -> V2).

  Lemma dec_rec_map: forall (ctx: list B1),
      dec_term_rec (map ρ ctx) ∘ map2 ρ σ =
        map2 (map_pair (map (F := list) ρ) ρ)
          (map_pair (map (F := list) ρ) σ) ∘ dec_term_rec ctx.
  Proof.
    intros. ext t. unfold compose.
    generalize dependent ρ; clear ρ.
    generalize dependent σ; clear σ.
    generalize dependent ctx.
    induction t as [v | b body IHbody | t1 IHt1 t2 IHt2];
      intros.
    - reflexivity.
    - cbn.
      fequal.
      replace (map ρ ctx ++ [ρ b])
        with (map ρ (ctx ++ [b])) by now rewrite map_list_app.
      rewrite IHbody.
      reflexivity.
    - cbn.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

  Lemma dec_map:
    dec_term ∘ map2 ρ σ =
      map2 (map_pair (map (F := list) ρ) ρ)
        (map_pair (map (F := list) ρ) σ) ∘ dec_term.
  Proof.
    unfold dec_term.
    change (@nil B2) with (map ρ nil).
    rewrite dec_rec_map.
    reflexivity.
  Qed.

End naturality.

#[export] Instance: DecoratedFunctorPoly term.
Proof.
  constructor.
  - typeclasses eauto.
  - unfold PolyDecorateNatural.
    intros.
    setoid_rewrite dec_map.
    fequal.
    fequal.
    now ext [ctx a].
  - intros.
    rewrite dec_dec_term.
    reflexivity.
  - intros.
    rewrite dec_extract_term.
    reflexivity.
Qed.


(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Applicative distribution
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

Fixpoint dist_term
  {G: Type -> Type} `{Map G} `{Pure G} `{Mult G}
   {B V: Type}
  (t: term (G B) (G V)): G (term B V) :=
  match t with
  | tvar vr => map (@tvar B V) vr
  | lam bin body => pure (@lam B V)
                     <⋆> bin
                     <⋆> dist_term body
  | tap t1 t2 => pure (@tap B V)
                  <⋆> dist_term t1
                  <⋆> dist_term t2
  end.

#[export] Instance term_dist2: ApplicativeDist2 term := @dist_term.

Lemma dist_term_morph:
  forall (G1 G2 : Type -> Type)
    `{Map G1} `{Mult G1} `{Pure G1}
    `{Map G2} `{Mult G2} `{Pure G2}
    (ϕ: forall (A: Type), G1 A -> G2 A),
    ApplicativeMorphism G1 G2 ϕ ->
    forall (B V: Type),
      dist2 (G := G2) ∘ map2 (ϕ B) (ϕ V) =

        ϕ (term B V) ∘ dist2 (G := G1) (B := B) (A := V).
Proof.
  intros. ext t. unfold compose.
  induction t.
  - cbn.
    rewrite appmor_natural.
    reflexivity.
  - cbn.
    rewrite IHt.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    rewrite ap_morphism_1.
    rewrite ap_morphism_1.
    rewrite appmor_pure.
    reflexivity.
Qed.

Lemma dist_term_linear:
  forall (G1 G2 : Type -> Type)
    `{Map G1} `{Mult G1} `{Pure G1} `{! Applicative G1}
    `{Map G2} `{Mult G2} `{Pure G2} `{! Applicative G2},
  forall (B V: Type),
    dist2 (G := G1 ∘ G2) =
    map (F := G1) (dist2 (G := G2)) ∘
      dist2 (T := term) (G := G1) (B := G2 B) (A := G2 V).
Proof.
  intros. ext t. unfold compose at 4.
  induction t.
  - cbn. compose near v on right.
    rewrite fun_map_map.
    reflexivity.
  - cbn.
    rewrite IHt.
    unfold_ops @Pure_compose.
    rewrite (ap_compose2 G2 G1).
    rewrite (ap_compose2 G2 G1).
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite app_pure_natural.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    unfold_ops @Pure_compose.
    rewrite (ap_compose2 G2 G1).
    rewrite (ap_compose2 G2 G1).
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite app_pure_natural.
    rewrite app_pure_natural.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    reflexivity.
Qed.

Section naturality.

  Context {B1 V1 B2 V2: Type}
    (ρ: B1 -> B2) (σ: V1 -> V2).

  Lemma dist_map `{Applicative G}:
    map (map2 ρ σ) ∘ dist_term (G := G) =
      dist_term ∘ map2 (map ρ) (map σ).
  Proof.
    intros. ext t. unfold compose.
    induction t as [v | b body IHbody | t1 IHt1 t2 IHt2];
      change (@nil B2) with (map ρ nil).
    - cbn.
      compose near v on left.
      rewrite fun_map_map.
      compose near v on right.
      rewrite fun_map_map.
      reflexivity.
    - cbn.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite <- ap_map.
      rewrite app_pure_natural.
      rewrite <- IHbody.
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      reflexivity.
    - cbn.
      rewrite map_ap.
      rewrite map_ap.
      rewrite app_pure_natural.
      rewrite <- IHt1.
      rewrite <- ap_map.
      rewrite app_pure_natural.
      rewrite <- IHt2.
      rewrite <- ap_map.
      rewrite map_ap.
      rewrite app_pure_natural.
      reflexivity.
  Qed.


End naturality.

#[export] Instance Natural_dist2_term:
  forall (G : Type -> Type) (Map_G : Map G) (Pure_G : Pure G) (Mult_G : Mult G),
    Applicative G -> Natural2 (@dist2 term term_dist2 G Map_G Pure_G Mult_G).
Proof.
  intros.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros. apply dist_map.
    auto.
Qed.

#[export] Instance TraversableFunctor2_term: TraversableFunctor2 term.
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply dist_term_morph.
  - intros. ext t. unfold id. induction t.
    reflexivity.
    cbn. rewrite IHt. reflexivity.
    cbn. rewrite IHt1, IHt2. reflexivity.
  - intros. apply dist_term_linear; auto.
Qed.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Join
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

Fixpoint join_term {B V: Type} (t: term B (term B V)): term B V :=
  match t with
  | tvar v => v
  | lam b body => lam b (join_term body)
  | tap t1 t2 => tap (join_term t1) (join_term t2)
  end.

Lemma join_ret_term {B V: Type}:
  join_term ∘ ret (A := term B V) = @id (term B V).
Proof.
  reflexivity.
Qed.

Lemma join_map_ret_term {B V: Type}:
  join_term ∘ map2 (@id B) (ret (A := V)) = @id (term B V).
Proof.
  ext t. unfold compose. induction t.
  - reflexivity.
  - cbn. rewrite IHt. reflexivity.
  - cbn. rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma join_join_term {B V: Type}:
  join_term ∘ join_term (B := B) (V := term B V) =
    join_term ∘ map2 id (join_term).
Proof.
  intros. ext t.
  unfold compose.
  induction t as [v | b body IHbody | t1 IHt1 t2 IHt2].
  - reflexivity.
  - cbn.
    rewrite IHbody.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

#[export] Instance Join_lambda_term: forall B, Join (term B) :=
  @join_term.

Section join_term_rewriting.

  Context (B V: Type).

  Lemma join_term_rw1: forall (v: term B V),
      join (tvar (B := B) v) = v.
  Proof.
    reflexivity.
  Qed.

  Lemma join_term_rw2: forall (b: B) (body: term B (term B V)),
      join (lam b body) = lam b (join body).
  Proof.
    reflexivity.
  Qed.

  Lemma join_term_rw3: forall (t1 t2: term B (term B V)),
      join (tap t1 t2) = tap (join t1) (join t2).
  Proof.
    reflexivity.
  Qed.

End join_term_rewriting.

Section naturality.

  Context {B1 V1 B2 V2: Type}
    (ρ: B1 -> B2) (σ: V1 -> V2).

  Lemma join_map:
    join (T := term B2) ∘ map2 ρ (map2 ρ σ) =
      map2 ρ σ ∘ (join (T := term B1) (A := V1)).
  Proof.
    ext t. unfold compose.
    induction t as [v | b body IHbody | t1 IHt1 t2 IHt2].
    - reflexivity.
    - cbn.
      rewrite IHbody.
      reflexivity.
    - cbn.
      rewrite IHt1.
      rewrite IHt2.
      reflexivity.
  Qed.

End naturality.

#[export] Instance Monad_term: forall B, Monad (term B).
Proof.
  constructor.
  - typeclasses eauto.
  - constructor; try typeclasses eauto.
    intros. reflexivity.
  - constructor; try typeclasses eauto.
    intros. unfold map, Map2_1.
    rewrite <- join_map.
    reflexivity.
  - intros. reflexivity.
  - intros. unfold map, Map2_1.
    apply join_map_ret_term.
  - intros. unfold map, Map2_1.
    apply join_join_term.
Qed.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Distribution and Decoration
+++++++++++++++++++++++++++++++++++++++++++++++
|*)
Lemma dist_dec_rec_commute:
  forall (B V: Type)
    `{ApplicativeCommutativeIdempotent G}
    (ctx: list (G B))
    (t: term (G B) (G V)),
    dist2 (T := term) (G := G) (map2 dist_Z dist2_Z2 (dec_term_rec ctx t)) =
      pure (dec_term_rec (B := B) (V := V)) <⋆> (dist list G ctx)
        <⋆> (dist2 (T := term) (G := G) t).
Proof.
  intros.
  generalize dependent ctx.
  induction t; intro ctx.
  - cbn.
    (* LHS *)
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    (* RHS *)
    rewrite map_to_ap.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    reflexivity.
  - cbn.
    (* LHS *)
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite IHt.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite dist_list_app.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite dist_list_one.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite (ap_flip_x3 (lhs := b) (rhs := dist list G ctx)).
    rewrite app_pure_natural.
    rewrite ap_contract.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite ap_contract.
    rewrite app_pure_natural.
    (* RHS *)
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    (* RHS *)
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite ap3.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite <- ap4; repeat rewrite ap2.
    rewrite (ap_flip_x3 (G := G)
               (lhs := dist2 (T := term) (G := G) t1)
               (rhs := dist list G ctx)).
    rewrite app_pure_natural.
    rewrite ap_contract.
    rewrite app_pure_natural.
    rewrite ap3.
    rewrite <- ap4; repeat rewrite ap2.
    reflexivity.
Qed.

Lemma dist_dec_commute:
  forall (B V: Type)
    `{ApplicativeCommutativeIdempotent G}
    (t: term (G B) (G V)),
    dist2 (T := term) (G := G) (map2 dist_Z dist2_Z2 (dec_term t)) =
      pure (dec_term (B := B) (V := V)) <⋆> (dist2 (T := term) (G := G) t).
Proof.
  intros.
  unfold dec_term.
  rewrite dist_dec_rec_commute; auto.
  rewrite dist_list_nil.
  rewrite ap2.
  reflexivity.
Qed.

Lemma dist_dec_commute2:
  forall (B V: Type)
    `{ApplicativeCommutativeIdempotent G},
    dist2 (T := term) (G := G) ∘ map2 (dist_Z (G := G)) (dist2_Z2 (G := G)) ∘ dec_term =
      map (dec_term (B := B) (V := V)) ∘
        (dist2 (T := term) (G := G) (B := B) (A := V)).
Proof.
  intros.
  ext t.
  unfold compose.
  rewrite dist_dec_commute; auto.
  rewrite <- map_to_ap.
  reflexivity.
Qed.

Lemma dist_dec_rec_commute_map:
  forall (B1 V1 B2 V2: Type)
    `{Applicative G}
    (ctx: list (G B1))
    (t: term (G B1) (G V1))
    (ρ: list B1 * B1 -> G B2)
    (σ: list B1 * V1 -> G V2),
    True.
Proof.
  intros.
  (*
  Check
    (map_term dist_pair dist_pair
       (dec_term_rec ctx
          (map_term ρ σ t)).
    dist2 (map_term dist_pair dist_pair (dec_term_rec ctx t)) =
      pure (dec_term_rec (B := B1) (V := V1)) <⋆> (dist list G ctx)
        <⋆> (dist2 t).
   *)
Abort.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Join and Decoration
+++++++++++++++++++++++++++++++++++++++++++++++
|*)
Lemma decorate_ret_term: forall (B V: Type) (V: V),
    dec_term (ret (T := term B) V) =
      ret ([], V).
Proof.
  reflexivity.
Qed.

Lemma decorate_rec_join_term: forall (B V: Type) (ctx: list B),
    dec_term_rec ctx ∘ join (T := term B) (A := V) =
      join (T := term (list B * B))
        ∘ map2 id (shift2 ∘ map_snd dec_term)
        ∘ dec_term_rec ctx.
Proof.
  intros. ext t. unfold compose at 1 2 3.
  generalize dependent ctx.
  induction t as [v | b body IHbody | t1 IHt1 t2 IHt2 ]; intro ctx.
  - (* LHS *)
    rewrite join_term_rw1.
    rewrite dec_rec_spec.
    (* RHS *)
    rewrite dec_term_rec_rw1.
    unfold compose at 2.
    rewrite map2_term_rw1.
    rewrite join_term_rw1.
    cbn.
    compose near (dec_term v) on right.
    unfold map2, Map2_term.
    rewrite (map2_map2_term).
    reflexivity.
  - cbn.
    fequal.
    rewrite IHbody.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Lemma decorate_join_term: forall (B V: Type),
    dec_term ∘ join (T := term B) (A := V) =
      join (T := term (list B * B)) ∘ map2 id (shift2 ∘ map_snd dec_term)
        ∘ dec_term.
Proof.
  intros.
  unfold dec_term.
  rewrite decorate_rec_join_term.
  reflexivity.
Qed.

(*|
+++++++++++++++++++++++++++++++++++++++++++++++
Distribute and Join
+++++++++++++++++++++++++++++++++++++++++++++++
|*)

(* (t: term (G B) (term (G B) (G V))) *)
Lemma dist_join_term {B V: Type}
  `{Applicative G}:
    dist2 (T := term) (G := G) ∘ join (T := term (G B)) (A := (G V)) =
      map (F := G) join ∘ dist2 (T := term) (G := G)
        ∘ map2 (F := term) id (dist2 (T := term) (G := G)).
Proof.
  intros. ext t. unfold compose.
  induction t as [v | b body IHbody | t1 IHt1 t2 IHt2].
  - cbn. compose near (dist2 v) on right.
    rewrite fun_map_map.
    change (tvar (B := B) (V := term B V)) with
      (ret (T := term B) (A := term B V)).
    setoid_rewrite join_ret_term. (* not sure why setoid_ required here *)
    rewrite fun_map_id.
    reflexivity.
  - cbn.
    rewrite IHbody.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    reflexivity.
  - cbn.
    rewrite IHt1.
    rewrite <- ap_map.
    rewrite app_pure_natural.
    rewrite IHt2.
    rewrite <- ap_map.
    rewrite map_ap.
    rewrite app_pure_natural.
    rewrite map_ap.
    rewrite map_ap.
    rewrite app_pure_natural.
    reflexivity.
Qed.

#[export] Instance DecoratedMonadPoly_term:
  DecoratedMonadPoly term.
Proof.
  constructor; try typeclasses eauto.
  - reflexivity.
  - intros.
    now rewrite join_map.
  - reflexivity.
  - intros.
    apply decorate_join_term.
Qed.

#[export] Instance DecoratedTraversableMonadPoly_term:
  DecoratedTraversableMonadPoly term.
Proof.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
  - constructor; try typeclasses eauto.
    intros.
    now rewrite dist_dec_commute2.
  - typeclasses eauto.
  - reflexivity.
  - unfold dist2_join.
    intros.
    setoid_rewrite dist_join_term.
    reflexivity.
Qed.


From Tealeaves Require
  Classes.Categorical.DecoratedTraversableMonadPoly
  Classes.Categorical.TraversableFunctor
  Adapters.CategoricalToKleisli.Monad
  Adapters.CategoricalToKleisli.DecoratedFunctor
  Adapters.CategoricalToKleisli.TraversableFunctor
  Adapters.CategoricalToKleisli.DecoratedTraversableFunctor
  Adapters.PolyToMono.Categorical.DecoratedFunctor
  Adapters.PolyToMono.Categorical.TraversableFunctor.

Module CategoricalPDTMUsefulInstances.

  Export
    Classes.Categorical.DecoratedTraversableMonadPoly.

  Export
    Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly
    Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedOperations
    Adapters.CategoricalToKleisli.DecoratedTraversableMonadPoly.DerivedInstances.

  Export
    Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly
    Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedOperations
    Adapters.CategoricalToKleisli.DecoratedTraversableFunctorPoly.DerivedInstances.

  Export
    Adapters.CategoricalToKleisli.DecoratedFunctorPoly
    Adapters.CategoricalToKleisli.DecoratedFunctorPoly.DerivedOperations
    Adapters.CategoricalToKleisli.DecoratedFunctorPoly.DerivedInstances.

  Export
    Adapters.CategoricalToKleisli.DecoratedTraversableMonad
    Adapters.CategoricalToKleisli.Monad.

  Export
    Adapters.PolyToMono.Categorical.DecoratedFunctor
    Adapters.PolyToMono.Categorical.TraversableFunctor.


  Export Adapters.CategoricalToKleisli.Monad.
  Export CategoricalToKleisli.Monad.DerivedOperations.
  Export CategoricalToKleisli.Monad.DerivedInstances.

  Export Adapters.CategoricalToKleisli.DecoratedFunctor.
  Export CategoricalToKleisli.DecoratedFunctor.DerivedOperations.
  Export CategoricalToKleisli.DecoratedFunctor.DerivedInstances.

  Export Adapters.CategoricalToKleisli.TraversableFunctor.
  Export CategoricalToKleisli.TraversableFunctor.DerivedOperations.
  Export CategoricalToKleisli.TraversableFunctor.DerivedInstances.

  Export Adapters.CategoricalToKleisli.DecoratedTraversableFunctor.
  Export CategoricalToKleisli.DecoratedTraversableFunctor.DerivedOperations.
  Export CategoricalToKleisli.DecoratedTraversableFunctor.DerivedInstances.

  Export Adapters.CategoricalToKleisli.DecoratedTraversableMonad.
  Export CategoricalToKleisli.DecoratedTraversableMonad.DerivedOperations.
  Export CategoricalToKleisli.DecoratedTraversableMonad.DerivedInstances.

  Export PolyToMono.Categorical.DecoratedFunctor.ToMono1.
  Export PolyToMono.Categorical.TraversableFunctor.ToMono.

  Context (B: Set) (V: Set).

  Goal Functor (term B).
    typeclasses eauto.
  Qed.

  Goal Categorical.Monad.Monad (term B).
    typeclasses eauto.
  Qed.

  Goal Categorical.DecoratedFunctor.DecoratedFunctor (list B) (term B).
    typeclasses eauto.
  Qed.

  Goal Categorical.TraversableFunctor.TraversableFunctor (term B).
    typeclasses eauto.
  Qed.

  Goal Categorical.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list B) (term B).
    Fail typeclasses eauto.
  Abort.

  Goal Kleisli.Monad.Monad (term B).
    typeclasses eauto.
  Qed.

  Goal Kleisli.DecoratedFunctor.DecoratedFunctor (list B) (term B).
    typeclasses eauto.
  Qed.

  Goal Kleisli.TraversableFunctor.TraversableFunctor (term B).
    typeclasses eauto.
  Qed.

  Goal Kleisli.DecoratedTraversableFunctor.DecoratedTraversableFunctor (list B) (term B).
    Fail typeclasses eauto.
  Abort.


  Goal Kleisli.DecoratedFunctorPoly.DecoratedFunctorPoly term.
    typeclasses eauto.
  Qed.

  Goal Kleisli.DecoratedTraversableMonadPoly.DecoratedTraversableMonadPoly term.
    typeclasses eauto.
  Qed.

  Goal Kleisli.DecoratedTraversableFunctorPoly.DecoratedTraversableFunctorPoly term.
    typeclasses eauto.
  Qed.

End CategoricalPDTMUsefulInstances.
