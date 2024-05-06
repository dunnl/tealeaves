From Tealeaves Require Export
  Examples.SystemF.Syntax.

Import Subset.Notations.
Import Monoid.Notations.
#[local] Generalizable Variables F G A B C ϕ.

#[local] Arguments mbinddt {ix} {W}%type_scope {T} U%function_scope
  {MBind} {F}%function_scope {H H0 H1 A B} _ _.

(** * Miscellaneous lemmas *)
(******************************************************************************)
Lemma filterk_incr : forall (A : Type) (k : K) (l : list (list K2 * (K * A))) (inc : list K2),
    filterk k (map (F := list) (incr inc) l) = map (F := list) (incr inc) (filterk k l).
Proof.
  intros. induction l.
  - easy.
  - destruct a as  [ctx [j a]].
    rewrite map_list_cons.
    change (incr inc (ctx, (j, a))) with (inc ++ ctx, (j, a)).
    compare values k and j.
    + do 2 rewrite filterk_cons_eq.
      autorewrite with tea_list.
      now rewrite IHl.
    + rewrite filterk_cons_neq; auto.
      rewrite filterk_cons_neq; auto.
Qed.

(** * Simplification support *)
(******************************************************************************)

(** Copied *)


(** ** Monoid-related *)

Ltac simplify_to_monoid :=
  unfold_ops @Pure_const @Mult_const; simpl_monoid.

Ltac extract_preincr :=
    match goal with
      |- context[((?f ∘ extract) ⦿ ?w)] =>
        rewrite extract_preincr2
    end.

(** ** tolist/in-related *)
Ltac tolist_to_binddt :=
  rewrite tolist_to_traverse1, traverse_to_binddt.

(*
Search "to_foldMap".
About element_to_foldMap_list1.
Ltac in_to_binddt :=
  rewrite in_to_foldMap, foldMap_to_traverse1, traverse_to_binddt.
*)

(** ** const/applicative/map related *)
Lemma pure_const_rw: forall {A} {a:A} {M} {unit:Monoid_unit M},
    pure (F := const M) (Pure := @Pure_const _ unit) a = Ƶ.
  reflexivity.
Qed.

Lemma ap_const_rw: forall {M} `{Monoid_op M} {A B} (x: const M (A -> B)) (y: const M A),
    ap (const M) x y = (x ● y).
  reflexivity.
Qed.

Lemma map_const_rw: forall A B (f: A -> B) X,
    map (F := const X) f = @id X.
Proof.
  reflexivity.
Qed.

(** /Copied *)

Lemma mextract_preincr2 :
  forall `{ix: Index} {W : Type} {op : Monoid_op W}
    {A: Type} {B : K -> Type} (f: forall k, A -> B k) (w : W),
    (f ◻ const (extract (W := prod W) (A := A))) ◻ const (incr w) =
      (f ◻ const (extract (W := prod W))).
Proof.
  intros.
  ext k. ext [w' a].
  reflexivity.
Qed.

Create HintDb sysf_rw.
Tactic Notation "simpl_F" := autorewrite with sysf_rw.

Section rw_mbinddt.

  Context
    (A B : Type)
    `{Applicative F}
    (f : forall k, list K * A -> F (SystemF k B)).

  Lemma mbinddt_type_rw1 : forall c,
      mbinddt typ f (ty_c c) = pure (ty_c c).
  Proof. reflexivity. Qed.

  Lemma mbinddt_type_rw2 : forall (a : A),
      mbinddt typ f (ty_v a) = f KType (nil, a).
  Proof. reflexivity. Qed.

  Lemma mbinddt_type_rw3 : forall (t1 t2 : typ A),
      mbinddt typ f (ty_ar t1 t2) =
        pure ty_ar <⋆> mbinddt typ f t1 <⋆> mbinddt typ f t2.
  Proof. reflexivity. Qed.

  Lemma mbinddt_type_rw4 : forall (body : typ A),
      mbinddt typ f (ty_univ body) =
        pure ty_univ <⋆> mbinddt typ (f ◻ const (incr [KType])) body.
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw1 : forall (a : A),
      mbinddt term f (tm_var a) = f KTerm (nil, a).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw2 : forall (τ : typ A) (t : term A),
      mbinddt term f (tm_abs τ t) =
        pure tm_abs <⋆> (mbinddt typ f τ) <⋆>
          (mbinddt term (f ◻ const (incr [KTerm])) t).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw3 : forall (t1 t2 : term A),
      mbinddt term f (tm_app t1 t2) =
        pure tm_app <⋆> (mbinddt term f t1) <⋆> (mbinddt term f t2).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw4 : forall (t : term A),
      mbinddt term f (tm_tab t) =
        pure tm_tab <⋆> (mbinddt term (fun k => f k ∘ incr [KType]) t).
  Proof. reflexivity. Qed.

  Lemma mbinddt_term_rw5 : forall (t: term A) (τ : typ A),
      mbinddt term f (tm_tap t τ) =
        pure tm_tap <⋆> (mbinddt term f t) <⋆> (mbinddt typ f τ).
  Proof. reflexivity. Qed.

End rw_mbinddt.

#[export] Hint Rewrite @mbinddt_term_rw1 @mbinddt_term_rw2 @mbinddt_term_rw3 @mbinddt_term_rw4 @mbinddt_term_rw5 : sysf_rw.
#[export] Hint Rewrite @mbinddt_type_rw1 @mbinddt_type_rw2 @mbinddt_type_rw3 @mbinddt_type_rw4 : sysf_rw.

Ltac simplify :=
  match goal with
  | |- context[mbinddt typ ?f ?t] =>
      first [ rewrite mbinddt_type_rw1
            | rewrite mbinddt_type_rw2
            | rewrite mbinddt_type_rw3
            | rewrite mbinddt_type_rw4 ]
  | |- context[mbinddt term ?f ?t] =>
      first [ rewrite mbinddt_term_rw1
            | rewrite mbinddt_term_rw2
            | rewrite mbinddt_term_rw3
            | rewrite mbinddt_term_rw4
            | rewrite mbinddt_term_rw5 ]
  | |- context[(?f ∘ extract) ⦿ ?w] =>
      rewrite extract_preincr2
  | |- context[(?f ∘ extract) (?w, ?a)] =>
      change ((f ∘ extract) (w, a)) with
      ((f ∘ (extract ∘ pair w)) a);
      rewrite extract_pair
  | |- context [id ∘ ?f] =>
      idtac "id ∘ f";
      change (id ∘ f) with f
  | |- context [?f ∘ id] =>
      idtac "f ∘ id";
      change (f ∘ id) with f
  | |- context [pure (F := const ?W) ?x] =>
      idtac "pure_const";
      rewrite pure_const_rw
  | |- context[(ap (const ?W) ?x ?y)] =>
      idtac "ap_const";
      rewrite ap_const_rw
  | |- context[pure (F := fun A => A) ?x] =>
      idtac "pure_I";
      change (pure (F := fun A => A) x) with x
  | |- context[(ap (fun A => A) ?x ?y)] =>
      idtac "ap_I";
      change (ap (fun A => A) x y) with (x y)
  | |- context[Ƶ ● ?m] =>
      idtac "monoid_id_r";
      rewrite (monoid_id_r m)
  | |- context[?m ● Ƶ] =>
      idtac "monoid_id_l";
      rewrite (monoid_id_l m)
  | |- context[map (F := const ?X) ?f] =>
      idtac "map_const";
      rewrite map_const_rw
  | |- context[map (F := const ?X)] =>
      (* this case works binders *)
      idtac "map_const_alt";
      change (map (F := const ?M) ?f ∘ ?g) with g
(*
  | |- context[free_loc (Fr ?x)] =>
      rewrite free_loc_Fr
  | |- context[free_loc (Bd ?b)] =>
      rewrite free_loc_Bd
  | |- context[?x ∈ [?y]] =>
      rewrite in_list_one
  | |- context[Forall_ctx ?P] =>
      unfold Forall_ctx
  | |- context[is_bound_or_free] =>
      simplify_is_bound_or_free
 *)
  (* new stuff *)
  | |- context[(?f ◻ const extract) ◻ const (incr ?w)] =>
      rewrite mextract_preincr2
  end.

(*
(** * Rewriting operations on <<typ>> *)
(******************************************************************************)

(** ** Fundamental operations *)
(******************************************************************************)

(** *** <<mmapdt>> *)
(******************************************************************************)
Section rw_mmapdt_type.

  Context
    (A B : Type)
    `{Applicative F}
    (f : K -> list K * A -> F B).

  Lemma rw_mmapdt_type1:
    forall c, mmapdt typ F f (ty_c c) = pure (ty_c c).
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    simplify.
    reflexivity.
  Qed.

  (* Why is this expressed with <⋆>? *)
  Lemma rw_mmapdt_type2: forall (a: A), mmapdt typ F f (ty_v a) = pure ty_v <⋆> f KType (nil, a).
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    simplify.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

  Lemma rw_mmapdt_type3: forall (t1 t2: typ A),
      mmapdt typ F f (ty_ar t1 t2) =
        pure (ty_ar) <⋆> mmapdt typ F f t1 <⋆> mmapdt typ F f t2.
  Proof.
    intros.
    rewrite mmapdt_to_mbinddt.
    simplify.
    reflexivity.
  Qed.

  Lemma rw_mmapdt_type4: forall (body: typ A),
      mmapdt typ F f (ty_univ body) =
        pure (ty_univ) <⋆> mmapdt typ F (fun k => f k ∘ incr [KType]) body.
  Proof.
    reflexivity.
  Qed.

End rw_mmapdt_type.

(*
#[export] Hint Rewrite @rw_mmapdt_type1 @rw_mmapdt_type2 @rw_mmapdt_type3 @rw_mmapdt_type4: sysf_rw.
*)

(** *** <<mbindd>> *)
(******************************************************************************)
Section rw_mbindd_type.

  Context
    (A B: Type)
    (f: forall k, list K * A -> SystemF k B).

  Lemma rw_mbindd_type1: forall c, mbindd typ f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type2: forall (a: A), mbindd typ f (ty_v a) = f KType (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type3: forall (t1 t2: typ A), mbindd typ f (ty_ar t1 t2) = ty_ar (mbindd typ f t1) (mbindd typ f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_type4: forall (body: typ A), mbindd typ f (ty_univ body) = ty_univ (mbindd typ (fun k => f k ∘ incr [KType]) body).
  Proof. reflexivity. Qed.

End rw_mbindd_type.

#[export] Hint Rewrite @rw_mbindd_type1 @rw_mbindd_type2 @rw_mbindd_type3 @rw_mbindd_type4: sysf_rw.

(** *** <<mbind>> *)
(******************************************************************************)
Section rw_mbind_type.

  Context
    (A B: Type)
    (f: forall k, A -> SystemF k B).

  Lemma rw_mbind_type1: forall c, mbind typ f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type2: forall (a: A), mbind typ f (ty_v a) = f KType a.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type3: forall (t1 t2: typ A), mbind typ f (ty_ar t1 t2) = ty_ar (mbind typ f t1) (mbind typ f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbind_type4: forall (body: typ A), mbind typ f (ty_univ body) = ty_univ (mbind typ f body).
  Proof.
    intros. unfold mbind. rewrite rw_mbindd_type4. repeat fequal. now ext k [w a].
  Qed.

End rw_mbind_type.

#[export] Hint Rewrite @rw_mbind_type1 @rw_mbind_type2 @rw_mbind_type3 @rw_mbind_type4: sysf_rw.

(** *** <<kbindd>> with <<KType>> *)
(******************************************************************************)
Section rw_kbindd_type.

  Context
    (A: Type)
    (f: list K * A -> typ A).

  Lemma rw_kbindd_KType_type1: forall c, kbindd typ KType f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type2: forall a, kbindd typ KType f (ty_v a) = f (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type3: forall (t1 t2: typ A), kbindd typ KType f (ty_ar t1 t2) = ty_ar (kbindd typ KType f t1) (kbindd typ KType f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_type4: forall (body: typ A), kbindd typ KType f (ty_univ body) = ty_univ (kbindd typ KType (f ∘ incr [KType]) body).
  Proof.
    intros. unfold kbindd. simpl_F.
    do 2 fequal. now ext j [w a].
  Qed.

End rw_kbindd_type.

#[export] Hint Rewrite @rw_kbindd_KType_type1 @rw_kbindd_KType_type2 @rw_kbindd_KType_type3 @rw_kbindd_KType_type4: sysf_rw.

(** *** <<kbindd>> with <<KTerm>> *)
(******************************************************************************)
Section rw_kbindd_type.

  Context
    (A: Type)
    (f: list K * A -> term A).

  Lemma rw_kbindd_KTerm_type1: forall c, kbindd typ KTerm f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type2: forall a, kbindd typ KTerm f (ty_v a) = ty_v a.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type3: forall (t1 t2: typ A), kbindd typ KTerm f (ty_ar t1 t2) = ty_ar (kbindd typ KTerm f t1) (kbindd typ KTerm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_type4: forall (body: typ A), kbindd typ KTerm f (ty_univ body) = ty_univ (kbindd typ KTerm (f ∘ incr [KType]) body).
  Proof.
    intros. unfold kbindd. simpl_F.
    do 2 fequal. now ext j [w a].
  Qed.

End rw_kbindd_type.

#[export] Hint Rewrite @rw_kbindd_KTerm_type1 @rw_kbindd_KTerm_type2 @rw_kbindd_KTerm_type3 @rw_kbindd_KTerm_type4: sysf_rw.

(** *** <<kbind>> with <<KType>> *)
(******************************************************************************)
Section rw_kbind_type.

  Context
    (A: Type)
    (f: A -> typ A).

  Lemma rw_kbind_KType_type1: forall c, kbind typ KType f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type2: forall a, kbind typ KType f (ty_v a) = f a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type3: forall (t1 t2: typ A), kbind typ KType f (ty_ar t1 t2) = ty_ar (kbind typ KType f t1) (kbind typ KType f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_type4: forall (body: typ A), kbind typ KType f (ty_univ body) = ty_univ (kbind typ KType f body).
  Proof.
    intros. unfold kbind. now simpl_F.
  Qed.

End rw_kbind_type.

#[export] Hint Rewrite @rw_kbind_KType_type1 @rw_kbind_KType_type2 @rw_kbind_KType_type3 @rw_kbind_KType_type4: sysf_rw.

(** *** <<kbind>> with <<KTerm>> *)
(******************************************************************************)
Section rw_kbind_type.

  Context
    (A: Type)
    (f: A -> term A).

  Lemma rw_kbind_KTerm_type1: forall c, kbind typ KTerm f (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type2: forall a, kbind typ KTerm f (ty_v a) = ty_v a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type3: forall (t1 t2: typ A), kbind typ KTerm f (ty_ar t1 t2) = ty_ar (kbind typ KTerm f t1) (kbind typ KTerm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_type4: forall (body: typ A), kbind typ KTerm f (ty_univ body) = ty_univ (kbind typ KTerm f body).
  Proof.
    intros. unfold kbind. now simpl_F.
  Qed.

End rw_kbind_type.

#[export] Hint Rewrite @rw_kbind_KTerm_type1 @rw_kbind_KTerm_type2 @rw_kbind_KTerm_type3 @rw_kbind_KTerm_type4: sysf_rw.

*)


(** ** List and occurrence operations *)
(******************************************************************************)

(** *** <<tomlistd>> *)
(******************************************************************************)
Section rw_tomlistd_type.

  Context
    (A: Type).

  Lemma rw_tomlistd_type1: forall c,
      tomlistd (A:= A) typ (ty_c c) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_tomlistd_type2: forall (a: A),
      tomlistd typ (ty_v a) = [ (nil, (KType, a)) ].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_tomlistd_type3: forall (t1 t2: typ A),
      tomlistd typ (ty_ar t1 t2) = tomlistd typ t1 ++ tomlistd typ t2.
  Proof.
    reflexivity.
  Qed.

  (* TODO automate and generalize this proof *)
  Lemma rw_tomlistd_type4: forall (body: typ A),
      tomlistd typ (ty_univ body) = map (F:= list) (incr [KType]) (tomlistd typ body).
  Proof.
    intros.
    unfold tomlistd, tomlistd_gen.
    rewrite mmapdt_to_mbinddt.
    simplify.
    simplify.
    simplify.
    simplify.
    compose near body on right.
    rewrite (dtp_mbinddt_morphism
               (list (@K I2)) SystemF (const (list _))).
               (const (list _))
               (ϕ := (fun k => map (A := list K2 * (@K I2 * A))
                             (F:= list) (Map := Map_list) (incr [KType])))).
    fequal. now ext k [w a].
  Qed.

End rw_tomlistd_type.

#[export] Hint Rewrite @rw_tomlistd_type1 @rw_tomlistd_type2 @rw_tomlistd_type3 @rw_tomlistd_type4: sysf_rw.

(** *** <<toklistd>> with <<KType>> *)
(******************************************************************************)
Section rw_toklistd_KType_type.

  Context
    (A: Type).

  Lemma rw_toklistd_KType_type1: forall c,
      toklistd (A:= A) typ KType (ty_c c) = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_toklistd_KType_type2: forall (a: A),
      toklistd typ KType (ty_v a) = [ (nil, a) ].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_toklistd_KType_type3: forall (t1 t2: typ A),
      toklistd typ KType (ty_ar t1 t2) =
        toklistd typ KType t1 ++ toklistd typ KType t2.
  Proof.
    intros.
    unfold toklistd, compose.
    rewrite rw_tomlistd_type3.
    now autorewrite with tea_list.
  Qed.

  Lemma rw_toklistd_KType_type4: forall (body: typ A), toklistd typ KType (ty_univ body) = map (F:= list) (incr [KType]) (toklistd typ KType body).
  Proof. intros. unfold toklistd, compose. rewrite rw_tomlistd_type4. now rewrite filterk_incr. Qed.

End rw_toklistd_KType_type.

#[export] Hint Rewrite @rw_toklistd_KType_type1 @rw_toklistd_KType_type2 @rw_toklistd_KType_type3 @rw_toklistd_KType_type4: sysf_rw.

(** *** <<toklistd>> with <<KTerm>> *)
(******************************************************************************)
Section rw_toklistd_KTerm_type.

  Context
    (A: Type).

  Lemma rw_toklistd_KTerm_type1: forall c, toklistd (A:= A) typ KTerm (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_KTerm_type2: forall (a: A), toklistd typ KTerm (ty_v a) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_KTerm_type3: forall (t1 t2: typ A), toklistd typ KTerm (ty_ar t1 t2) = toklistd typ KTerm t1 ++ toklistd typ KTerm t2.
  Proof. intros. unfold toklistd, compose. rewrite rw_tomlistd_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklistd_KTerm_type4: forall (body: typ A), toklistd typ KTerm (ty_univ body) = map (F:= list) (incr [KType]) (toklistd typ KTerm body).
  Proof. intros. unfold toklistd, compose. rewrite rw_tomlistd_type4. now rewrite filterk_incr. Qed.

End rw_toklistd_KTerm_type.

#[export] Hint Rewrite @rw_toklistd_KTerm_type1 @rw_toklistd_KTerm_type2 @rw_toklistd_KTerm_type3 @rw_toklistd_KTerm_type4: sysf_rw.

(** *** <<tomlist>> *)
(******************************************************************************)
Section rw_tomlist_type.

  Context
    (A: Type).

  Lemma rw_tomlist_type1: forall c, tomlist (A:= A) typ (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_type2: forall (a: A), tomlist typ (ty_v a) = [ (KType, a) ].
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_type3: forall (t1 t2: typ A), tomlist typ (ty_ar t1 t2) = tomlist typ t1 ++ tomlist typ t2.
  Proof. intros. unfold tomlist, compose. rewrite rw_tomlistd_type3. now autorewrite with tea_list. Qed.

  Lemma rw_tomlist_type4: forall (body: typ A), tomlist typ (ty_univ body) = (tomlist typ body).
  Proof. intros. unfold tomlist, compose. rewrite rw_tomlistd_type4.
         compose near (tomlistd typ body) on left. rewrite (fun_map_map (F:= list)).
         fequal. now ext [w a].
  Qed.

End rw_tomlist_type.

#[export] Hint Rewrite @rw_tomlist_type1 @rw_tomlist_type2 @rw_tomlist_type3 @rw_tomlist_type4: sysf_rw.

(** *** <<toklist>> with <<KType>> *)
(******************************************************************************)
Section rw_toklist_KType_type.

  Context
    (A: Type).

  Lemma rw_toklist_KType_type1: forall c, toklist (A:= A) typ KType (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_type2: forall (a: A), toklist typ KType (ty_v a) = [ a ].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_type3: forall (t1 t2: typ A), toklist typ KType (ty_ar t1 t2) = toklist typ KType t1 ++ toklist typ KType t2.
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_KType_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklist_KType_type4: forall (body: typ A), toklist typ KType (ty_univ body) = (toklist typ KType body).
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_KType_type4.
         compose near (toklistd typ KType body) on left. rewrite (fun_map_map (F:= list)).
         fequal. now ext [w a]. Qed.

End rw_toklist_KType_type.

#[export] Hint Rewrite @rw_toklist_KType_type1 @rw_toklist_KType_type2 @rw_toklist_KType_type3 @rw_toklist_KType_type4: sysf_rw.

(** *** <<toklist>> with <<KTerm>> *)
(******************************************************************************)
Section rw_toklist_KTerm_type.

  Context
    (A: Type).

  Lemma rw_toklist_KTerm_type1: forall c, toklist (A:= A) typ KTerm (ty_c c) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_type2: forall (a: A), toklist typ KTerm (ty_v a) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_type3: forall (t1 t2: typ A), toklist typ KTerm (ty_ar t1 t2) = toklist typ KTerm t1 ++ toklist typ KTerm t2.
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_KTerm_type3. now autorewrite with tea_list. Qed.

  Lemma rw_toklist_KTerm_type4: forall (body: typ A), toklist typ KTerm (ty_univ body) = (toklist typ KTerm body).
  Proof. intros. unfold toklist, compose. rewrite rw_toklistd_KTerm_type4.
         compose near (toklistd typ KTerm body) on left. rewrite (fun_map_map (F:= list)).
         fequal. now ext [w a]. Qed.

End rw_toklist_KTerm_type.

#[export] Hint Rewrite @rw_toklist_KTerm_type1 @rw_toklist_KTerm_type2 @rw_toklist_KTerm_type3 @rw_toklist_KTerm_type4: sysf_rw.

Corollary rw_toklist_KTerm_type: forall A (τ: typ A), toklist typ KTerm τ = nil.
Proof.
  intros. induction τ; autorewrite with sysf_rw.
  - trivial.
  - trivial.
  - now rewrite IHτ1, IHτ2.
  - now rewrite IHτ.
Qed.

(** *** Variable occurrence with context *)
(******************************************************************************)
Section rw_tomsetd_type.

  Context
    (A: Type)
    (k: K2).

  Implicit Types
           (w: list K) (a: A).

  Lemma rw_tomsetd_type1: forall c w a, (w, (k, a)) ∈md (ty_c c) <-> False.
  Proof.
    intros. unfold tomsetd, compose. autorewrite with sysf_rw. easy.
  Qed.

  Lemma rw_tomsetd_type2: forall w a a', (w, (k, a)) ∈md (ty_v a') <-> w = nil /\ k = KType /\ a = a'.
  Proof.
    intros. unfold tomsetd, compose.
    autorewrite with sysf_rw.
    rewrite tosubset_list_one.
    split.
    - now inversion 1.
    - firstorder. now subst.
  Qed.

  Lemma rw_tomsetd_type3: forall w a (t1 t2: typ A), (w, (k, a)) ∈md ty_ar t1 t2 <-> ((w, (k, a)) ∈md t1 \/ (w, (k, a)) ∈md t2).
  Proof.
    intros. unfold tomsetd, compose.
    now autorewrite with sysf_rw tea_list tea_set.
  Qed.

  Lemma rw_tomsetd_type4: forall w a (body: typ A), (w, (k, a)) ∈md (ty_univ body) <-> exists w', (w', (k, a)) ∈md body /\ w = (cons KType w').
  Proof.
    intros. unfold tomsetd, compose. autorewrite with sysf_rw.
    rewrite (tosubset_map_iff).
    splits.
    - intros [[w'' [j a']] [rest1 rest2]]. cbn in *. inverts rest2. eauto.
    - intros [w' rest]. exists (w', (k, a)). now inverts rest.
  Qed.

End rw_tomsetd_type.

#[export] Hint Rewrite @rw_tomsetd_type1 @rw_tomsetd_type2 @rw_tomsetd_type3 @rw_tomsetd_type4: sysf_rw.

Corollary rw_tomsetd_type_KTerm: forall w A a (τ: typ A), (w, (KTerm, a)) ∈md τ <-> False.
Proof.
  intros. generalize dependent w.
  induction τ; intro w; autorewrite with sysf_rw; try easy.
  - rewrite IHτ1, IHτ2. tauto.
  - split; try tauto.
    intros [w' [rest1 rest2]]. now rewrite IHτ in rest1.
Qed.

(** *** Variable occurrence without context *)
(******************************************************************************)
Section rw_tomset_type.

  Context
    (A: Type)
    (k: K2).

  Implicit Types (a: A).

  Lemma rw_tomset_type1: forall c a, (k, a) ∈m (ty_c c) <-> False.
  Proof. intros. rewrite ind_iff_in. firstorder eauto. Qed.

  Lemma rw_tomset_type2: forall a a', (k, a) ∈m (ty_v a') <-> k = KType /\ a = a'.
  Proof. intros. rewrite ind_iff_in. setoid_rewrite rw_tomsetd_type2. firstorder eauto.  Qed.

  Lemma rw_tomset_type3: forall a (t1 t2: typ A), (k, a) ∈m ty_ar t1 t2 <-> (k, a) ∈m t1 \/ (k, a) ∈m t2.
  Proof. intros. repeat rewrite ind_iff_in. setoid_rewrite rw_tomsetd_type3. firstorder eauto. Qed.

  Lemma rw_tomset_type4: forall a (body: typ A), (k, a) ∈m (ty_univ body) <-> (k, a) ∈m body.
  Proof. intros. repeat rewrite ind_iff_in. setoid_rewrite rw_tomsetd_type4. firstorder eauto.  Qed.

End rw_tomset_type.

#[export] Hint Rewrite @rw_tomset_type1 @rw_tomset_type2 @rw_tomset_type3 @rw_tomset_type4: sysf_rw.

(** ** <<free>> and <<freeset>> *)
(******************************************************************************)

(** *** <<free>> with <<KType>> *)
(******************************************************************************)
Section rw_free_KType_type.

  Lemma rw_free_KType_type11: forall (x: atom), free typ KType (ty_v (Fr x)) = [x].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type12: forall (n: nat), free typ KType (ty_v (Bd n)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type2: forall (c: base_typ), free typ KType (ty_c c) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KType_type3: forall t1 t2, free typ KType (ty_ar t1 t2) = free typ KType t1 ++ free typ KType t2.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KType_type4: forall t, free typ KType (ty_univ t) = free typ KType t.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_free_KType_type.

#[export] Hint Rewrite rw_free_KType_type11 rw_free_KType_type12 rw_free_KType_type2 rw_free_KType_type3 rw_free_KType_type4: sysf_rw.

(** *** <<freeset>> with <<KType>> *)
(******************************************************************************)
Section rw_freeset_KType_type.

  #[local] Open Scope set_scope.

  Lemma rw_freeset_KType_type11: forall (x: atom), freeset typ KType (ty_v (Fr x)) [=] {{ x }}.
  Proof.
    unfold freeset. intros. autorewrite with sysf_rw tea_rw_atoms. fsetdec.
  Qed.

  Lemma rw_freeset_KType_type12: forall (n: nat), freeset typ KType (ty_v (Bd n)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KType_type2: forall (c: base_typ), freeset typ KType (ty_c c) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KType_type3: forall t1 t2, freeset typ KType (ty_ar t1 t2) [=] freeset typ KType t1 ∪ freeset typ KType t2.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KType_type4: forall t, freeset typ KType (ty_univ t) [=] freeset typ KType t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_freeset_KType_type.

#[export] Hint Rewrite rw_freeset_KType_type11 rw_freeset_KType_type12 rw_freeset_KType_type2 rw_freeset_KType_type3 rw_freeset_KType_type4: sysf_rw.

(** *** <<free>> with <<KTerm>> *)
(******************************************************************************)
Section rw_free_KTerm_type.

  Lemma rw_free_KTerm_type11: forall (x: atom), free typ KTerm (ty_v (Fr x)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type12: forall (n: nat), free typ KTerm (ty_v (Bd n)) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type2: forall (c: base_typ), free typ KTerm (ty_c c) = [].
  Proof.
    reflexivity.
  Qed.

  Lemma rw_free_KTerm_type3: forall t1 t2, free typ KTerm (ty_ar t1 t2) = free typ KTerm t1 ++ free typ KTerm t2.
  Proof. intros. unfold free. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_free_KTerm_type4: forall t, free typ KTerm (ty_univ t) = free typ KTerm t.
  Proof. intros. unfold free. now autorewrite with sysf_rw tea_list. Qed.

End rw_free_KTerm_type.

#[export] Hint Rewrite rw_free_KTerm_type11 rw_free_KTerm_type12 rw_free_KTerm_type2 rw_free_KTerm_type3 rw_free_KTerm_type4: sysf_rw.

Corollary rw_free_KTerm_type: forall (τ: typ LN), free typ KTerm τ = [].
Proof.
  intros. induction τ; autorewrite with sysf_rw.
  - trivial.
  - trivial.
  - now rewrite IHτ1, IHτ2.
  - now rewrite IHτ.
Qed.

(** *** <<freeset>> with <<KTerm>> *)
(******************************************************************************)
Section rw_freeset_KTerm_type.

  #[local] Open Scope set_scope.

  Lemma rw_freeset_KTerm_type11: forall (x: atom), freeset typ KTerm (ty_v (Fr x)) [=] ∅.
  Proof.
    unfold freeset. intros. rewrite rw_free_KTerm_type11. autorewrite with tea_rw_atoms. fsetdec. Qed.

  Lemma rw_freeset_KTerm_type12: forall (n: nat), freeset typ KTerm (ty_v (Bd n)) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type2: forall (c: base_typ), freeset typ KTerm (ty_c c) [=] ∅.
  Proof.
    reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type3: forall t1 t2, freeset typ KTerm (ty_ar t1 t2) [=] freeset typ KTerm t1 ∪ freeset typ KTerm t2.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

  Lemma rw_freeset_KTerm_type4: forall t, freeset typ KTerm (ty_univ t) [=] freeset typ KTerm t.
  Proof.
    intros. unfold freeset. autorewrite with sysf_rw tea_rw_atoms. reflexivity.
  Qed.

End rw_freeset_KTerm_type.

#[export] Hint Rewrite rw_freeset_KTerm_type11 rw_freeset_KTerm_type12 rw_freeset_KTerm_type2 rw_freeset_KTerm_type3 rw_freeset_KTerm_type4: sysf_rw.

Corollary rw_freeset_KTerm_type: forall (τ: typ LN), (freeset typ KTerm τ [=] ∅)%set.
Proof.
  intros. induction τ.
  - autorewrite with sysf_rw. fsetdec.
  - cbn. fsetdec.
  - autorewrite with sysf_rw. fsetdec.
  - autorewrite with sysf_rw. fsetdec.
Qed.

#[export] Hint Rewrite rw_freeset_KTerm_type: sysf_rw.

(** ** Locally nameless operations *)
(******************************************************************************)

(** *** <<open>> *)
(******************************************************************************)
Section rw_open_type.

  Context
    (u: typ LN).

  Lemma rw_open_type1: forall c, open typ KType u (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_open_type2: forall (l: LN), open typ KType u (ty_v l) = open_loc KType u (nil, l).
  Proof. reflexivity. Qed.

  Lemma rw_open_type3: forall (t1 t2: typ LN), open typ KType u (ty_ar t1 t2) = ty_ar (open typ KType u t1) (open typ KType u t2).
  Proof. reflexivity. Qed.

End rw_open_type.

#[export] Hint Rewrite @rw_open_type1 @rw_open_type2 @rw_open_type3: sysf_rw.

(** *** <<subst>> with <<KType>> *)
(******************************************************************************)
Section rw_subst_KType_type.

  Context
    (x: atom)
    (u: typ LN).

  Lemma rw_subst_KType_type1: forall c, subst typ KType x u (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_subst_KType_type2: forall (l: LN), subst typ KType x u (ty_v l) = subst_loc KType x u l.
  Proof. reflexivity. Qed.

  Lemma rw_subst_KType_type3: forall (t1 t2: typ LN), subst typ KType x u (ty_ar t1 t2) = ty_ar (subst typ KType x u t1) (subst typ KType x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_KType_type4: forall (t: typ LN), subst typ KType x u (ty_univ t) = ty_univ (subst typ KType x u t).
  Proof.
    intros.
    unfold subst.
    unfold kbind.
    unfold mbind.
    unfold mbindd.
    simplify.
    simplify.
    simplify.
    simplify.
    reflexivity.
  Qed.

End rw_subst_KType_type.

#[export] Hint Rewrite @rw_subst_KType_type1 @rw_subst_KType_type2 @rw_subst_KType_type3 @rw_subst_KType_type4: sysf_rw.

(** *** <<subst>> with <<KTerm>> *)
(******************************************************************************)
Section rw_subst_KTerm_type.

  Context
    (x: atom)
    (u: term LN).

  Lemma rw_subst_KTerm_type1: forall c, subst typ KTerm x u (ty_c c) = ty_c c.
  Proof. reflexivity. Qed.

  Lemma rw_subst_KTerm_type2: forall (l: LN), subst typ KTerm x u (ty_v l) = ty_v l.
  Proof. reflexivity. Qed.

  Lemma rw_subst_KTerm_type3: forall (t1 t2: typ LN), subst typ KTerm x u (ty_ar t1 t2) = ty_ar (subst typ KTerm x u t1) (subst typ KTerm x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_KTerm_type4: forall (t: typ LN), subst typ KTerm x u (ty_univ t) = ty_univ (subst typ KTerm x u t).
  Proof.
    intros.
    unfold subst.
    unfold kbind.
    unfold mbind.
    unfold mbindd.
    simplify.
    simplify.
    simplify.
    simplify.
    reflexivity.
  Qed.

End rw_subst_KTerm_type.

#[export] Hint Rewrite @rw_subst_KTerm_type1 @rw_subst_KTerm_type2 @rw_subst_KTerm_type3 @rw_subst_KTerm_type4: sysf_rw.

Corollary rw_subst_KTerm_type: forall (τ: typ LN) (x: atom) (u: term LN), subst typ KTerm x u τ = τ.
Proof.
  intros; induction τ; try easy.
  - cbn. now rewrite IHτ1, IHτ2.
  - autorewrite with sysf_rw.
    now rewrite IHτ.
Qed.

#[export] Hint Rewrite @rw_subst_KTerm_type: sysf_rw.

(** *** <<locally_closed>> with <<KType>> *)
(******************************************************************************)
Section rw_lc_KType_type.

  Lemma rw_lc_KType_type1: forall c, locally_closed typ KType (ty_c c).
  Proof.
    intros. unfold locally_closed, locally_closed_gap; introv hyp.
    now rewrite rw_tomsetd_type1 in hyp.
  Qed.

  Lemma rw_lc_KType_type2: forall (l: LN), locally_closed typ KType (ty_v l) <-> exists x, l = Fr x.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_type2. split.
    - introv hyp. destruct l.
      + eauto.
      + enough (n < 0). lia. now apply (hyp [] (Bd n)).
    - intros [x heq]. subst. introv hyp. inversion hyp.
      inverts H0. cbn; trivial.
  Qed.

  Lemma rw_lc_KType_type3: forall (t1 t2: typ LN), locally_closed typ KType (ty_ar t1 t2) <-> (locally_closed typ KType t1 /\ locally_closed typ KType t2).
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_type3. firstorder.
  Qed.

  #[local] Open Scope nat_scope.

  Lemma rw_lc_KType_type4: forall (t: typ LN), locally_closed typ KType (ty_univ t) <-> locally_closed_gap typ KType 1 t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_type4. split.
    - intros hyp w l Hin.
      specialize (hyp (KType:: w) l). cbn in *.
      assert (rw: S (countk (@KType: K) w + 0) = (countk KType w + 1)) by lia.
      rewrite <- rw. apply hyp. eauto.
    - intros hyp w l [w' [H1 H2]]. subst.
      specialize (hyp w' l H1). cbn in *. destruct l.
      + easy.
      + lia.
  Qed.

End rw_lc_KType_type.

#[export] Hint Rewrite @rw_lc_KType_type1 @rw_lc_KType_type2 @rw_lc_KType_type3 @rw_lc_KType_type4: sysf_rw.

(** *** <<locally_closed>> with <<KTerm>> *)
(******************************************************************************)
Section rw_lc_KTerm_type.

  Lemma rw_lc_KTerm_type: forall τ, locally_closed typ KTerm τ <-> True.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_type_KTerm. intuition.
  Qed.

  Lemma lc_KTerm_type: forall τ, locally_closed typ KTerm τ.
  Proof.
    intros. now rewrite rw_lc_KTerm_type.
  Qed.

End rw_lc_KTerm_type.

#[export] Hint Rewrite @rw_lc_KTerm_type: sysf_rw.

(** *** <<scoped>> with <<KTerm>> *)
(******************************************************************************)
Section rw_scoped_KTerm_type.

  Lemma rw_scoped_KTerm_type: forall τ (vars: AtomSet.t), scoped typ KTerm τ vars.
  Proof.
    intros. unfold scoped. autorewrite with sysf_rw. fsetdec.
  Qed.

End rw_scoped_KTerm_type.

(** ** <<ok_type>> *)
(******************************************************************************)
Lemma ok_type_ar: forall Δ τ1 τ2,
    ok_type Δ (ty_ar τ1 τ2) <->
    ok_type Δ τ1 /\ ok_type Δ τ2.
Proof.
  intros. unfold ok_type.
  unfold scoped.
  autorewrite with sysf_rw.
  intuition fsetdec.
Qed.

Lemma ok_type_univ: forall Δ τ,
    ok_type Δ (ty_univ τ) <->
    scoped typ KType τ (AssocList.domset Δ) /\
    locally_closed_gap typ KType 1 τ.
Proof.
  intros. unfold ok_type.
  unfold scoped.
  now autorewrite with sysf_rw.
Qed.

(** * Rewriting operations on <<term>> *)
(******************************************************************************)

(** ** Fundamental operations *)
(******************************************************************************)

(** *** <<mbinddt>> *)
(******************************************************************************)
(** *** <<mmapdt>> *)
(******************************************************************************)
Section rw_mmapdt_term.

  Context
    (A B: Type)
    `{Applicative F}
    (f: K -> list K * A -> F B).

  Lemma rw_mmapdt_term1: forall (a: A), mmapdt term F f (tm_var a) = pure tm_var <⋆> f KTerm (nil, a).
  Proof. intros. unfold mmapdt. autorewrite with sysf_rw. now rewrite <- map_to_ap. Qed.

  Lemma rw_mmapdt_term2: forall (τ: typ A) (t: term A), mmapdt term F f (tm_abs τ t) = pure tm_abs <⋆> (mmapdt typ F f τ) <⋆> (mmapdt term F (fun k => f k ∘ incr [KTerm]) t).
  Proof. reflexivity. Qed.

  Lemma rw_mmapdt_term3: forall (t1 t2: term A), mmapdt term F f (tm_app t1 t2) = pure tm_app <⋆> (mmapdt term F f t1) <⋆> (mmapdt term F f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mmapdt_term4: forall (t: term A), mmapdt term F f (tm_tab t) = pure tm_tab <⋆> (mmapdt term F (fun k => f k ∘ incr [KType]) t).
  Proof. reflexivity. Qed.

  Lemma rw_mmapdt_term5: forall (t: term A) (τ: typ A), mmapdt term F f (tm_tap t τ) = pure tm_tap <⋆> (mmapdt term F f t) <⋆> (mmapdt typ F f τ).
  Proof. reflexivity. Qed.

End rw_mmapdt_term.

#[export] Hint Rewrite @rw_mmapdt_term1 @rw_mmapdt_term2 @rw_mmapdt_term3 @rw_mmapdt_term4 @rw_mmapdt_term5: sysf_rw.

(** *** <<mbindd>> *)
(******************************************************************************)
Section rw_mbindd_term.

  Context
    (A B: Type)
    (f: forall k, list K * A -> SystemF k B).

  Lemma rw_mbindd_term1: forall (a: A), mbindd term f (tm_var a) = f KTerm (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_term2: forall (τ: typ A) (t: term A), mbindd term f (tm_abs τ t) = tm_abs (mbindd typ f τ) (mbindd term (fun k => f k ∘ incr [KTerm]) t).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_term3: forall (t1 t2: term A), mbindd term f (tm_app t1 t2) = tm_app (mbindd term f t1) (mbindd term f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_term4: forall (t: term A), mbindd term f (tm_tab t) = tm_tab (mbindd term (fun k => f k ∘ incr [KType]) t).
  Proof. reflexivity. Qed.

  Lemma rw_mbindd_term5: forall (t: term A) (τ: typ A), mbindd term f (tm_tap t τ) = tm_tap (mbindd term f t) (mbindd typ f τ).
  Proof. reflexivity. Qed.

End rw_mbindd_term.

#[export] Hint Rewrite @rw_mbindd_term1 @rw_mbindd_term2 @rw_mbindd_term3 @rw_mbindd_term4 @rw_mbindd_term5: sysf_rw.

(** *** <<mbind>> *)
(******************************************************************************)
Section rw_mbind_term.

  Context
    (A B: Type)
    (f: forall k, A -> SystemF k B).

  Lemma rw_mbind_term1: forall (a: A), mbind term f (tm_var a) = f KTerm a.
  Proof. reflexivity. Qed.

  Lemma rw_mbind_term2: forall (τ: typ A) (t: term A), mbind term f (tm_abs τ t) = tm_abs (mbind typ f τ) (mbind term f t).
  Proof. intros. unfold mbind. autorewrite with sysf_rw. repeat fequal. now ext k [w a]. Qed.

  Lemma rw_mbind_term3: forall (t1 t2: term A), mbind term f (tm_app t1 t2) = tm_app (mbind term f t1) (mbind term f t2).
  Proof. reflexivity. Qed.

  Lemma rw_mbind_term4: forall (t: term A), mbind term f (tm_tab t) = tm_tab (mbind term f t).
  Proof. intros. unfold mbind. autorewrite with sysf_rw. repeat fequal. now ext k [w a]. Qed.

  Lemma rw_mbind_term5: forall (t: term A) (τ: typ A), mbind term f (tm_tap t τ) = tm_tap (mbind term f t) (mbind typ f τ).
  Proof. reflexivity. Qed.

End rw_mbind_term.

#[export] Hint Rewrite @rw_mbind_term1 @rw_mbind_term2 @rw_mbind_term3 @rw_mbind_term4 @rw_mbind_term5: sysf_rw.

(** *** <<kbindd>> with <<KType>> *)
(******************************************************************************)
Section rw_kbindd_KType_term.

  Context
    (A: Type)
    (f: list K * A -> typ A).

  Lemma rw_kbindd_KType_term1: forall (a: A), kbindd term KType f (tm_var a) = tm_var a.
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_term2: forall (τ: typ A) (t: term A), kbindd term KType f (tm_abs τ t) = tm_abs (kbindd typ KType f τ) (kbindd term KType (f ∘ incr [KTerm]) t).
  Proof. intros. unfold kbindd. autorewrite with sysf_rw. do 2 fequal. now ext k [w a]. Qed.

  Lemma rw_kbindd_KType_term3: forall (t1 t2: term A), kbindd term KType f (tm_app t1 t2) = tm_app (kbindd term KType f t1) (kbindd term KType f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KType_term4: forall (t: term A), kbindd term KType f (tm_tab t) = tm_tab (kbindd term KType (f ∘ incr [KType]) t).
  Proof. intros. unfold kbindd. autorewrite with sysf_rw. do 2 fequal. now ext k [w a]. Qed.

  Lemma rw_kbindd_KType_term5: forall (t: term A) (τ: typ A), kbindd term KType f (tm_tap t τ) = tm_tap (kbindd term KType f t) (kbindd typ KType f τ).
  Proof. reflexivity. Qed.

End rw_kbindd_KType_term.

#[export] Hint Rewrite @rw_kbindd_KType_term1 @rw_kbindd_KType_term2 @rw_kbindd_KType_term3 @rw_kbindd_KType_term4 @rw_kbindd_KType_term5: sysf_rw.

(** *** <<kbindd>> with <<KTerm>> *)
(******************************************************************************)
Section rw_kbindd_KTerm_term.

  Context
    (A: Type)
    (f: list K * A -> term A).

  Lemma rw_kbindd_KTerm_term1: forall (a: A), kbindd term KTerm f (tm_var a) = f (nil, a).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_term2: forall (τ: typ A) (t: term A), kbindd term KTerm f (tm_abs τ t) = tm_abs (kbindd typ KTerm f τ) (kbindd term KTerm (f ∘ incr [KTerm]) t).
  Proof. intros. unfold kbindd. autorewrite with sysf_rw. do 2 fequal. now ext k [w a]. Qed.

  Lemma rw_kbindd_KTerm_term3: forall (t1 t2: term A), kbindd term KTerm f (tm_app t1 t2) = tm_app (kbindd term KTerm f t1) (kbindd term KTerm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbindd_KTerm_term4: forall (t: term A), kbindd term KTerm f (tm_tab t) = tm_tab (kbindd term KTerm (f ∘ incr [KType]) t).
  Proof. intros. unfold kbindd. autorewrite with sysf_rw. do 2 fequal. now ext k [w a]. Qed.

  Lemma rw_kbindd_KTerm_term5: forall (t: term A) (τ: typ A), kbindd term KTerm f (tm_tap t τ) = tm_tap (kbindd term KTerm f t) (kbindd typ KTerm f τ).
  Proof. reflexivity. Qed.

End rw_kbindd_KTerm_term.

#[export] Hint Rewrite @rw_kbindd_KTerm_term1 @rw_kbindd_KTerm_term2 @rw_kbindd_KTerm_term3 @rw_kbindd_KTerm_term4 @rw_kbindd_KTerm_term5: sysf_rw.

(** *** <<kbind>> with <<KType>> *)
(******************************************************************************)
Section rw_kbind_KType_term.

  Context
    (A: Type)
    (f: A -> typ A).

  Lemma rw_kbind_KType_term1: forall (a: A), kbind term KType f (tm_var a) = tm_var a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_term2: forall (τ: typ A) (t: term A), kbind term KType f (tm_abs τ t) = tm_abs (kbind typ KType f τ) (kbind term KType f t).
  Proof. intros. unfold kbind. now autorewrite with sysf_rw. Qed.

  Lemma rw_kbind_KType_term3: forall (t1 t2: term A), kbind term KType f (tm_app t1 t2) = tm_app (kbind term KType f t1) (kbind term KType f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KType_term4: forall (t: term A), kbind term KType f (tm_tab t) = tm_tab (kbind term KType f t).
  Proof. intros. unfold kbind. now autorewrite with sysf_rw. Qed.

  Lemma rw_kbind_KType_term5: forall (t: term A) (τ: typ A), kbind term KType f (tm_tap t τ) = tm_tap (kbind term KType f t) (kbind typ KType f τ).
  Proof. reflexivity. Qed.

End rw_kbind_KType_term.

#[export] Hint Rewrite @rw_kbind_KType_term1 @rw_kbind_KType_term2 @rw_kbind_KType_term3 @rw_kbind_KType_term4 @rw_kbind_KType_term5: sysf_rw.

(** *** <<kbind>> with <<KTerm>> *)
(******************************************************************************)
Section rw_kbind_KTerm_term.

  Context
    (A: Type)
    (f: A -> term A).

  Lemma rw_kbind_KTerm_term1: forall (a: A), kbind term KTerm f (tm_var a) = f a.
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_term2: forall (τ: typ A) (t: term A), kbind term KTerm f (tm_abs τ t) = tm_abs (kbind typ KTerm f τ) (kbind term KTerm f t).
  Proof. intros. unfold kbind. now autorewrite with sysf_rw. Qed.

  Lemma rw_kbind_KTerm_term3: forall (t1 t2: term A), kbind term KTerm f (tm_app t1 t2) = tm_app (kbind term KTerm f t1) (kbind term KTerm f t2).
  Proof. reflexivity. Qed.

  Lemma rw_kbind_KTerm_term4: forall (t: term A), kbind term KTerm f (tm_tab t) = tm_tab (kbind term KTerm f t).
  Proof. intros. unfold kbind. now autorewrite with sysf_rw. Qed.

  Lemma rw_kbind_KTerm_term5: forall (t: term A) (τ: typ A), kbind term KTerm f (tm_tap t τ) = tm_tap (kbind term KTerm f t) (kbind typ KTerm f τ).
  Proof. reflexivity. Qed.

End rw_kbind_KTerm_term.

#[export] Hint Rewrite @rw_kbind_KTerm_term1 @rw_kbind_KTerm_term2 @rw_kbind_KTerm_term3 @rw_kbind_KTerm_term4 @rw_kbind_KTerm_term5: sysf_rw.

(** ** List and occurrence operations *)
(******************************************************************************)

(** *** <<tomlistd>> *)
(******************************************************************************)
Section rw_tomlistd_type.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_tomlistd_term1: forall (a: A), tomlistd term (tm_var a) = [ (nil, (KTerm, a)) ].
  Proof. reflexivity. Qed.

  Lemma rw_tomlistd_term2: forall τ t, tomlistd term (tm_abs τ t) = tomlistd typ τ ++ map (F:= list) (incr [KTerm]) (tomlistd term t).
  Proof.
    intros. unfold tomlistd, tomlistd_gen. rewrite rw_mmapdt_term2. fequal.
    compose near t on right. unfold mmapdt.
    rewrite (dtp_mbinddt_morphism
               (list (@K I2)) term SystemF (const (list (list K2 * (K * A))))
               (const (list _)) (ϕ:= (fun _ => map (F:= list) (incr [KTerm])))
               (fun (k: @K I2) => map (F:= const (list (list K2 * (K * A))))
                                  (mret SystemF k) ∘ (fun '(w, a) => [(w, (k, a))]))).
    fequal. now ext k [w a].
  Qed.

  Lemma rw_tomlistd_term3: forall t1 t2, tomlistd term (tm_app t1 t2) = tomlistd term t1 ++ tomlistd term t2.
  Proof. reflexivity. Qed.

  Lemma rw_tomlistd_term4: forall t, tomlistd term (tm_tab t) = map (F:= list) (incr [KType]) (tomlistd term t).
  Proof.
    intros. unfold tomlistd, tomlistd_gen.
    rewrite rw_mmapdt_term4. cbn.
    compose near t on right. unfold mmapdt.
    rewrite (dtp_mbinddt_morphism
               (list (@K I2)) term SystemF (const (list _)) (const (list _)) (ϕ:= (fun _ => map (F:= list) (incr [KType])))
               (fun (k: @K I2) => map (F:= const (list (list K2 * (K2 * A)))) (mret SystemF k) ∘ (fun '(w, a) => [(w, (k, a))]))).
    fequal. now ext k [w a].
  Qed.

  Lemma rw_tomlistd_term5: forall t τ, tomlistd term (tm_tap t τ) = tomlistd term t ++ tomlistd typ τ.
  Proof. reflexivity. Qed.

End rw_tomlistd_type.

#[export] Hint Rewrite @rw_tomlistd_term1 @rw_tomlistd_term2 @rw_tomlistd_term3 @rw_tomlistd_term4 @rw_tomlistd_term5: sysf_rw.

(** *** <<toklistd>> with <<KType>> *)
(******************************************************************************)
Section rw_toklistd_KType_type.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_toklistd_KType_term1: forall (a: A), toklistd term KType (tm_var a) = nil.
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_KType_term2: forall τ t, toklistd term KType (tm_abs τ t) = toklistd typ KType τ ++ map (F:= list) (incr [KTerm]) (toklistd term KType t).
  Proof. intros. unfold toklistd, compose. rewrite rw_tomlistd_term2. rewrite filterk_app. now rewrite filterk_incr. Qed.

  Lemma rw_toklistd_KType_term3: forall t1 t2, toklistd term KType (tm_app t1 t2) = toklistd term KType t1 ++ toklistd term KType t2.
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_app. Qed.

  Lemma rw_toklistd_KType_term4: forall t, toklistd term KType (tm_tab t) = map (F:= list) (incr [KType]) (toklistd term KType t).
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_incr. Qed.

  Lemma rw_toklistd_KType_term5: forall t τ, toklistd term KType (tm_tap t τ) = toklistd term KType t ++ toklistd typ KType τ.
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_app. Qed.

End rw_toklistd_KType_type.

#[export] Hint Rewrite @rw_toklistd_KType_term1 @rw_toklistd_KType_term2 @rw_toklistd_KType_term3 @rw_toklistd_KType_term4 @rw_toklistd_KType_term5: sysf_rw.

(** *** <<toklistd>> with <<KTerm>> *)
(******************************************************************************)
Section rw_toklistd_KTerm_term.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_toklistd_KTerm_term1: forall (a: A), toklistd term KTerm (tm_var a) = [ (nil, a) ].
  Proof. reflexivity. Qed.

  Lemma rw_toklistd_KTerm_term2: forall τ t, toklistd term KTerm (tm_abs τ t) = toklistd typ KTerm τ ++ map (F:= list) (incr [KTerm]) (toklistd term KTerm t).
  Proof. intros. unfold toklistd, compose. rewrite rw_tomlistd_term2. rewrite filterk_app. now rewrite filterk_incr. Qed.

  Lemma rw_toklistd_KTerm_term3: forall t1 t2, toklistd term KTerm (tm_app t1 t2) = toklistd term KTerm t1 ++ toklistd term KTerm t2.
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_app. Qed.

  Lemma rw_toklistd_KTerm_term4: forall t, toklistd term KTerm (tm_tab t) = map (F:= list) (incr [KType]) (toklistd term KTerm t).
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_incr. Qed.

  Lemma rw_toklistd_KTerm_term5: forall t τ, toklistd term KTerm (tm_tap t τ) = toklistd term KTerm t ++ toklistd typ KTerm τ.
  Proof. intros. unfold toklistd, compose. autorewrite with sysf_rw. now rewrite filterk_app. Qed.

End rw_toklistd_KTerm_term.

#[export] Hint Rewrite @rw_toklistd_KTerm_term1 @rw_toklistd_KTerm_term2 @rw_toklistd_KTerm_term3 @rw_toklistd_KTerm_term4 @rw_toklistd_KTerm_term5: sysf_rw.

(** *** <<tomlist>> *)
(******************************************************************************)
Section rw_tomlist_term.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_tomlist_term1: forall (a: A), tomlist term (tm_var a) = [ (KTerm, a) ].
  Proof. reflexivity. Qed.

  Lemma rw_tomlist_term2: forall τ t, tomlist term (tm_abs τ t) = tomlist typ τ ++ tomlist term t.
  Proof.
    intros.
    unfold tomlist, tomlistd.
    unfold tomlistd_gen.
    unfold compose.
    rewrite mmapdt_to_mbinddt.
    rewrite mmapdt_to_mbinddt.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    simplify.
    change (?l1 ● ?l2) with (l1 ++ l2).
    autorewrite with tea_list.
    fequal.

    (*
    autorewrite with sysf_rw tea_list.
    compose near (tomlistd term t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.
     *)
  Admitted.

  Lemma rw_tomlist_term3: forall t1 t2, tomlist term (tm_app t1 t2) = tomlist term t1 ++ tomlist term t2.
  Proof. intros. unfold tomlist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_tomlist_term4: forall t, tomlist term (tm_tab t) = tomlist term t.
  Proof.
    intros. unfold tomlist, compose. autorewrite with sysf_rw.
    compose near (tomlistd term t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_tomlist_term5: forall t τ, tomlist term (tm_tap t τ) = tomlist term t ++ tomlist typ τ.
  Proof. intros. unfold tomlist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_tomlist_term.

#[export] Hint Rewrite @rw_tomlist_term1 @rw_tomlist_term2 @rw_tomlist_term3 @rw_tomlist_term4 @rw_tomlist_term5: sysf_rw.

(** *** <<toklist>> with <<KType>> *)
(******************************************************************************)
Section rw_toklist_KType_term.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_toklist_KType_term1: forall (a: A), toklist term KType (tm_var a) = [ ].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KType_term2: forall τ t, toklist term KType (tm_abs τ t) = toklist typ KType τ ++ toklist term KType t.
  Proof.
    intros. unfold toklist, compose.
    autorewrite with sysf_rw tea_list.
    compose near (toklistd term KType t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_toklist_KType_term3: forall t1 t2, toklist term KType (tm_app t1 t2) = toklist term KType t1 ++ toklist term KType t2.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_toklist_KType_term4: forall t, toklist term KType (tm_tab t) = toklist term KType t.
  Proof.
    intros. unfold toklist, compose. autorewrite with sysf_rw.
    compose near (toklistd term KType t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_toklist_KType_term5: forall t τ, toklist term KType (tm_tap t τ) = toklist term KType t ++ toklist typ KType τ.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_toklist_KType_term.

#[export] Hint Rewrite @rw_toklist_KType_term1 @rw_toklist_KType_term2 @rw_toklist_KType_term3 @rw_toklist_KType_term4 @rw_toklist_KType_term5: sysf_rw.

(** *** <<toklist>> with <<KTerm>> *)
(******************************************************************************)
Section rw_toklist_KTerm_term.

  Context
    (A: Type).

  Implicit Types (τ: typ A) (t: term A) (a: A).

  Lemma rw_toklist_KTerm_term1: forall (a: A), toklist term KTerm (tm_var a) = [ a ].
  Proof. reflexivity. Qed.

  Lemma rw_toklist_KTerm_term2: forall τ t, toklist term KTerm (tm_abs τ t) = toklist typ KTerm τ ++ toklist term KTerm t.
  Proof.
    intros. unfold toklist, compose. autorewrite with sysf_rw tea_list.
    compose near (toklistd term KTerm t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_toklist_KTerm_term3: forall t1 t2, toklist term KTerm (tm_app t1 t2) = toklist term KTerm t1 ++ toklist term KTerm t2.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

  Lemma rw_toklist_KTerm_term4: forall t, toklist term KTerm (tm_tab t) = toklist term KTerm t.
  Proof.
    intros. unfold toklist, compose. autorewrite with sysf_rw.
    compose near (toklistd term KTerm t) on left. rewrite (fun_map_map (F:= list)).
    repeat fequal. now ext [w a].
  Qed.

  Lemma rw_toklist_KTerm_term5: forall t τ, toklist term KTerm (tm_tap t τ) = toklist term KTerm t ++ toklist typ KTerm τ.
  Proof. intros. unfold toklist, compose. now autorewrite with sysf_rw tea_list. Qed.

End rw_toklist_KTerm_term.

#[export] Hint Rewrite @rw_toklist_KTerm_term1 @rw_toklist_KTerm_term2 @rw_toklist_KTerm_term3 @rw_toklist_KTerm_term4 @rw_toklist_KTerm_term5: sysf_rw.

(** *** Variable occurrence with context *)
(******************************************************************************)
Section rw_tomsetd_type.

  Context
    (A: Type)
    (k: K2).

  Implicit Types (w: list K) (a: A).

  Lemma rw_tomsetd_term1: forall w a a', (w, (k, a)) ∈md (tm_var a') <->  w = nil /\ k = KTerm /\ a = a'.
    intros. unfold tomsetd, compose. autorewrite with sysf_rw.
    rewrite tosubset_list_one.
    split.
    - now inversion 1.
    - intros [? [? ?]]; now subst.
  Qed.

  Lemma rw_tomsetd_term2: forall τ t w a,
      (w, (k, a)) ∈md (tm_abs τ t) <->
      (w, (k, a)) ∈md τ \/ exists w', (w', (k, a)) ∈md t /\ w = KTerm:: w'.
  Proof.
    intros. unfold tomsetd, compose. autorewrite with sysf_rw tea_list.
    rewrite (tosubset_map_iff). split.
    - intros [hyp | hyp].
      + now left.
      + right. destruct hyp as [[w' [j a'']] [hyp1 hyp2]].
        exists w'. inverts hyp2. easy.
    - intros [hyp | hyp].
      + now left.
      + right. destruct hyp as [w' [hyp1 hyp2]]. subst.
        exists (w', (k, a)). auto.
  Qed.

  Lemma rw_tomsetd_term3: forall w a (t1 t2: term A), (w, (k, a)) ∈md tm_app t1 t2 <-> ((w, (k, a)) ∈md t1 \/ (w, (k, a)) ∈md t2).
  Proof.
    intros. unfold tomsetd, compose.
    now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_tomsetd_term4: forall w a (t: term A), (w, (k, a)) ∈md (tm_tab t) <-> exists w', (w', (k, a)) ∈md t /\ w = KType:: w'.
  Proof.
    intros. unfold tomsetd, compose. autorewrite with sysf_rw.
    rewrite (tosubset_map_iff). splits.
    - intros [[w'' [j a']] [rest1 rest2]]. cbn in *. inverts rest2. eauto.
    - intros [w' rest]. exists (w', (k, a)). now inverts rest.
  Qed.

  Lemma rw_tomsetd_term5: forall w a (t: term A) (τ: typ A), (w, (k, a)) ∈md (tm_tap t τ) <-> (w, (k, a)) ∈md t \/ (w, (k, a)) ∈md τ.
  Proof.
    intros. unfold tomsetd, compose. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_tomsetd_type.

#[export] Hint Rewrite @rw_tomsetd_term1 @rw_tomsetd_term2 @rw_tomsetd_term3 @rw_tomsetd_term4 @rw_tomsetd_term5: sysf_rw.

(** *** Variable occurrence without context *)
(******************************************************************************)
Section rw_tomset_type.

  Context
    (A: Type)
    (k: K2).

  Implicit Types (a: A).

  Lemma rw_tomset_term1: forall a a', (k, a) ∈m tm_var a' <-> k = KTerm /\ a = a'.
    intros. unfold tomset, compose. autorewrite with sysf_rw.
    rewrite tosubset_list_one.
    split. inversion 1; easy. inversion 1; now subst.
  Qed.

  Lemma rw_tomset_term2: forall τ t a a',
      (k, a) ∈m (tm_abs τ t) <-> (k, a) ∈m τ \/ (k, a) ∈m t.
  Proof.
    intros. unfold tomset, compose. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_tomset_term3: forall a (t1 t2: term A), (k, a) ∈m tm_app t1 t2 <-> (k, a) ∈m t1 \/ (k, a) ∈m t2.
  Proof.
    intros. unfold tomset, compose. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_tomset_term4: forall a (t: term A), (k, a) ∈m tm_tab t <-> (k, a) ∈m t.
  Proof.
    intros. unfold tomset, compose. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_tomset_term5: forall a (t: term A) (τ: typ A), (k, a) ∈m tm_tap t τ <-> (k, a) ∈m t \/ (k, a) ∈m τ.
  Proof.
    intros. unfold tomset, compose. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_tomset_type.

#[export] Hint Rewrite @rw_tomset_term1 @rw_tomset_term2 @rw_tomset_term3 @rw_tomset_term4 @rw_tomset_term5: sysf_rw.

(** ** <<free>> and <<freeset>> *)
(******************************************************************************)

(** *** <<free>> with <<KType>> *)
(******************************************************************************)
Section rw_free_KType_term.

  Lemma rw_free_KType_term1: forall (l: LN), free term KType (tm_var l) = [].
  Proof. reflexivity. Qed.

  Lemma rw_free_KType_term2: forall τ t, free term KType (tm_abs τ t) = free typ KType τ ++ free term KType t.
  Proof.
    introv. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KType_term3: forall t1 t2, free term KType (tm_app t1 t2) = free term KType t1 ++ free term KType t2.
  Proof.
    introv. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KType_term4: forall t, free term KType (tm_tab t) = free term KType t.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_free_KType_term5: forall t τ, free term KType (tm_tap t τ) = free term KType t ++ free typ KType τ.
  Proof.
    dup. { intros. unfold free. now autorewrite with sysf_rw tea_list. }
    intros.
    unfold free.
    unfold toklist.
    unfold compose.
    unfold toklistd.
    unfold tomlistd.
    unfold tomlistd_gen.
    rewrite mmapdt_to_mbinddt.
    unfold compose.
  Admitted.

End rw_free_KType_term.

#[export] Hint Rewrite rw_free_KType_term1 rw_free_KType_term2 rw_free_KType_term3 rw_free_KType_term4 rw_free_KType_term5: sysf_rw.

(** *** <<freeset>> with <<KType>> *)
(******************************************************************************)
Section rw_freeset_KType_term.

  #[local] Open Scope set_scope.

  Lemma rw_freeset_KType_term1: forall (l: LN), freeset term KType (tm_var l) [=] ∅.
  Proof. reflexivity. Qed.

  Lemma rw_freeset_KType_term2: forall τ t, freeset term KType (tm_abs τ t) [=] freeset typ KType τ ∪ freeset term KType t.
  Proof.
    introv. unfold freeset. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

  Lemma rw_freeset_KType_term3: forall t1 t2, freeset term KType (tm_app t1 t2) [=] freeset term KType t1 ∪ freeset term KType t2.
  Proof.
    introv. unfold freeset. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

  Lemma rw_freeset_KType_term4: forall t, freeset term KType (tm_tab t) [=] freeset term KType t.
  Proof.
    intros. unfold freeset. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_freeset_KType_term5: forall t τ, freeset term KType (tm_tap t τ) [=] freeset term KType t ∪ freeset typ KType τ.
  Proof.
    intros. unfold freeset. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

End rw_freeset_KType_term.

#[export] Hint Rewrite rw_freeset_KType_term1 rw_freeset_KType_term2 rw_freeset_KType_term3 rw_freeset_KType_term4 rw_freeset_KType_term5: sysf_rw.

(** *** <<free>> with <<KTerm>> *)
(******************************************************************************)
Section rw_free_KTerm_term.

  Lemma rw_free_KTerm_term11: forall (x: atom), free term KTerm (tm_var (Fr x)) = [ x ].
  Proof. reflexivity. Qed.

  Lemma rw_free_KTerm_term12: forall (n: nat), free term KTerm (tm_var (Bd n)) = [ ].
  Proof. reflexivity. Qed.

  Lemma rw_free_KTerm_term2: forall τ t, free term KTerm (tm_abs τ t) = free typ KTerm τ ++ free term KTerm t.
  Proof.
    introv. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KTerm_term3: forall t1 t2, free term KTerm (tm_app t1 t2) = free term KTerm t1 ++ free term KTerm t2.
  Proof.
    introv. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

  Lemma rw_free_KTerm_term4: forall t, free term KTerm (tm_tab t) = free term KTerm t.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_free_KTerm_term5: forall t τ, free term KTerm (tm_tap t τ) = free term KTerm t ++ free typ KTerm τ.
  Proof.
    intros. unfold free. now autorewrite with sysf_rw tea_list.
  Qed.

End rw_free_KTerm_term.

#[export] Hint Rewrite rw_free_KTerm_term11 rw_free_KTerm_term12 rw_free_KTerm_term2 rw_free_KTerm_term3 rw_free_KTerm_term4 rw_free_KTerm_term5: sysf_rw.

(** *** <<freeset>> with <<KTerm>> *)
(******************************************************************************)
Section rw_freeset_KTerm_term.

  #[local] Open Scope set_scope.

  Lemma rw_freeset_KTerm_term11: forall (x: atom), freeset term KTerm (tm_var (Fr x)) [=] {{ x }}.
  Proof.
    introv. unfold freeset. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_freeset_KTerm_term12: forall (n: nat), freeset term KTerm (tm_var (Bd n)) [=] ∅.
  Proof. reflexivity. Qed.

  Lemma rw_freeset_KTerm_term2: forall τ t, freeset term KTerm (tm_abs τ t) [=] freeset typ KTerm τ ∪ freeset term KTerm t.
  Proof.
    introv. unfold freeset. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

  Lemma rw_freeset_KTerm_term3: forall t1 t2, freeset term KTerm (tm_app t1 t2) [=] freeset term KTerm t1 ∪ freeset term KTerm t2.
  Proof.
    introv. unfold freeset. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

  Lemma rw_freeset_KTerm_term4: forall t, freeset term KTerm (tm_tab t) [=] freeset term KTerm t.
  Proof.
    intros. unfold freeset. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_freeset_KTerm_term5: forall t τ, freeset term KTerm (tm_tap t τ) [=] freeset term KTerm t ∪ freeset typ KTerm τ.
  Proof.
    intros. unfold freeset. now autorewrite with sysf_rw tea_rw_atoms.
  Qed.

End rw_freeset_KTerm_term.

#[export] Hint Rewrite rw_freeset_KTerm_term11 rw_freeset_KTerm_term12 rw_freeset_KTerm_term2 rw_freeset_KTerm_term3 rw_freeset_KTerm_term4 rw_freeset_KTerm_term5: sysf_rw.

(** ** Locally nameless operations *)
(******************************************************************************)

(** *** <<subst>> with <<KType>> *)
(******************************************************************************)
Section rw_subst_KType_term.

  Context
    (x: atom)
    (u: typ LN).

  Lemma rw_subst_KType_term1: forall l, subst term KType x u (tm_var l) = tm_var l.
  Proof. reflexivity. Qed.

  Lemma rw_subst_KType_term2: forall τ t, subst term KType x u (tm_abs τ t) = tm_abs (subst typ KType x u τ) (subst term KType x u t).
  Proof.
    introv. unfold subst. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_subst_KType_term3: forall t1 t2, subst term KType x u (tm_app t1 t2) = tm_app (subst term KType x u t1) (subst term KType x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_KType_term4: forall t, subst term KType x u (tm_tab t) = tm_tab (subst term KType x u t).
  Proof.
    introv. unfold subst. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_subst_KType_term5: forall t τ, subst term KType x u (tm_tap t τ) = tm_tap (subst term KType x u t) (subst typ KType x u τ).
  Proof. reflexivity. Qed.

End rw_subst_KType_term.

#[export] Hint Rewrite @rw_subst_KType_term1 @rw_subst_KType_term2 @rw_subst_KType_term3 @rw_subst_KType_term4 @rw_subst_KType_term5: sysf_rw.

(** *** <<subst>> with <<KTerm>> *)
(******************************************************************************)
Section rw_subst_KTerm_term.

  Context
    (x: atom)
    (u: term LN).

  Lemma rw_subst_KTerm_term11: subst term KTerm x u (tm_var (Fr x)) = u.
  Proof. unfold subst. autorewrite with sysf_rw. cbn. compare values x and x. Qed.

  Lemma rw_subst_KTerm_term12: forall (y: atom), x <> y -> subst term KTerm x u (tm_var (Fr y)) = tm_var (Fr y).
  Proof. intros. unfold subst. autorewrite with sysf_rw. cbn. compare values x and y. Qed.

  Lemma rw_subst_KTerm_term13: forall (n: nat), subst term KTerm x u (tm_var (Bd n)) = tm_var (Bd n).
  Proof. reflexivity. Qed.

  Lemma rw_subst_KTerm_term2: forall τ t, subst term KTerm x u (tm_abs τ t) = tm_abs (subst typ KTerm x u τ) (subst term KTerm x u t).
  Proof.
    introv. unfold subst. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_subst_KTerm_term3: forall t1 t2, subst term KTerm x u (tm_app t1 t2) = tm_app (subst term KTerm x u t1) (subst term KTerm x u t2).
  Proof. reflexivity. Qed.

  Lemma rw_subst_KTerm_term4: forall t, subst term KTerm x u (tm_tab t) = tm_tab (subst term KTerm x u t).
  Proof.
    introv. unfold subst. now autorewrite with sysf_rw.
  Qed.

  Lemma rw_subst_KTerm_term5: forall t τ, subst term KTerm x u (tm_tap t τ) = tm_tap (subst term KTerm x u t) (subst typ KTerm x u τ).
  Proof. reflexivity. Qed.

End rw_subst_KTerm_term.

#[export] Hint Rewrite @rw_subst_KTerm_term11 @rw_subst_KTerm_term12 @rw_subst_KTerm_term13 @rw_subst_KTerm_term2 @rw_subst_KTerm_term3 @rw_subst_KTerm_term4 @rw_subst_KTerm_term5: sysf_rw.

#[local] Open Scope nat_scope.

(** *** <<locally_closed>> with <<KType>> *)
(******************************************************************************)
Section rw_lc_KType_term.

  Lemma rw_lc_KType_term1: forall l, locally_closed term KType (tm_var l).
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    introv. autorewrite with sysf_rw. introv [? [? ?]]; now subst.
  Qed.

  Lemma rw_lc_KType_term2: forall (τ: typ LN) (t: term LN), locally_closed term KType (tm_abs τ t) <-> locally_closed typ KType τ /\ locally_closed term KType t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_term2. split.
    - introv hyp. split.
      + intros. apply (hyp w l). now left.
      + intros. apply (hyp (KTerm:: w) l). right. eauto.
    - introv [hyp1 hyp2]. introv [hyp | hyp].
      + auto.
      + inverts hyp. inverts H. cbn. now apply hyp2.
  Qed.

  Lemma rw_lc_KType_term3: forall (t1 t2: term LN), locally_closed term KType (tm_app t1 t2) <-> locally_closed term KType t1 /\ locally_closed term KType t2.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_term3. firstorder.
  Qed.

  #[local] Open Scope nat_scope.

  Lemma rw_lc_KType_term4: forall t, locally_closed term KType (tm_tab t) <-> locally_closed_gap term KType 1 t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_term4. split.
    - intros hyp w l Hin.
      specialize (hyp (KType:: w) l). cbn in *.
      assert (rw: S (countk (@KType: K) w + 0) = (countk KType w + 1)) by lia.
      rewrite <- rw. apply hyp. eauto.
    - intros hyp w l [w' [H1 H2]]. subst.
      specialize (hyp w' l H1). cbn in *. destruct l.
      + easy.
      + lia.
  Qed.

  Lemma rw_lc_KType_term5: forall t τ, locally_closed term KType (tm_tap t τ) <-> locally_closed term KType t /\ locally_closed typ KType τ.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_term5. split.
    - introv hyp1. split.
      + introv hyp2. apply hyp1. now left.
      + introv hyp2. apply hyp1. now right.
    - introv [hyp1 hyp2] [hyp | hyp]; auto.
  Qed.

End rw_lc_KType_term.

#[export] Hint Rewrite @rw_lc_KType_term1 @rw_lc_KType_term2 @rw_lc_KType_term3 @rw_lc_KType_term4 @rw_lc_KType_term5: sysf_rw.

(** *** <<locally_closed>> with <<KTerm>> *)
(******************************************************************************)
Section rw_lc_KTerm_term.

  Lemma rw_lc_KTerm_term11: forall x, locally_closed term KTerm (tm_var (Fr x)).
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    introv. autorewrite with sysf_rw. introv [? [? ?]]; now subst.
  Qed.

  Lemma rw_lc_KTerm_term12: forall n, locally_closed term KTerm (tm_var (Bd n)) <-> False.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    split; [ |intuition]. introv hyp. cbn in hyp.
    specialize (hyp [] (Bd n) ltac:(auto)). cbn in hyp. lia.
  Qed.

  Lemma rw_lc_KTerm_term2: forall (τ: typ LN) (t: term LN), locally_closed term KTerm (tm_abs τ t) <-> locally_closed typ KTerm τ /\ locally_closed_gap term KTerm 1 t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_term2. split.
    - introv hyp. split.
      + intros. apply (hyp w l). now left.
      + intros. specialize (hyp (KTerm:: w) l). cbn in *.
      assert (rw: S (countk (@KTerm: K) w + 0) = (countk KTerm w + 1)) by lia.
      rewrite <- rw. apply hyp. eauto.
    - introv [hyp1 hyp2]. introv [hyp | hyp].
      + auto.
      + destruct hyp as [w' [hyp' hyp'']]. subst. cbn in *.
      assert (rw: S (countk (@KTerm: K) w' + 0) = (countk KTerm w' + 1)) by lia.
      rewrite rw. apply hyp2. auto.
  Qed.

  Lemma rw_lc_KTerm_term3: forall (t1 t2: term LN), locally_closed term KTerm (tm_app t1 t2) <-> locally_closed term KTerm t1 /\ locally_closed term KTerm t2.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_term3. firstorder.
  Qed.

  #[local] Open Scope nat_scope.

  Lemma rw_lc_KTerm_term4: forall t, locally_closed term KTerm (tm_tab t) <-> locally_closed term KTerm t.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_term4. split.
    - intros hyp w l Hin. specialize (hyp (KType:: w) l).
      apply hyp. eauto.
    - intros hyp w l [w' [rest1 rest2]]. subst.
      cbn. apply hyp; auto.
  Qed.

  Lemma rw_lc_KTerm_term5: forall t τ, locally_closed term KTerm (tm_tap t τ) <-> locally_closed term KTerm t /\ locally_closed typ KTerm τ.
  Proof.
    intros. unfold locally_closed, locally_closed_gap.
    setoid_rewrite rw_tomsetd_term5. split.
    - introv hyp1. split.
      + introv hyp2. apply hyp1. now left.
      + introv hyp2. apply hyp1. now right.
    - introv [hyp1 hyp2] [hyp | hyp]; auto.
  Qed.

End rw_lc_KTerm_term.

#[export] Hint Rewrite @rw_lc_KTerm_term11 @rw_lc_KTerm_term12 @rw_lc_KTerm_term2 @rw_lc_KTerm_term3 @rw_lc_KTerm_term4 @rw_lc_KTerm_term5: sysf_rw.

(** * Rewriting principles for <<ok_term>> *)
(******************************************************************************)
Lemma ok_term_abs: forall Δ Γ τ t,
    ok_term Δ Γ (tm_abs τ t) <->
    ok_type Δ τ /\
    scoped term KTerm t (AssocList.domset Γ) /\
    scoped term KType t (AssocList.domset Δ) /\
    locally_closed term KType t /\
    locally_closed_gap term KTerm 1 t.
Proof.
  intros. unfold ok_type, ok_term.
  unfold scoped.
  autorewrite with sysf_rw.
  intuition fsetdec.
Qed.

Lemma ok_term_app: forall Δ Γ t1 t2,
    ok_term Δ Γ (tm_app t1 t2) <-> ok_term Δ Γ t1 /\ ok_term Δ Γ t2.
Proof.
  intros. unfold ok_term, scoped.
  autorewrite with sysf_rw.
  intuition fsetdec.
Qed.
