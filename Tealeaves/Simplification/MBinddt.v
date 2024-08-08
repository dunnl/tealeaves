From Tealeaves Require Export
  Simplification.Support
  Simplification.Binddt
  Theory.Multisorted.DecoratedTraversableMonad
  Classes.Multisorted.Theory.Foldmap.

Import
  Categories.TypeFamily.Notations
  List.ListNotations
  Product.Notations
  Monoid.Notations
  ContainerFunctor.Notations
  Subset.Notations
  Applicative.Notations.

Section local_lemmas_needed.

  Context
    `{ix: Index}
    {W: Type}
      {T: K -> Type -> Type}
      (U : Type -> Type)
      `{MultiDecoratedTraversablePreModule (ix := ix) W T U}
      `{! MultiDecoratedTraversableMonad (ix := ix) W T}.

  Lemma simplify_mmapdt_at_leaves_lemma :
    forall {k: K} {A B: Type} {G}
      `{Applicative G}
      (f : K -> W * A -> G B) (w: W) (a : A),
      (mapMret (T := T) ◻ f) k (w, a) =
        pure (mret T k) <⋆> f k (w, a).
  Proof.
    intros.
    unfold mapMret, vec_apply, vec_compose.
    rewrite <- map_to_ap.
    reflexivity.
  Qed.

End local_lemmas_needed.

(*|
Miscellaneous
|*)
Ltac normalize_K :=
  repeat
    match goal with
    | |- context[@K ?Ix] =>
        unfold K, Ix
    end.

(** * Rewriting with binddt *)
(******************************************************************************)
Module ToBinddt.

  Ltac rewrite_core_ops_to_mbinddt :=
    match goal with
    (* map *)
    | |- context[mmap ?f ?t] =>
        ltac_trace "mmap_to_mbinddt";
        progress (rewrite mmap_to_mbinddt)
    (* mapd/bind/traverse *)
    | |- context[mbind ?f ?t] =>
        ltac_trace "mbind_to_mbinddt";
        progress (rewrite mbind_to_mbinddt)
    | |- context[mmapd ?f ?t] =>
        ltac_trace "mmapd_to_mbinddt";
        progress (rewrite mmapd_to_mbinddt)
    (* mmapdt/bindd/bindt *)
    | |- context[mmapdt ?f ?t] =>
        ltac_trace "mmapdt_to_mbinddt";
        progress (rewrite mmapdt_to_mbinddt)
    | |- context[mbindd ?f ?t] =>
        ltac_trace "mbindd_to_mbinddt";
        progress (rewrite mbindd_to_mbinddt)
    | |- context[bindt ?f ?t] =>
        ltac_trace "bindt_to_mbinddt";
        progress (rewrite mbindt_to_mbinddt)
    end.

End ToBinddt.

Ltac cbn_mbinddt_post_hook := idtac.

(*|
mbinddt
|*)

(* We surround this with "repeat" to so we don't get stuck on a false target: a left-most binddt might be "simplified" to an equal-looking expression because the
   <<cbn>> simplifies some hidden argument, so that a right-more expression, the intended target, gets ignored *)
Ltac cbn_mbinddt :=
  repeat match goal with
  | |- context[mbinddt (W := ?W) (T := ?T)
                (H := ?H) (H0 := ?H0) (H1 := ?H1)
                ?U ?F ?f ?t] =>
      let e := constr:(mbinddt (W := W) (T := T) U F
                         (H := H) (H0 := H0) (H1 := H1)
                         f t) in
      (* cbn_subterm e *)
  let e' := eval cbn -[K btgd btg] in e in
    progress (change e with e'); cbn_mbinddt_post_hook

  end.

Ltac simplify_mbinddt_unfold_ret_hook := idtac.

Ltac simplify_mbinddt :=
  cbn_mbinddt;
  simplify_mbinddt_unfold_ret_hook.

(*|
mbindd
|*)
Ltac cbn_mbindd :=
  match goal with
  | |- context[mbindd (W := ?W) (T := ?T)
                ?U ?f ?t] =>
      let e := constr:(mbindd (W := W) (T := T) U f t) in
      cbn_subterm e
  end.

Ltac simplify_mbindd_post_refold_hook :=
  repeat simplify_applicative_I.

Ltac simplify_mbindd_pre_refold_hook ix := idtac.

Ltac simplify_mbindd :=
  match goal with
  | |- context[mbindd (ix := ?ix) (W := ?W) (T := ?T)
                ?U ?f ?t] =>
      rewrite ?mbindd_to_mbinddt;
      simplify_mbinddt;
      simplify_mbindd_pre_refold_hook ix;
      rewrite <- ?mbindd_to_mbinddt;
      simplify_mbindd_post_refold_hook
  end.

(*|
mbind
|*)
Ltac cbn_mbind :=
  match goal with
  | |- context[mbind (W := ?W) (T := ?T)
                ?U ?f ?t] =>
      let e := constr:(mbind (W := W) (T := T) U f t) in
      cbn_subterm e
  end.

(* after unfolding,
   mbindd U (f ◻ allK extract) (C x1 x2)
   is simplified to
   C (mbindd typ ((f ◻ allK extract) ◻ allK (incr [ktyp])) x1) ...
 *)
Ltac simplify_mbind_pre_refold_hook ix :=
  repeat ( rewrite vec_compose_assoc;
           rewrite (vec_compose_allK (H := ix));
           rewrite extract_incr).

Ltac simplify_mbind_post_refold_hook := idtac.

(* At a k-annotated leaf,
   mbind f (Ret x)
   becomes
   (f ◻ allK (extract (W := ?W))) k (Ƶ, x)] =>
 *)

Ltac simplify_mbind_at_leaf_hook :=
  repeat match goal with
      |- context [(?f ◻ allK (extract (W := ?W))) ?k (?w, ?a)] =>
        change ((?f ◻ allK (extract (W := ?W))) ?k (?w, ?a))
        with (f k a)
    end.

Ltac simplify_mbind :=
  match goal with
  | |- context[mbind (ix := ?ix) (W := ?W) (T := ?T)
                ?U ?f ?t] =>
      rewrite ?mbind_to_mbindd;
      simplify_mbindd;
      simplify_mbind_pre_refold_hook ix;
      rewrite <- ?mbind_to_mbindd;
      simplify_mbind_post_refold_hook;
      simplify_mbind_at_leaf_hook
  end.

(*|
mmapdt
|*)
Ltac cbn_mmapdt :=
  match goal with
  | |- context[mmapdt (W := ?W) (T := ?T)
                ?U ?F ?f ?t] =>
      let e := constr:(mmapdt (W := W) (T := T) U F
                         f t) in
      cbn_subterm e
  end.

Ltac reassociate_in_args ix :=
  match goal with
  | |- context[(?h ◻ ?g) ◻ ?f] =>
      (* rewrite (vec_compose_assoc (H := ix) h g f) *)
      rewrite vec_compose_assoc
  end.

(* After unfolding,
       mbinddt U (mapMret ◻ f) (C x1 x2)
       is simplified to (where w is C's decoration for x1)
       pure C <⋆> mbinddt U ((mapMret ◻ f) ◻ allK (incr w)) x1 <⋆> ...
 *)
Ltac simplify_mmapdt_pre_refold_hook ix :=
  repeat reassociate_in_args ix.

Ltac simplify_mmapdt_post_refold_hook := idtac.

Ltac simplify_mmapdt_at_leaves_hook :=
  rewrite ?(simplify_mmapdt_at_leaves_lemma _).

Ltac simplify_mmapdt :=
  match goal with
  | |- context[mmapdt (W := ?W) (T := ?T) (ix := ?ix)
                ?U ?f ?t] =>
      rewrite ?mmapdt_to_mbinddt;
      simplify_mbinddt;
      simplify_mmapdt_pre_refold_hook ix;
      rewrite <- ?mmapdt_to_mbinddt;
      simplify_mmapdt_post_refold_hook;
      simplify_mmapdt_at_leaves_hook
  end.

(*|
mmap
|*)

Ltac simplify_mmapd_pre_refold_hook ix := idtac.
Ltac simplify_mmapd_post_refold_hook :=
    repeat simplify_applicative_I.

Ltac simplify_mmapd :=
  match goal with
  | |- context[mmapd (W := ?W) (T := ?T) (ix := ?ix)
                ?U ?f ?t] =>
      rewrite ?mmapd_to_mmapdt;
      simplify_mmapdt;
      simplify_mmapd_pre_refold_hook ix;
      rewrite <- ?mmapdt_to_mbinddt;
      simplify_mmapd_post_refold_hook
  end.


(*
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
  (* new stuff *)
  | |- context[(?f ◻ allK extract) ◻ allK (incr ?w)] =>
      rewrite mextract_preincr2
  end.
 *)

