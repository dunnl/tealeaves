From Tealeaves Require Export
  Simplification.Support
  Simplification.Binddt
  Theory.Multisorted.DecoratedTraversableMonad.

Import
  List.ListNotations
  Product.Notations
  Monoid.Notations
  ContainerFunctor.Notations
  Subset.Notations.

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
Ltac cbn_mbinddt :=
  match goal with
  | |- context[mbinddt (W := ?W) (T := ?T)
                (H := ?H) (H0 := ?H0) (H1 := ?H1)
                ?U ?F ?f ?t] =>
      let e := constr:(mbinddt (W := W) (T := T) U F
                         (H := H) (H0 := H0) (H1 := H1)
                         f t) in
      (* cbn_subterm e *)
  let e' := eval cbn -[btgd btg] in e in
    progress (change e with e'); cbn_mbinddt_post_hook

  end.

Ltac simplify_mbinddt :=
  cbn_mbinddt.

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

Ltac simplify_mbindd :=
  match goal with
  | |- context[mbindd (W := ?W) (T := ?T)
                ?U ?f ?t] =>
      rewrite ?mbindd_to_mbinddt;
      simplify_mbinddt;
      rewrite <- ?mbindd_to_mbinddt;
      repeat simplify_applicative_I
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

Ltac simplify_mbind :=
  match goal with
  | |- context[mbind (W := ?W) (T := ?T)
                ?U ?f ?t] =>
      rewrite ?mbind_to_mbindd;
      simplify_mbindd;
      rewrite <- ?mbind_to_mbindd;
      repeat simplify_applicative_I
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

Ltac simplify_mmapdt :=
  cbn_mmapdt.

(*|
mmap
|*)
(*
Ltac cbn_mmap :=
  match goal with
  | |- context[mmap (W := ?W) (T := ?T)
                ?U ?f ?t] =>
      let e := constr:(mmap (W := W) (T := T) U f t) in
      cbn_subterm e
  end.

Ltac simplify_mmap :=
  match goal with
  | |- context[mmap (W := ?W) (T := ?T)
                ?U ?f ?t] =>
      rewrite ?mmap_to_mmapd;
      simplify_mmapd;
      rewrite <- ?mmap_to_mmapd;
      repeat simplify_applicative_I
  end.
*)





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

