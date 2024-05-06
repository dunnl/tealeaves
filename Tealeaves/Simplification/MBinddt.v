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

(** * Rewriting with binddt *)
(******************************************************************************)
Module ToBinddt.

  Ltac rewrite_core_ops_to_binddt :=
    match goal with
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

  (*
  Ltac rewrite_derived_ops_to_binddt T :=
    match goal with
    (* tolist *)
    | |- context[tolist (F := T) ?t] =>
        ltac_trace "tolist_to_binddt";
        rewrite (tolist_to_binddt (T := T))
    (* elements *)
    | |- context[element_of (F := T) ?x ?t] =>
        ltac_trace "element_of_to_binddt";
        rewrite (element_of_to_binddt (T := T))
    | |- context[element_ctx_of (T := T) (?n, ?l) ?t] =>
        ltac_trace "element_ctx_of_to_binddt";
        rewrite (element_ctx_of_to_binddt (T := T))
    (* tosubset *)
    | |- context[tosubset (F := T) ?t] =>
        ltac_trace "tosubset_to_binddt";
        rewrite (tosubset_to_binddt (T := T))
    | |- context[toctxset (F := T) ?t] =>
        ltac_trace "toctxset_to_binddt";
        rewrite (toctxset_to_binddt (T := T))
    (* foldMap *)
    | |- context[foldMap (T := T) ?t] =>
        ltac_trace "foldMap_to_binddt";
        rewrite foldMap_to_traverse1, traverse_to_binddt
    | |- context[foldMapd (T := T) ?t] =>
        ltac_trace "foldMap_to_binddt";
        rewrite (foldMapd_to_mapdt1 (T := T)),
          (mapdt_to_binddt (T := T))
    (* quantifiers *)
    | |- context[Forall_ctx (T := T)  ?P] =>
        ltac_trace "Forall_to_foldMapd";
        unfold Forall_ctx
    end.
    *)

End ToBinddt.

(*|
If we find some <<binddt f t>>, simplify it with cbn.
|*)
Ltac cbn_mbinddt :=
  match goal with
  | |- context[mbinddt (W := ?W) (T := ?T)
                (H := ?H) (H0 := ?H0) (H1 := ?H1)
                ?U ?F ?f ?t] =>
      let e := constr:(mbinddt (W := W) (T := T) U F
                         (H := H) (H0 := H0) (H1 := H1)
                         f t) in
      cbn_subterm e
      (*
      let e' := eval cbn in e in
        progress (change e with e')
       *)
  end.
