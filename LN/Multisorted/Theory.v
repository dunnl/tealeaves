(** This files contains metatheorems for the locally nameless variables
 that closely parallel those of Metalib. *)
From Tealeaves Require Import
     Util.Prelude
     Util.EqDec_eq LN.Atom LN.AtomSet
     Multisorted.Classes.Monad
     LN.Multisorted.Operations.

Import Monoid.Notations.
Import LN.AtomSet.Notations.
Import Singlesorted.Classes.SetlikeFunctor.Notations.
Import Multisorted.Classes.SetlikeFunctor.Notations.
#[local] Open Scope tealeaves_scope.
#[local] Open Scope tealeaves_multi_scope.
#[local] Open Scope set_scope.

Notation "↑" := (btg).
Arguments btg {ix} {T}%function_scope {MReturn0} {A}%type_scope k _%function_scope.
Arguments subst_loc {ix} {T}%function_scope {H0} {k}.
Arguments open_loc {ix} {T}%function_scope {H0} {k}.

(** * Lemmas for local reasoning *)
(** The following lemmas govern the behavior of the <<*_loc>> operations of
      the locally nameless library. These are put into a hint database
      <<tea_local>> to use with <<autorewrite>>. Since <<autorewrite>> tries the
      first unifying lemma (even if this generates absurd side conditions), we
      use <<Hint Rewrite ... using ...>> clauses and typically prefer
      <<autorewrite*>>, which only uses hints whose side conditions are
      discharged by the associated tactic. *)

Create HintDb tea_local.

Section locally_nameless_utilities.

  Context
    `{DecoratedMultisortedMonad
        (Row nat) (mn_op := Monoid_op_Row)
        (mn_unit := Monoid_unit_Row) T}
    `{! forall k, Tomlist (T k)} `{! ListableMultisortedMonad T}.

  Implicit Types (k j : K).

  (** ** [toset] and [mret] *)
  (** TODO KLUDGE : These are mostly redundant and should go elsewhere, but
      there are some typeclass issues that need to be resolved
      first. *)
  (******************************************************************************)
  Lemma in_mret_iff {A} : forall k1 k2 (a a' : A),
      (k2, a') ∈m mret T k1 a <-> k1 = k2 /\ a = a'.
  Proof.
    intros.
    (* KLUDGE *)
    (*
    change ((@tomset_Listable H H (T k1) (H2 k1))) with
        ((fun k => @tomset_Listable H H (T k) (H2 k)) k1).
    now rewrite (in_mret_iff F T).
    *)
  Admitted.

  Lemma in_mret_iff_eq {A} : forall k (a a' : A),
      (k, a') ∈m mret T k a <-> a = a'.
  Proof.
    intros.
    now rewrite in_mret_iff.
  Qed.

  Lemma ind_mret_iff {A} : forall k j w (a a' : A),
      (j, (w, a')) ∈md mret T k a <-> k = j /\ w = Ƶ /\ a = a'.
  Proof.
    intros.
    Set Printing Implicit.
    About ind_mret_iff.
    now rewrite (ind_mret_iff T w j k a a').
    change ((@tomset_Listable ix ix (T k) (H5 k))) with
        ((fun k => @tomset_Listable ix ix (T k) (H5 k)) k).
    now rewrite (ind_mret_iff F T w j k a a').
  Qed.

  Lemma ind_mret_iff_eq {A} : forall k w (a a' : A),
      (k, (w, a')) ∈md mret T k a <-> w = Ƶ /\ a = a'.
  Proof.
    intros. now rewrite (ind_mret_iff).
  Qed.

  (** ** (In)equalities between leaves *)
  Lemma Fr_injective : forall (x y : atom),
      (Fr x = Fr y) <-> (x = y).
  Proof.
    intros. split; intro hyp.
    now injection hyp. now subst.
  Qed.

  Lemma Fr_injective_not_iff : forall (x y : atom),
      (Fr x <> Fr y) <-> (x <> y).
  Proof.
    intros. split; intro hyp; contradict hyp.
    now subst. now injection hyp.
  Qed.

  Lemma Fr_injective_not : forall (x y : atom),
      x <> y -> ~ (Fr x = Fr y).
  Proof.
    intros. now rewrite Fr_injective.
  Qed.

  Lemma B_neq_Fr : forall n x,
      (Bd n = Fr x) = False.
  Proof.
    introv. propext. discriminate. contradiction.
  Qed.

  (** ** [subst_loc] *)
  (******************************************************************************)
  Lemma subst_loc_eq : forall k (u : T k leaf) x,
      subst_loc x u (Fr x) = u.
  Proof. intros. cbn. now compare values x and x. Qed.

  Lemma subst_loc_neq : forall k (u : T k leaf) x y,
      y <> x -> subst_loc x u (Fr y) = mret T k (Fr y).
  Proof. intros. cbn. now compare values x and y. Qed.

  Lemma subst_loc_b : forall k u x n,
      subst_loc x u (Bd n) = mret T k (Bd n).
  Proof. reflexivity. Qed.

  Lemma subst_loc_fr_neq : forall k (u : T k leaf) l x,
      Fr x <> l -> subst_loc x u l = mret T k l.
  Proof.
    introv neq. unfold subst_loc.
    destruct l as [a|?]; [compare values x and a | reflexivity ].
  Qed.

  Existing Instance DecoratedMultisortedModule_Monad.
  Import Operations.Notations.

  Lemma subst_in_mret_eq : forall k x l (u : T k leaf),
      (mret T k l) '{k | x ~> u} = subst_loc x u l.
  Proof.
    intros. unfold subst. compose near l on left.
    now rewrite (bindk_comp_mret_eq (T k)).
  Qed.

  Lemma subst_in_mret_neq : forall k j x l (u : T j leaf),
      j <> k ->
      (mret T k l) '{j | x ~> u} = mret T k l.
  Proof.
    intros. unfold subst. compose near l on left.
    now rewrite (bindk_comp_mret_neq (T k)).
  Qed.

  (** ** [open_loc] *)
  (******************************************************************************)
  Lemma open_loc_lt : forall k (u : T k leaf) w n,
      n < w k -> open_loc u (w, Bd n) = mret T k (Bd n).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and (w k).
  Qed.

  Lemma open_loc_gt : forall k (u : T k leaf) n w,
      n > w k -> open_loc u (w, Bd n) = mret T k (Bd (n - 1)).
  Proof.
    introv ineq. unfold open_loc. compare naturals n and (w k).
  Qed.

  Lemma open_loc_eq : forall k w (u : T k leaf),
      open_loc u (w, Bd (w k)) = u.
  Proof.
    introv. unfold open_loc. compare naturals (w k) and (w k).
  Qed.

  Lemma open_loc_atom : forall k (u : T k leaf) w x,
      open_loc u (w, Fr x) = mret T k (Fr x).
  Proof.
    reflexivity.
  Qed.

  (** ** [Miscellaneous utilities] *)
  (******************************************************************************)
  Lemma ninf_in_neq : forall k x l (t : F leaf),
      ~ x ∈ free F k t ->
      (k, l) ∈m t -> Fr x <> l.
  Proof.
    introv hyp1 hyp2.
    rewrite in_free_iff in hyp1. destruct l.
    - injection. intros; subst.
      contradiction.
    - discriminate.
  Qed.

  Lemma ninf_in_neq_t : forall k' (t : T k' leaf) k x l,
      ~ x ∈ free (T k') k t -> (k, l) ∈m t -> Fr x <> l.
  Proof.
    introv hyp1 hyp2.
    rewrite in_free_iff in hyp1. destruct l.
    - injection. intros; subst.
      contradiction.
    - discriminate.
  Qed.

  Lemma neq_symmetry : forall X (x y : X),
      (x <> y) = (y <> x).
  Proof.
    intros. propext; intro hyp; contradict hyp; congruence.
  Qed.

  (** ** Local closure *)
(*
  Lemma is_bound_or_free_op: forall (w1 w2 : Row nat) (l : leaf),
      is_bound_or_free k (w1, l) ->
      is_bound_or_free k (w2 ● w1, l).
  Proof.
    unfold monoid_op, Monoid_op_Row, monoid_op, Monoid_op_plus.
    unfold is_bound_or_free. introv hyp.
    destruct l; [easy |]. lia.
  Qed.  *)

End locally_nameless_utilities.

Tactic Notation "unfold_monoid" :=
  repeat unfold monoid_op, Monoid_op_Row, Monoid_op_plus,
  monoid_unit, Monoid_unit_Row, Monoid_unit_zero in *.

Tactic Notation "unfold_lia" :=
  unfold_monoid; lia.

Hint Rewrite @in_mret_iff @in_mret_iff_eq
     @ind_mret_iff @ind_mret_iff_eq using typeclasses eauto : tea_local.

Hint Rewrite Fr_injective Fr_injective_not_iff B_neq_Fr : tea_local.
#[export] Hint Resolve Fr_injective_not : tea_local.

Hint Rewrite @subst_loc_eq @subst_in_mret_eq using typeclasses eauto : tea_local.
Hint Rewrite @subst_loc_neq @subst_loc_b @subst_loc_fr_neq @subst_in_mret_neq
     using first [ typeclasses eauto | auto ] : tea_local.

Hint Rewrite @open_loc_lt @open_loc_gt
     using first [ typeclasses eauto | auto ] : tea_local.
Hint Rewrite @open_loc_eq @open_loc_atom using typeclasses eauto : tea_local.

Tactic Notation "simpl_local" := (autorewrite* with tea_local).

(** * Locally nameless metatheory *)
(******************************************************************************)
Section locally_nameless_metatheory.

  Context
    `{DecoratedMultisortedModule
        (Row nat) (mn_op := Monoid_op_Row)
        (mn_unit := Monoid_unit_Row) F T}
    `{! Tomlist F} `{! forall k, Tomlist (T k)} `{! ListableMultisortedModule F T}.

  Existing Instance DecoratedMultisortedModule_Monad.
  Existing Instance ListableMultisortedModule_Monad.
  Import Operations.Notations.

  Implicit Types
           (k : K) (j : K)
           (l : leaf) (p : leaf)
           (x : atom) (t : F leaf)
           (w : Row nat) (n : nat).

  (** ** Leaf analysis: substitution with contexts *)
  Lemma ind_subst_loc_iff : forall k l w j p (u : T k leaf) x,
      (j, (w, p)) ∈md subst_loc x u l <->
      l <> Fr x /\ k = j /\ w = Ƶ /\ l = p \/ (* l is not replaced *)
      l = Fr x /\ (j, (w, p)) ∈md u. (* l is replaced *)
  Proof.
    introv. compare l to atom x; simpl_local; intuition.
  Qed.

  Corollary ind_subst_loc_iff_eq : forall k l w p (u : T k leaf) x,
      (k, (w, p)) ∈md subst_loc x u l <->
      l <> Fr x /\ w = Ƶ /\ l = p \/
      l = Fr x /\ (k, (w, p)) ∈md u.
  Proof.
    introv. rewrite ind_subst_loc_iff. intuition.
  Qed.

  Corollary ind_subst_loc_iff_neq : forall k l w j p (u : T k leaf) x,
      k <> j ->
      (j, (w, p)) ∈md subst_loc x u l <->
      l = Fr x /\ (j, (w, p)) ∈md u.
  Proof.
    introv neq. rewrite ind_subst_loc_iff. intuition.
  Qed.

  Theorem ind_subst_iff : forall k j w t u l x,
      (* <<l>> occurs in the result of a <<subst>> IFF *)
      (j, w, l) ∈md t '{k | x ~> u} <->
      (* <<l>> is an occurrence in <<t>> not of the same sort as the <<subst>> OR *)
      k <> j /\ (j, w, l) ∈md t \/
      (* <<l>> is an occurrence of the same sort but not an occurrence of <<x>> OR *)
      k = j /\ (k, w, l) ∈md t /\ l <> Fr x \/
      (* <<x>> occurs and <<l>> is the any leaf in a substituted <<u>> *)
      exists w1 w2 : Row nat, (k, w1, Fr x) ∈md t /\ (j, w2, l) ∈md u /\ w = w1 ● w2.
  Proof with auto.
    intros. compare values k and j.
    - rewrite (ind_subst_iff_eq F). setoid_rewrite (ind_subst_loc_iff_eq j).
      split.
      + intros [l' [n1 [n2 conditions]]].
        right. destruct conditions as [c1 [[c2|c2] c3]].
        { subst. left. destructs c2; subst.
          rewrite monoid_id_l. auto. }
        { subst. right. destructs c2; subst. eauto. }
      + intros [[contra ?] | [ [? [in_t neq]] | hyp ] ].
        { contradiction.  }
        { exists l w (Ƶ : Row nat). rewrite monoid_id_l. split... }
        { destruct hyp as [w1 [w2 ?]]. exists (Fr x) w1 w2. intuition. }
    - rewrite (ind_subst_iff_neq F)... split.
      + intros [? | [p [n1 [n2 [in_t in_local]]]]]...
        rewrite (ind_subst_loc_iff_neq k) in in_local...
        right. right. exists n1 n2. destruct in_local as [[? ?] ?]; subst...
      + intros [[? ?] | [[? ?] | ?]].
        { auto. }
        { contradiction. }
        { right. exists (Fr x). simpl_local... }
  Qed.

  Corollary ind_subst_iff_eq : forall k w t u l x,
      (k, w, l) ∈md t '{k | x ~> u} <->
      (k, w, l) ∈md t /\ l <> Fr x \/
      exists w1 w2 : Row nat, (k, w1, Fr x) ∈md t /\ (k, w2, l) ∈md u /\ w = w1 ● w2.
  Proof.
    intros. rewrite ind_subst_iff. intuition.
  Qed.

  Corollary ind_subst_iff_neq : forall k j w t u l x,
      k <> j ->
      (j, w, l) ∈md t '{k | x ~> u} <->
      (j, w, l) ∈md t \/
      exists w1 w2 : Row nat, (k, w1, Fr x) ∈md t /\ (j, w2, l) ∈md u /\ w = w1 ● w2.
  Proof.
    intros. rewrite ind_subst_iff. intuition.
  Qed.

  (** ** Leaf analysis: substitution without contexts *)
  Lemma in_subst_loc_iff : forall k l j p (u : T k leaf) x,
      (j, p) ∈m subst_loc x u l <->
      l <> Fr x /\ k = j /\ l = p \/
      l = Fr x /\ (j, p) ∈m u.
  Proof.
    introv. compare l to atom x; autorewrite* with tea_local; intuition.
  Qed.

  Corollary in_subst_loc_iff_eq : forall k l p (u : T k leaf) x,
      (k, p) ∈m subst_loc x u l <->
      l <> Fr x /\ l = p \/
      l = Fr x /\ (k, p) ∈m u.
  Proof.
    introv. rewrite in_subst_loc_iff; intuition.
  Qed.

  Corollary in_subst_loc_iff_neq : forall k l j p (u : T k leaf) x,
      k <> j ->
      (j, p) ∈m subst_loc x u l <->
      l = Fr x /\ (j, p) ∈m u.
  Proof.
    introv neq. rewrite in_subst_loc_iff. intuition.
  Qed.

  Theorem in_subst_iff : forall k j t u l x,
      (* <<l>> occurs in the result of a <<subst>> IFF *)
      (j, l) ∈m t '{k | x ~> u} <->
      (* <<l>> is an occurrence in <<t>> not of the same sort as the <<subst>> OR *)
      k <> j /\ (j, l) ∈m t \/
      (* <<l>> is an occurrence of the same sort but not an occurrence of <<x>> OR *)
      k = j /\ (k, l) ∈m t /\ l <> Fr x \/
      (* <<x>> occurs and <<l>> is the any leaf in a substituted <<u>> *)
      (k, Fr x) ∈m t /\ (j, l) ∈m u.
  Proof with auto.
    intros. destruct_eq_args k j.
    - rewrite (in_subst_iff_eq F).
      setoid_rewrite (in_subst_loc_iff_eq). split.
      + intros [? [?  in_sub]].
        destruct in_sub as [[? heq] | [heq ?]]; subst...
      + intros [[contra ?] | [ [? [in_t neq]] | ? ] ].
        { contradiction.  }
        { exists l... }
        { exists (Fr x). intuition. }
    - rewrite (in_subst_iff_neq F); auto. split.
      + intros [? | [p [in_t in_local]] ]; auto.
        rewrite in_subst_loc_iff_neq in in_local; auto.
        destruct in_local as [? ?]; subst. auto.
      + intros [[? ?] | [[? ?] | ?]].
        { auto. }
        { contradiction. }
        { right. exists (Fr x). simpl_local... }
  Qed.

  Corollary in_subst_iff_eq : forall k t u l x,
      (k, l) ∈m t '{k | x ~> u} <->
      (k, l) ∈m t /\ l <> Fr x \/
      (k, Fr x) ∈m t /\ (k, l) ∈m u.
  Proof with auto.
    intros. rewrite in_subst_iff. intuition.
  Qed.

  Corollary in_subst_iff_neq : forall k j t u l x,
      k <> j ->
      (j, l) ∈m t '{k | x ~> u} <->
      (j, l) ∈m t \/
      (k, Fr x) ∈m t /\ (j, l) ∈m u.
  Proof with auto.
    intros. rewrite in_subst_iff. intuition.
  Qed.

  (** ** Free variables after substitution *)
    (* TODO : We can give this one an exact characterization without ∈ *)
  Corollary in_free_subst_iff_eq : forall t k u x y,
      y ∈ free F k (t '{k | x ~> u}) <->
      y ∈ free F k t /\ y <> x \/ x ∈ free F k t /\ y ∈ free (T k) k u.
  Proof.
    intros. repeat rewrite (in_free_iff).
    rewrite in_subst_iff_eq. now simpl_local.
  Qed.

  Corollary in_freeset_subst_iff_eq : forall t k u x y,
      y ∈@ freeset F k (t '{k | x ~> u}) <->
      y ∈@ freeset F k t /\ y <> x \/
      x ∈@ freeset F k t /\ y ∈@ freeset (T k) k u.
  Proof.
    intros. repeat rewrite <- (free_iff_freeset).
    apply in_free_subst_iff_eq.
  Qed.

  Corollary in_free_subst_iff_neq : forall t k j u x y,
      k <> j ->
      y ∈ free F j (t '{k | x ~> u}) <->
      y ∈ free F j t \/ x ∈ free F k t /\ y ∈ free (T k) j u.
  Proof.
    intros. repeat rewrite (in_free_iff).
    rewrite in_subst_iff_neq; auto. reflexivity.
  Qed.

  Corollary in_freeset_subst_iff_neq : forall t k j u x y,
      k <> j ->
      y ∈@ freeset F j (t '{k | x ~> u}) <->
      y ∈@ freeset F j t \/
      x ∈@ freeset F k t /\ y ∈@ freeset (T k) j u.
  Proof.
    intros. repeat rewrite <- (free_iff_freeset).
    auto using in_free_subst_iff_neq.
  Qed.

  (** ** Upper and lower bounds for leaves after substitution *)
  Corollary in_subst_upper : forall k j t u l x,
      (j, l) ∈m t '{k | x ~> u} ->
      (j, l) ∈m t /\ (j, l) <> (k, Fr x) \/ (j, l) ∈m u.
  Proof with auto.
    introv hin. rewrite in_subst_iff in hin.
    destruct hin as [[hyp1 hyp2] | [hyp | hyp] ].
    - left. split; [assumption |]. injection...
    - destructs hyp. subst. left.
      split; [assumption |]. injection...
    - intuition.
  Qed.

  Lemma prod_K_not_iff : forall (k : K) A (x y : A),
      ((k, x) <> (k, y)) <-> (x <> y).
  Proof.
    intros. split; intro hyp; contradict hyp.
    now subst. now injection hyp.
  Qed.

  Hint Rewrite prod_K_not_iff : tea_local.

  Corollary in_subst_upper_eq : forall k t u l x,
      (k, l) ∈m t '{k | x ~> u} ->
      (k, l) ∈m t /\ l <> Fr x \/ (k, l) ∈m u.
  Proof.
    introv hyp. apply in_subst_upper in hyp.
    autorewrite* with tea_local in hyp.
    intuition.
  Qed.

  Corollary in_subst_upper_neq : forall k j t u l x,
      k <> j ->
      (j, l) ∈m t '{k | x ~> u} ->
      (j, l) ∈m t \/ (j, l) ∈m u.
  Proof.
    introv neq hyp. apply in_subst_upper in hyp.
    intuition.
  Qed.

  Corollary in_free_subst_upper : forall k j t u x y,
      y ∈ free F j (t '{k | x ~> u}) ->
      (y ∈ free F j t /\ j <> k) \/ (y ∈ free F k t /\ y <> x /\ k = j) \/ y ∈ free (T k) j u.
  Proof.
    setoid_rewrite (in_free_iff). introv hyp.
    apply in_subst_upper in hyp.
    destruct hyp as [hyp | hyp].
    - destruct hyp. compare values j and k.
      + right. left. splits; auto.
        intro contra; subst; contradiction.
      + auto.
    - eauto using in_subst_upper.
  Qed.

  Corollary in_free_subst_upper_eq : forall k t u x y,
      y ∈ free F k (t '{k | x ~> u}) ->
      (y ∈ free F k t /\ y <> x) \/ y ∈ free (T k) k u.
  Proof.
    introv hyp. apply in_free_subst_upper in hyp.
    intuition.
  Qed.

  Corollary in_free_subst_upper_neq : forall k j t u x y,
      k <> j ->
      y ∈ free F j (t '{k | x ~> u}) ->
      y ∈ free F j t \/ y ∈ free (T k) j u.
  Proof.
    introv neq hyp. apply in_free_subst_upper in hyp.
    intuition.
  Qed.

  Corollary freeset_subst_upper : forall k j t u x y,
      y ∈@ freeset F j (t '{k | x ~> u}) ->
      k = j /\ y ∈@ (freeset F k t \\ {{x}} ∪ freeset (T k) j u) \/
      k <> j /\ y ∈@ (freeset F j t ∪ freeset (T k) j u).
  Proof.
    setoid_rewrite AtomSet.union_spec.
    setoid_rewrite AtomSet.diff_spec.
    setoid_rewrite <- free_iff_freeset.
    introv hyp. apply in_free_subst_upper in hyp.
    compare values j and k.
    + left. destruct hyp as [hyp | [hyp | hyp]].
      { split; auto. intuition. }
      { split; auto. left. split. intuition. fsetdec. }
      { split; auto. }
    + right. split; auto. destruct hyp as [hyp | [hyp | hyp]].
      { intuition. }
      { intuition. }
      { intuition. }
  Qed.

  Corollary freeset_subst_upper_eq : forall k t u x,
      freeset F k (t '{k | x ~> u}) ⊆
              (freeset F k t \\ {{x}} ∪ freeset (T k) k u).
  Proof.
    intros. intros a hyp. apply freeset_subst_upper in hyp.
    intuition.
  Qed.

  Corollary freeset_subst_upper_neq : forall k j t u x,
      k <> j ->
      freeset F j (t '{k | x ~> u}) ⊆
              (freeset F j t ∪ freeset (T k) j u).
  Proof.
    intros. intros a hyp. apply freeset_subst_upper in hyp.
    intuition.
  Qed.

  Corollary in_subst_lower_eq : forall t k u l x,
      (k, l) ∈m t /\ l <> Fr x ->
      (k, l) ∈m t '{k | x ~> u}.
  Proof with auto.
    intros; rewrite in_subst_iff...
  Qed.

  Corollary in_subst_lower_neq : forall t k j u l x,
      k <> j ->
      (j, l) ∈m t ->
      (j, l) ∈m t '{k | x ~> u}.
  Proof with auto.
    intros; rewrite in_subst_iff...
  Qed.

  Corollary in_free_subst_lower_eq : forall t k (u : T k leaf) x y,
      y ∈ free F k t /\ y <> x ->
      y ∈ free F k (t '{k | x ~> u}).
  Proof.
    setoid_rewrite (in_free_iff). intros.
    apply in_subst_lower_eq. now simpl_local.
  Qed.

  Corollary in_free_subst_lower_neq : forall t k j u x y,
      k <> j ->
      y ∈ free F j t ->
      y ∈ free F j (t '{k | x ~> u}).
  Proof.
    setoid_rewrite (in_free_iff). intros.
    now apply in_subst_lower_neq.
  Qed.

  Corollary freeset_subst_lower_eq : forall t k (u : T k leaf) x,
      freeset F k t \\ {{ x }} ⊆ freeset F k (t '{k | x ~> u}).
  Proof.
    introv. intro a. rewrite AtomSet.diff_spec.
    do 2 rewrite <- (free_iff_freeset).
    intros [? ?]. apply in_free_subst_lower_eq.
    intuition.
  Qed.

  Corollary freeset_subst_lower_eq_alt : forall t k (u : T k leaf) x,
      freeset F k t ⊆ freeset F k (t '{k | x ~> u}) ∪ {{ x }}.
  Proof.
    introv. intro a. rewrite AtomSet.union_spec.
    do 2 rewrite <- (free_iff_freeset).
    destruct_eq_args a x.
    - right. fsetdec.
    - left. auto using in_free_subst_lower_eq.
  Qed.

  Corollary scoped_subst_eq : forall t k (u : T k leaf) x γ1 γ2,
      scoped F k t γ1 ->
      scoped (T k) k u γ2 ->
      scoped F k (t '{k | x ~> u}) (γ1 \\ {{x}} ∪ γ2).
  Proof.
    introv St Su. unfold scoped in *.
    etransitivity. apply freeset_subst_upper_eq. fsetdec.
  Qed.

  Corollary freeset_subst_lower_neq : forall t k j u x,
      k <> j ->
      freeset F j t ⊆
      freeset F j (t '{k | x ~> u}).
  Proof.
    introv neq. intro a.
    do 2 rewrite <- (free_iff_freeset).
    now apply in_free_subst_lower_neq.
  Qed.

  (** ** Substitution of fresh variables *)
  Theorem subst_fresh : forall t k x u,
      ~ x ∈ free F k t ->
      t '{k | x ~> u} = t.
  Proof.
    intros. apply (subst_id F). intros.
    assert (Fr x <> l) by eauto using (ninf_in_neq (F := F)).
    now simpl_local.
  Qed.

  Corollary subst_fresh_set : forall t k x u,
      ~ x ∈@ freeset F k t ->
      t '{k | x ~> u} = t.
  Proof.
    setoid_rewrite <- free_iff_freeset. apply subst_fresh.
  Qed.

  Theorem subst_fresh_t : forall k' (t : T k' leaf) k x u,
      ~ x ∈ free (T k') k t ->
      t '{k | x ~> u} = t.
  Proof.
    intros. apply (subst_id (T k')). intros.
    assert (Fr x <> l) by eauto using ninf_in_neq_t.
    now simpl_local.
  Qed.

  Corollary subst_fresh_set_t : forall k' (t : T k' leaf) k x u,
      ~ x ∈@ freeset (T k') k t ->
      t '{k | x ~> u} = t.
  Proof.
    setoid_rewrite <- free_iff_freeset. apply subst_fresh_t.
  Qed.

  Theorem free_subst_fresh : forall t k j u x,
      ~ x ∈ free F k t ->
      free F j (t '{k | x ~> u}) = free F j t.
  Proof with auto.
    introv fresh. replace (t '{k | x ~> u}) with t...
    rewrite subst_fresh...
  Qed.

  Corollary free_subst_fresh_eq : forall t k u x,
      ~ x ∈ free F k t ->
      free F k (t '{k | x ~> u}) = free F k t.
  Proof.
    introv fresh. replace (t '{k | x ~> u}) with t; auto.
    now rewrite subst_fresh.
  Qed.

  Corollary freeset_subst_fresh : forall t k j u x,
      ~ x ∈@ freeset F k t ->
      freeset F j (t '{k | x ~> u}) [=] freeset F j t.
  Proof.
    introv fresh. intro y.
    rewrite <- ?(free_iff_freeset) in *.
    now rewrite free_subst_fresh.
  Qed.

  Corollary freeset_subst_fresh_eq : forall t k u x,
      ~ x ∈@ freeset F k t ->
      freeset F k (t '{k | x ~> u}) [=] freeset F k t.
  Proof.
    intros. apply freeset_subst_fresh; auto.
  Qed.

  (** ** Composing substitutions *)


  Create HintDb tmp.
  Hint Rewrite @subst_in_mret_neq using auto : tmp.
       (* using (solve [typeclasses eauto] || auto ] : tea_local. *)

  Lemma subst_subst_neq_loc : forall j k1 k2 (u1 : T k1 leaf) (u2 : T k2 leaf) (x1 x2 : atom),
      k1 <> k2 ->
      ~ x1 ∈ free (T k2) k1 u2 ->
      subst (T j) k2 x2 u2 ∘ ↑ k1 (subst_loc x1 u1) j =
      subst (T j) k1 x1 (subst (T k1) k2 x2 u2 u1) ∘ ↑ k2 (subst_loc x2 u2) j.
  Proof with easy.
    intros. ext l. unfold compose. compare j to both of { k1 k2 }.
    - do 2 simpl_tgt_fallback.

      rewrite (subst_in_mret_eq (F := F)).

      Set Printing Implicit.
      About subst_in_mret_eq.

      pose (@subst_in_mret_eq ix F T _ _ _ _ _ _ k1 x1 l).
      rewrite e.
      k1 x1 l (u1 '{ k2 | x2 ~> u2})).
      pose (subst_in_mret_eq k1 x1 l (u1 '{ k2 | x2 ~> u2})).

      Hint Rewrite @subst_loc_eq @subst_in_mret_eq using typeclasses eauto : tea_local.
Hint Rewrite @subst_loc_neq @subst_loc_b @subst_loc_fr_neq @subst_in_mret_neq

      simpl_local.
      compare l to atom x1.
      + rewrite 2(subst_loc_eq)...
      + rewrite subst_loc_neq; auto. now simpl_local.
      + rewrite subst_loc_b. now simpl_local.
    - simpl_tgt. simpl_local. compare l to atom x2.
      + simpl_local. rewrite subst_fresh_t...
      + simpl_local...
      + simpl_local...
    - simpl_tgt_fallback. now do 2 (rewrite subst_in_mret_neq; auto).
  Qed.

  Theorem subst_subst_neq : forall k1 k2 u1 u2 t (x1 x2 : atom),
      k1 <> k2 ->
      ~ x1 ∈ free (T k2) k1 u2 ->
      t '{k1 | x1 ~> u1} '{k2 | x2 ~> u2} =
      t '{k2 | x2 ~> u2} '{k1 | x1 ~> u1 '{k2 | x2 ~> u2} }.
  Proof.
    intros. unfold subst.
    compose near t on left.
    compose near t on right.
    unfold bindk. rewrite 2(rmod_mbind_mbind F T).
    fequal. ext j. now apply subst_subst_neq_loc.
  Qed.

  Lemma subst_subst_eq_local : forall k (u1 u2 : T k leaf) x1 x2,
      ~ x1 ∈ free (T k) k u2 ->
      x1 <> x2 ->
      subst (T k) k x2 u2 ∘ subst_loc x1 u1 =
      subst (T k) k x1 (subst (T k) k x2 u2 u1) ∘ subst_loc x2 u2.
  Proof with auto.
    intros. ext l. unfold compose. compare l to atom x1.
    - rewrite subst_loc_eq, subst_loc_neq,
      subst_in_mret_eq, subst_loc_eq...
    - rewrite subst_loc_neq...
      compare values x2 and a.
      + rewrite subst_in_mret_eq, subst_loc_eq, subst_fresh_t...
      + rewrite subst_loc_neq, 2(subst_in_mret_eq), 2(subst_loc_neq)...
    - rewrite 2(subst_loc_b), 2(subst_in_mret_eq), 2(subst_loc_b)...
  Qed.

  Theorem subst_subst_eq : forall k u1 u2 t (x1 x2 : atom),
      ~ x1 ∈ free (T k) k u2 ->
      x1 <> x2 ->
      t '{k | x1 ~> u1} '{k | x2 ~> u2} =
      t '{k | x2 ~> u2} '{k | x1 ~> u1 '{k | x2 ~> u2} }.
  Proof with auto.
    intros. unfold subst.
    compose near t.
    rewrite 2(bindk_bindk_eq F).
    fequal. now apply subst_subst_eq_local.
  Qed.

  (** ** Commuting two substitutions *)
  Corollary subst_subst_comm_eq : forall k u1 u2 t (x1 x2 : atom),
      x1 <> x2 ->
      ~ x1 ∈ free (T k) k u2 ->
      ~ x2 ∈ free (T k) k u1 ->
      t '{k | x1 ~> u1} '{k | x2 ~> u2} =
      t '{k | x2 ~> u2} '{k | x1 ~> u1}.
  Proof.
    intros. rewrite subst_subst_eq; auto.
    rewrite subst_fresh_t; auto.
  Qed.

  Corollary subst_subst_comm_neq : forall k1 k2 u1 u2 t (x1 x2 : atom),
      k1 <> k2 ->
      ~ x1 ∈ free (T k2) k1 u2 ->
      ~ x2 ∈ free (T k1) k2 u1 ->
      t '{k1 | x1 ~> u1} '{k2 | x2 ~> u2} =
      t '{k2 | x2 ~> u2} '{k1 | x1 ~> u1}.
  Proof.
    intros. rewrite subst_subst_neq; auto.
    rewrite subst_fresh_t; auto.
  Qed.

  (** ** Local closure is preserved by substitution *)
  Theorem subst_lc_eq : forall k u t x,
      locally_closed F k t ->
      locally_closed (T k) k u ->
      locally_closed F k (subst F k x u t).
  Proof.
    unfold locally_closed. introv lct lcu hin.
    rewrite ind_subst_iff_eq in hin.
    destruct hin as [[? ?] | [n1 [n2 [h1 [h2 h3]]]]].
    - auto.
    - subst. specialize (lcu n2 l h2).
      unfold is_bound_or_free in *.
      destruct l; auto. unfold_lia.
  Qed.

  Theorem subst_lc_neq : forall k j u t x,
      k <> j ->
      locally_closed F j t ->
      locally_closed (T k) j u ->
      locally_closed F j (subst F k x u t).
  Proof.
    unfold locally_closed. introv neq lct lcu hin.
    rewrite ind_subst_iff_neq in hin; auto.
    destruct hin as [? | [n1 [n2 [h1 [h2 h3]]]]].
    - auto.
    - subst. specialize (lcu n2 l h2).
      unfold is_bound_or_free in *.
      destruct l; auto. unfold_lia.
  Qed.

  (** ** Decompose substitution into closing/opening *)
  Lemma subst_spec_local : forall k (u : T k leaf) w l x,
      subst_loc x u l =
      open_loc u (cobind (prod (Row nat)) (close_loc k x) (w, l)).
  Proof.
    introv. compare l to atom x; autorewrite* with tea_local.
    - cbn. compare values x and x. unfold id.
      compare naturals (w k) and (w k).
    - cbn. compare values x and a. (* todo fix fragile names *)
    - cbn. unfold id. compare naturals n and (w k).
      now compare naturals (S (w k)) and (w k).
      now compare naturals (S n) and (w k).
  Qed.

  Theorem subst_spec : forall k x u t,
      t '{k | x ~> u} = ('[k | x] t) '(k | u).
  Proof.
    intros. compose near t on right.
    unfold open, close, subst.
    rewrite (bindkr_fmapkr F).
    symmetry. apply (bindkr_proper_bindk F k t).
    symmetry. apply subst_spec_local.
  Qed.

  (** ** Substitution when <<u>> is a leaf **)
  Definition subst_loc_leaf k x (u : leaf) : leaf -> leaf :=
    fun l => match l with
          | Fr y => if x == y then u else Fr y
          | Bd n => Bd n
          end.

  Theorem subst_by_leaf_spec : forall k x l,
      subst F k x (mret T k l) = fmapk F k (subst_loc_leaf k x l).
  Proof.
    intros. unfold subst. ext t.
    apply (tomset_bindk_proper_fmapk F).
    intros l' l'in. destruct l'.
    - cbn. compare values x and a.
    - reflexivity.
  Qed.

  (** ** Substitution by the same variable is the identity *)
  (** TODO : Intuitively this theorem should be stronger, but
      this is because we don't have strong properness for [bind] in general. *)
  Theorem subst_same : forall t k x,
      t '{k | x ~> mret T k (Fr x)} = t.
  Proof.
    intros. apply subst_id.
    intros. compare l to atom x; now simpl_local.
  Qed.

  (** ** Free variables after variable closing *)
  Lemma in_free_close_iff_loc_1 : forall k w l t x  y,
      (k, w, l) ∈md t ->
      close_loc k x (w, l) = Fr y ->
      (k, Fr y) ∈m t /\ x <> y.
  Proof.
    introv lin heq. destruct l as [la | ln].
    - cbn in heq. destruct_eq_args x la.
      inverts heq. now apply (in_of_ind F) in lin.
    - cbn in heq. compare_nats_args ln (w k); discriminate.
  Qed.

  Lemma in_free_close_iff_loc_2 : forall t k x y,
      x <> y ->
      (k, Fr y) ∈m t ->
      exists w l, (k, w, l) ∈md t /\ close_loc k x (w, l) = Fr y.
  Proof.
    introv neq yin. rewrite (ind_of_in F) in yin. destruct yin as [w yin].
    exists w. exists (Fr y). cbn. compare values x and y.
  Qed.

  Theorem in_free_close_iff : forall k t x y,
      y ∈ free F k ('[k | x] t) <-> y ∈ free F k t /\ x <> y.
  Proof.
    introv. rewrite (free_close_iff_eq).
    rewrite (in_free_iff). split.
    - introv [? [? [? ?] ] ]. eauto using in_free_close_iff_loc_1.
    - intros [? ?]. eauto using in_free_close_iff_loc_2.
  Qed.

  Corollary in_free_close_iff_1 : forall k t x y,
      y <> x ->
      y ∈ free F k ('[k | x] t) <-> y ∈ free F k t.
  Proof.
    intros. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary freeset_close : forall k t x,
      freeset F k ('[k | x] t) [=] freeset F k t \\ {{ x }}.
  Proof.
    introv. intro a. rewrite AtomSet.diff_spec.
    rewrite <- 2(free_iff_freeset). rewrite in_free_close_iff.
    fsetdec.
  Qed.

  Corollary nin_free_close : forall k t x,
      ~ (x ∈ free F k ('[k | x] t)).
  Proof.
    introv. rewrite in_free_close_iff. intuition.
  Qed.

  Corollary nin_freeset_close : forall k t x,
      ~ (x ∈@ freeset F k ('[k | x] t)).
  Proof.
    introv. rewrite <- free_iff_freeset. apply nin_free_close.
  Qed.

  (** ** Variable closing and local closure *)
  Theorem close_lc_eq : forall k t x,
      locally_closed F k t ->
      locally_closed_gap F k 1 (close F k x t).
  Proof.
    unfold locally_closed. introv lct hin.
    rewrite ind_close_iff_eq in hin.
    destruct hin as [l1 [? ?]]. compare l1 to atom x; subst.
    - cbn. compare values x and x. unfold_lia.
    - cbn. compare values x and a.
    - cbn. compare naturals n and (w k).
      + unfold_lia.
      + (* contradiction *)
        specialize (lct w (Bd (w k)) ltac:(assumption)).
        cbn in lct. now unfold_lia.
      + specialize (lct w (Bd n) ltac:(assumption)).
        cbn in lct. now unfold_lia.
  Qed.

  Theorem close_lc_neq : forall k j t x,
      k <> j ->
      locally_closed F j t ->
      locally_closed F j (close F k x t).
  Proof.
    unfold locally_closed. introv neq lct hin.
    rewrite ind_close_iff_neq in hin; auto.
  Qed.

  Import Monoid.Notations.

  (** ** Upper and lower bounds on free variables after opening *)
  Lemma free_open_upper_local : forall t k j (u : T k leaf) w l x,
      (k, l) ∈m t ->
      x ∈ free (T k) j (open_loc u (w, l)) ->
        k = j /\ l = Fr x /\ x ∈ free F j t \/
        x ∈ free (T k) j u.
    Proof with auto.
      introv lin xin. rewrite in_free_iff_T in xin.
      rewrite 2(in_free_iff). destruct l as [y | n].
      - left. autorewrite with tea_local in xin. inverts xin...
      - right. cbn in xin. compare naturals n and (w k).
      { contradict xin. simpl_local. intuition. }
      { assumption. }
      { contradict xin. simpl_local. intuition. }
  Qed.

  Corollary free_open_upper_local_eq : forall t k (u : T k leaf) w l x,
      (k, l) ∈m t ->
      x ∈ free (T k) k (open_loc u (w, l)) ->
      x ∈ free F k t \/ x ∈ free (T k) k u.
  Proof.
    introv lin xin.
    apply free_open_upper_local
      with (t:=t) in xin; auto.
    intuition.
  Qed.

  Corollary free_open_upper_local_neq : forall t k j (u : T k leaf) w l x,
      k <> j ->
      (k, l) ∈m t ->
      x ∈ free (T k) j (open_loc u (w, l)) ->
      x ∈ free (T k) j u.
  Proof.
    introv neq lin xin.
    apply free_open_upper_local
      with (t:=t) in xin; auto.
    intuition.
  Qed.

  Theorem free_open_upper : forall t k j (u : T k leaf) x,
      x ∈ free F j (t '(k | u)) ->
      x ∈ free F j t \/ x ∈ free (T k) j u.
  Proof.
    introv xin. compare values j and k.
    - rewrite free_open_iff_eq in xin.
      destruct xin as [l [w [hin ?]]].
      apply (in_of_ind F) in hin.
      eauto using free_open_upper_local_eq.
    - rewrite free_open_iff_neq in xin; auto.
      destruct xin as  [? |  [l [w [hin ?]]]].
      auto. apply (in_of_ind F) in hin.
      right. eauto using free_open_upper_local_neq.
  Qed.

  Corollary freeset_open_upper : forall t k j (u : T k leaf),
      freeset F j (t '(k | u)) ⊆ freeset F j t ∪ freeset (T k) j u.
  Proof.
    intros. intro a. rewrite AtomSet.union_spec.
    repeat rewrite <- (free_iff_freeset).
    auto using free_open_upper.
  Qed.

  Corollary free_open_upper_eq : forall t k (u : T k leaf) x,
      x ∈ free F k (t '(k | u)) ->
      x ∈ free F k t \/ x ∈ free (T k) k u.
  Proof.
    intros. auto using free_open_upper.
  Qed.

  Corollary freeset_open_upper_eq : forall t k (u : T k leaf),
      freeset F k (t '(k | u)) ⊆ freeset F k t ∪ freeset (T k) k u.
  Proof.
    intros. apply freeset_open_upper.
  Qed.

  Theorem free_open_lower : forall t k j u x,
      x ∈ free F j t ->
      x ∈ free F j (t '(k | u)).
  Proof.
    introv xin. compare values j and k.
    - rewrite (in_free_iff) in xin.
      rewrite (ind_of_in F) in xin.
      destruct xin as [w xin].
      rewrite (free_open_iff_eq k).
      setoid_rewrite (in_free_iff).
      exists (Fr x) w. now autorewrite with tea_local.
    - rewrite (free_open_iff_neq k); auto.
  Qed.

  Theorem free_open_lower_eq : forall t k u x,
      x ∈ free F k t ->
      x ∈ free F k (t '(k | u)).
  Proof.
    intros. auto using free_open_lower.
  Qed.

  Corollary freeset_open_lower : forall t k j u,
      freeset F j t ⊆ freeset F j (t '(k | u)).
  Proof.
    intros. intro a. rewrite <- 2(free_iff_freeset).
    apply free_open_lower.
  Qed.

  Corollary freeset_open_lower_eq : forall t k u,
      freeset F k t ⊆ freeset F k (t '(k | u)).
  Proof.
    intros. apply freeset_open_lower.
  Qed.

  (** ** Opening a locally closed term is the identity *)
  (**************************************************************************)
  Lemma open_lc_local : forall k (u : T k leaf) w l,
      is_bound_or_free k 0 (w, l) ->
      open_loc u (w, l) = mret T k l.
  Proof.
    introv hyp. destruct l as [a | n].
    - reflexivity.
    - cbn in *. compare naturals n and (w k); unfold_lia.
  Qed.

  Lemma open_lc : forall k t u,
      locally_closed F k t ->
      t '(k | u) = t.
  Proof.
    introv lc. apply open_id. introv lin.
    specialize (lc _ _ lin).
    destruct l; auto using open_lc_local.
  Qed.

  (** ** Opening followed by substitution *)
  (**************************************************************************)
  Open Scope nat_scope.

  Lemma subst_open_eq_loc : forall k u1 u2 x,
      locally_closed (T k) k u2 ->
      subst (T k) k x u2 ∘ open_loc u1 =
      open_loc (u1 '{k | x ~> u2}) ∗kr (subst_loc x u2 ∘ snd).
  Proof.
    introv lcu2. ext [w l]. rewrite kcompkr_spec.
    unfold compose. compare l to atom x.
    - cbn. simpl_local. compare values x and x.
      symmetry. apply (bindkr_proper_id (T k)). intros ? [?|?] hin.
      + trivial.
      + specialize (lcu2 _ _ hin). cbn in lcu2. cbn. unfold_monoid.
        compare naturals n and (w k + w0 k).
    - cbn. simpl_local. compare values x and a.
      now rewrite (bindkr_comp_mret_eq (T k) k).
      (* <<< TODO standardize this lemma *)
    - cbn. rewrite (bindkr_comp_mret_eq (T k) k).
      compare naturals n and (w k); simpl_local.
      + rewrite monoid_id_l. cbn. compare naturals n and (w k).
      + rewrite monoid_id_l. cbn. compare naturals (w k) and (w k).
      + rewrite monoid_id_l. cbn. compare naturals n and (w k).
  Qed.

  Theorem subst_open_eq :  forall k u1 u2 t x,
      locally_closed (T k) k u2 ->
      t '(k | u1) '{k | x ~> u2} =
      t '{k | x ~> u2} '(k | u1 '{k | x ~> u2}).
  Proof.
    introv lc. compose near t.
    unfold open, subst at 1 3.
    rewrite (bindk_bindkr F), (bindkr_bindk F).
    fequal. apply subst_open_eq_loc; auto.
  Qed.

  (*
  Theorem subst_open_neq :  forall j k u1 u2 t x,
      k <> j ->
      locally_closed k u2 ->
      t '(k | u1) '{j | x ~> u2} =
      t '{j | x ~> u2} '(k | u1 '{j | x ~> u2}).
  Proof.
    introv neq lc. compose near t.
    unfold open, subst at 1 3.
    rewrite (bindk_bindkr F). (bindkr_bindk F).
    fequal. apply subst_open_loc; auto.
  Qed.
   *)

  Lemma subst_open_neq_loc k1 k2 (u1 : T k1 leaf) (u2 : T k2 leaf) (x : atom) :
    k1 <> k2 ->
    locally_closed (T k2) k1 u2 ->
    btg k2 (subst_loc x u2) ∗m btgr T k1 (open_loc u1) =
    btgr T k1 (open_loc (mbind (T k1) (↑ k2 (subst_loc x u2)) u1)) ∗mr
          (fun k : K => btg k2 (subst_loc x u2) k ∘ snd).
  Proof.
    introv neq lcu2. ext j [w l]. compare j to both of { k1 k2 }.
    - (* j = k1, j <> k2 *)
      rewrite mkcompr_spec.
      unfold mkcomp, compose, snd. simpl_tgt.
      compose near l on right. rewrite (mbindr_comp_mret (T k1)).
      unfold compose. rewrite (monoid_id_l).
      simpl_tgt. destruct l. (** TODO Simplify this part *)
      + cbn. compose near (Fr a) on left.
        rewrite (mmon_mbind_comp_mret T).
        now simpl_tgt.
      + cbn. compare naturals n and (w k1).
        { compose near (Bd n) on left.
          rewrite (mmon_mbind_comp_mret T).
          now simpl_tgt. }
        { compose near (Bd (n - 1)) on left.
          rewrite (mmon_mbind_comp_mret T).
          now simpl_tgt. }
    - (* j <> k1, j = k2 *)
      unfold mkcomp, mkcompr, compose, snd.
      simpl_tgt. unfold compose, snd.
      compose near l on left. rewrite (mmon_mbind_comp_mret T).
      simpl_tgt. compare l to atom x.
      + cbn. compare values x and x. admit.
      + cbn. compare values x and a. compose near (Fr a) on right.
        admit.
      + cbn. admit.
    - unfold mkcomp, compose, snd. rewrite mkcompr_spec.
      simpl_tgt. unfold compose, snd. compose near l.
      rewrite (mmon_mbind_comp_mret T).
      rewrite (mbindr_comp_mret (T j)).
      simpl_tgt. reflexivity.
  Admitted.

  Theorem subst_open_neq :  forall k1 k2 (u1 : T k1 leaf) (u2 : T k2 leaf) (x : atom) (t : F leaf),
      k1 <> k2 ->
      locally_closed (T k2) k1 u2 ->
      t '(k1 | u1) '{k2 | x ~> u2} =
      t '{k2 | x ~> u2} '(k1 | u1 '{k2 | x ~> u2}).
  Proof.
    introv neq lc.
    compose near t. unfold subst, open.
    unfold bindk, bindkr.
    rewrite (mbind_mbindr F), (mbindr_mbind F).
    fequal. now rewrite subst_open_neq_loc.
  Qed.

  (** ** Decompose opening into variable opening followed by substitution *)
  (**************************************************************************)
  Lemma open_spec_eq_loc : forall k u x w l,
      l <> Fr x ->
      (subst (T k) k x u ∘ open_loc (mret T k (Fr x))) (w, l) =
      open_loc u (w, l).
  Proof.
    introv neq. unfold compose. compare l to atom x.
    - contradiction.
    - cbn. rewrite subst_in_mret_eq, subst_loc_fr_neq.
      trivial. intuition.
    - cbn. compare naturals n and (w k).
      now rewrite subst_in_mret_eq.
      now rewrite subst_in_mret_eq, subst_loc_eq.
      now rewrite subst_in_mret_eq, subst_loc_b.
  Qed.

  (* This theorem would be easy to prove with [subst_open_eq], but
   applying that theorem would introduce a local closure hypothesis
   for <<u>> that is not actually required for our purposes. *)
  Theorem open_spec_eq : forall k u t x,
      ~ x ∈@ freeset F k t ->
      t '(k | u) = t '(k | mret T k (Fr x)) '{k | x ~> u}.
  Proof.
    introv fresh. compose near t on right.
    unfold subst, open. rewrite (bindk_bindkr F).
    apply (bindkr_proper F). intros.
    assert (a <> Fr x).
    { apply (in_of_ind F) in H5.
      rewrite <- free_iff_freeset in fresh.
      eapply ninf_in_neq in fresh; eauto. }
    now rewrite <- (open_spec_eq_loc k u x).
  Qed.

  (** ** Opening by a variable, followed by non-equal substitution *)
  (**************************************************************************)
  Lemma subst_open_var_loc : forall k u x y,
      x <> y ->
      locally_closed (T k) k u ->
      subst (T k) k x u ∘ open_loc (mret T k (Fr y)) =
      open_loc (mret T k (Fr y)) ∗kr (subst_loc x u ∘ snd).
  Proof with auto.
    introv neq lc. rewrite subst_open_eq_loc...
    simpl_local. reflexivity.
  Qed.

  Theorem subst_open_var : forall k u t x y,
      x <> y ->
      locally_closed (T k) k u ->
      t '(k | mret T k (Fr y)) '{k | x ~> u} =
      t '{k | x ~> u} '(k | mret T k (Fr y)).
  Proof.
    introv neq lc. compose near t.
    unfold open, subst.
    rewrite (bindk_bindkr F), (bindkr_bindk F).
    fequal. apply subst_open_var_loc; auto.
  Qed.

  (** ** Closing, followed by opening *)
  (**************************************************************************)
  Lemma open_close_loc : forall k x w l,
      (open_loc (mret T k (Fr x)) ∘ cobind (prod (Row nat))
                (close_loc k x)) (w, l) = mret T k l.
  Proof.
    intros. cbn. unfold id. compare l to atom x.
    - compare values x and x. compare naturals (w k) and (w k).
    - compare values x and a.
    - compare naturals n and (w k).
      compare naturals (S (w k)) and (w k).
      compare naturals (S n) and (w k).
  Qed.

  Theorem open_close : forall k x t,
      ('[k | x] t) '(k | mret T k (Fr x)) = t.
  Proof.
    intros. compose near t on left.
    unfold open, close.
    rewrite (bindkr_fmapkr F).
    apply (bindkr_proper_id F); intros.
    auto using open_close_loc.
  Qed.

  (** ** Opening by a leaf reduces to an [fmapkr] *)
  Definition open_leaf_loc k (u : leaf) : Row nat * leaf -> leaf :=
    fun wl => match wl with
           | (w, l) =>
             match l with
             | Fr x => Fr x
             | Bd n =>
               match Nat.compare n (w k) with
               | Gt => Bd (n - 1)
               | Eq => u
               | Lt => Bd n
               end
             end
           end.

  Lemma open_by_leaf_spec : forall k l,
      open F k (mret T k l) = fmapkr F k (open_leaf_loc k l).
  Proof.
    intros. unfold open. ext t.
    apply (bindkr_proper_fmapkr F).
    intros w l' l'in. destruct l'.
    - reflexivity.
    - cbn. compare naturals n and (w k).
  Qed.

  (** ** Opening, followed by closing *)
  (**************************************************************************)
  Lemma close_open_local : forall k x w l,
      l <> Fr x ->
      (close_loc k x ∘ cobind (prod (Row nat))
                 (open_leaf_loc k (Fr x))) (w, l) = l.
  Proof.
    introv neq. cbn. unfold id. compare l to atom x.
    - contradiction.
    - unfold compose; cbn. now compare values x and a.
    - unfold compose; cbn.
      compare naturals n and (w k). compare values x and x.
      compare naturals (n - 1) and (w k).
  Qed.

  Theorem close_open : forall k x t,
      ~ x ∈ free F k t ->
      '[k | x] (t '(k | mret T k (Fr x))) = t.
  Proof.
    introv fresh. compose near t on left.
    rewrite open_by_leaf_spec. unfold close.
    rewrite (fmapkr_fmapkr_eq F k).
    apply (fmapkr_proper_id F).
    intros w l lin.
    assert (l <> Fr x).
    { rewrite neq_symmetry. apply (in_of_ind F) in lin.
      eauto using ninf_in_neq. }
    auto using close_open_local.
  Qed.

  (** ** Opening and local closure *)
  (**************************************************************************)
  Lemma open_lc_gap_eq_1 : forall k n t u,
      locally_closed (T k) k u ->
      locally_closed_gap F k n t ->
      locally_closed_gap F k (n - 1) (t '(k | u)).
  Proof.
    unfold locally_closed_gap.
    introv lcu lct Hin. rewrite ind_open_iff_eq in Hin.
    destruct Hin as [l1 [n1 [n2 [h1 [h2 h3]]]]].
    destruct l1.
    - cbn in h2. rewrite ind_mret_iff_eq in h2.
      destruct h2; subst. cbn. trivial.
    - specialize (lct _ _ h1). cbn in h2. compare naturals n0 and (n1 k).
      + rewrite ind_mret_iff_eq in h2; destruct h2; subst.
        cbn. unfold_monoid. lia.
      + specialize (lcu n2 l h2). unfold is_bound_or_free in *.
        destruct l; [trivial|]. unfold_monoid. lia.
      + rewrite ind_mret_iff_eq in h2. destruct h2; subst.
        unfold is_bound_or_free in *. unfold_lia.
  Qed.

  Lemma open_lc_gap_eq_2 : forall k n t u,
      n > 0 ->
      locally_closed (T k) k u ->
      locally_closed_gap F k (n - 1) (t '(k | u)) ->
      locally_closed_gap F k n t.
  Proof.
    unfold locally_closed_gap.
    introv ngt lcu lct Hin. setoid_rewrite ind_open_iff_eq in lct.
    destruct l.
    - cbv. trivial.
    - compare naturals n0 and (w k).
      + specialize (lct w (Bd n0)).
        lapply lct.
        { cbn; unfold_lia. }
        { exists (Bd n0) w (Ƶ : Row nat).
          split; auto. cbn. compare naturals n0 and (w k).
          rewrite ind_mret_iff_eq. now simpl_monoid. }
      + cbn. unfold_lia.
      + cbn. specialize (lct w (Bd (n0 - 1))).
        lapply lct.
        { cbn; unfold_lia. }
        { exists (Bd n0) w (Ƶ : Row nat).
          split; auto. cbn. compare naturals n0 and (w k).
          rewrite ind_mret_iff_eq. now simpl_monoid. }
  Qed.

  Theorem open_lc_gap_eq_iff : forall k n t u,
      n > 0 ->
      locally_closed (T k) k u ->
      locally_closed_gap F k n t <->
      locally_closed_gap F k (n - 1) (t '(k | u)).
  Proof.
    intros; intuition (eauto using open_lc_gap_eq_1, open_lc_gap_eq_2).
  Qed.

  Corollary open_lc_gap_eq_var : forall k n t x,
      n > 0 ->
      locally_closed_gap F k n t <->
      locally_closed_gap F k (n - 1) (t '(k | mret T k (Fr x))).
  Proof.
    intros. apply open_lc_gap_eq_iff. auto.
    intros w l hin. rewrite ind_mret_iff_eq in hin.
    destruct hin; subst. cbv. trivial.
  Qed.

  Corollary open_lc_gap_eq_iff_1 : forall k t u,
      locally_closed (T k) k u ->
      locally_closed_gap F k 1 t <->
      locally_closed F k (t '(k | u)).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_iff; auto.
    reflexivity.
  Qed.

  Corollary open_lc_gap_eq_var_1 : forall k t x,
      locally_closed_gap F k 1 t <->
      locally_closed F k (t '(k | mret T k (Fr x))).
  Proof.
    intros. unfold locally_closed.
    change 0 with (1 - 1).
    rewrite <- open_lc_gap_eq_var; auto.
    reflexivity.
  Qed.

  Lemma open_lc_gap_neq_1 : forall k j n t u,
      k <> j ->
      locally_closed (T j) k u ->
      locally_closed_gap F k n t ->
      locally_closed_gap F k n (t '(j | u)).
  Proof.
    unfold locally_closed_gap.
    introv neq lcu lct Hin.
    rewrite ind_open_iff_neq in Hin; auto.
    destruct Hin.
    - auto.
    - destruct H5 as [l' [n1 [n2 [in_t [in_open ?]]]]].
      subst. destruct l'.
      + cbn in in_open. rewrite ind_mret_iff in in_open.
        false. intuition.
      + destruct l.
        { cbn. trivial. }
        { cbn. cbn in in_open.
          compare naturals n0 and (n1 j).
          - rewrite ind_mret_iff in in_open. false; intuition.
          - specialize (lcu _ _ in_open).
            unfold is_bound_or_free in lcu. unfold_lia.
          - rewrite ind_mret_iff in in_open. false; intuition.
        }
  Qed.

  Lemma open_lc_gap_neq_2 : forall k j n t u,
      k <> j ->
      locally_closed (T j) k u ->
      locally_closed_gap F k n (t '(j | u)) ->
      locally_closed_gap F k n t.
  Proof.
    unfold locally_closed_gap.
    introv neq lcu lct Hin.
    destruct l.
    + cbn. auto.
    + specialize (lct w (Bd n0)).
      apply lct. rewrite ind_open_iff_neq; auto.
  Qed.

  Theorem open_lc_gap_neq_iff : forall k j n t u,
      k <> j ->
      locally_closed (T j) k u ->
      locally_closed_gap F k n t <->
      locally_closed_gap F k n (t '(j | u)).
  Proof.
    intros. intuition (eauto using open_lc_gap_neq_1, open_lc_gap_neq_2).
  Qed.

  Corollary open_lc_gap_neq_var : forall k j t x,
      k <> j ->
      locally_closed F k t <->
      locally_closed F k (t '(j | mret T j (Fr x))).
  Proof.
    intros. unfold locally_closed.
    rewrite open_lc_gap_neq_iff; eauto.
    reflexivity. unfold locally_closed, locally_closed_gap.
    setoid_rewrite ind_mret_iff. intuition.
  Qed.

End locally_nameless_metatheory.
