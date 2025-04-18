From Tealeaves Require Import
  Backends.Common.Names
  Backends.Nominal.Common.Hmap
  Backends.Nominal.FV
  Functors.List.

Import Monoid.Notations.
Import List.ListNotations.
Import ContainerFunctor.Notations.

(** * Freshen an Entire List *)
(********************************************************************)
(* First list is an avoid set. Second argument is a history/name pair. *)
Definition renb: list name -> list name * name -> name :=
  fun Γ '(history, a) =>
    freshen (Γ ++ history) a.

(* First list is an avoid set. Second argument is a context/name pair. *)
Definition renb_ctx: list name -> list name * name -> name :=
  fun Γ => hadapt (renb Γ).

(* First list is an avoid set. Second argument is a list to be freshened. *)
Definition renbList: list name -> list name -> list name :=
  fun Γ l => hmap (renb Γ) l.

Lemma renbList_spec: forall Γ,
    renbList Γ = mapd_list_prefix (renb_ctx Γ).
Proof.
  intros.
  unfold renb_ctx.
  rewrite hmap_spec.
  reflexivity.
Qed.

Goal forall Γ, renbList Γ [1; 2; 3] =
            [freshen (Γ ++ []) 1;
             freshen (Γ ++ [freshen Γ 1]) 2;
             freshen (Γ ++ [freshen Γ 1; freshen (Γ ++ [freshen Γ 1]) 2]) 3].
Proof.
  cbn.
  intros.
  rewrite List.app_nil_r.
  reflexivity.
Qed.

Lemma renb_preincr (Γ: list atom) (history: list atom):
  renb Γ ⦿ history =
    renb (Γ ++ history).
Proof.
  ext [w l].
  unfold preincr, incr, compose.
  cbn.
  unfold_ops @Monoid_op_list.
  rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma renbList_decomposition: forall Γ l1 x l2,
    renbList Γ (l1 ++ [x] ++ l2) =
      renbList Γ l1 ++
        [freshen (Γ ++ renbList Γ l1) x] ++
        renbList (Γ ++ renbList Γ l1 ++ [freshen (Γ ++ renbList Γ l1) x]) l2.
Proof.
  intros.
  unfold renbList.
  rewrite hmap_decompose.
  rewrite renb_preincr.
  reflexivity.
Qed.

(** ** Examples *)
(********************************************************************)
Example renblist_demo:
  forall Γ, renbList Γ [1; 2; 3] =
         [freshen Γ 1;
          freshen (Γ ++ [freshen Γ 1]) 2;
          freshen (Γ ++ [freshen Γ 1] ++ [freshen (Γ ++ [freshen Γ 1]) 2]) 3
         ].
Proof.
  intros. cbn.
  rewrite List.app_nil_r.
  reflexivity.
Qed.
Compute renbList [] [1; 2; 3; 5].
Compute renbList [5] [1; 2; 3; 5].
Compute renbList [5] [1; 2; 3; 5; 5].
Compute renbList [5] [5; 5; 5; 5; 5].
Compute renbList [3; 4; 8] [0; 1; 8; 2; 5].
Compute renbList [] [5; 5; 5; 5; 5].

(** * Local Definition of Assigning Unique Names to a [list] *)
(********************************************************************)
Section historyToName.

  Context {A: Type}. (* Can be anything *)

  (** ** <<historyToName>> *)
  (** Perform one local binder renaming on a locally nameless binder occurrence, given the history (the names assigned
    to binders higher in the tree) and the initial avoid set.  *)
  (********************************************************************)
  Definition historyToName
    (Γ: list name)
    (p: list name * A): name :=
    match p with
    | (history, _) => fresh (Γ ++ history)
    end.

  (** ** Rewriting Principles for <<historyToName>> *)
  (********************************************************************)
  Section historyToName_rw.

    Context (avoid: list name).

    Lemma historyToName_nil (u: A):
      historyToName avoid (@nil atom, u) = fresh avoid.
    Proof.
      cbn -[fresh].
      rewrite List.app_nil_r.
      reflexivity.
    Qed.

    Lemma historyToName_pair (history: list atom) (u: A):
      historyToName avoid (history, u) = fresh (avoid ++ history).
    Proof.
      reflexivity.
    Qed.

    Lemma historyToName_preincr (history: list atom):
      historyToName avoid ⦿ history =
        historyToName (avoid ++ history).
    Proof.
      ext [w l].
      unfold preincr, incr, compose.
      rewrite historyToName_pair.
      unfold historyToName.
      unfold_ops @Monoid_op_list.
      rewrite <- List.app_assoc.
      reflexivity.
    Qed.

  End historyToName_rw.

  (** ** Freshness for <<historyToName>> *)
  (********************************************************************)
  Lemma historyToName_fresh (Γ: list name): forall p,
      ~ (historyToName Γ p ∈ Γ).
  Proof.
    intros.
    unfold historyToName.
    destruct p.
    specialize (fresh_not_in (Γ ++ l)).
    intros hyp contra.
    apply hyp.
    rewrite element_of_list_app.
    now left.
  Qed.

End historyToName.

(** * Assign Unique Names to a [list] *)
(********************************************************************)
Section listToName.

  Context {A: Type}. (* Can be anything *)

  (** ** Assign Names to an Arbitrary [list] *)
  (********************************************************************)
  Definition assignNames (Γ: list name):
    list A -> list name :=
    hmap (historyToName Γ).

  (** *** Localized version *)
  (********************************************************************)
  Definition assignNames_loc: list name -> list A * A -> name :=
    fun Γ => hadapt (historyToName Γ).

  (** ** Basic Properties of <<assignNames>> *)
  (********************************************************************)
  Corollary length_assignNames (Γ: list name) (l: list A):
    length (assignNames Γ l) = length l.
  Proof.
    intros.
    unfold assignNames.
    rewrite length_hmap.
    reflexivity.
  Qed.

  Lemma assignNames_loc_spec (Γ: list name) (ctx: list A) (a: A):
    assignNames_loc Γ (ctx, a) =
      historyToName Γ (assignNames Γ ctx, a).
  Proof.
    reflexivity.
  Qed.

  Definition assignNames_spec (Γ: list name):
    assignNames Γ = mapd_list_prefix (assignNames_loc Γ).
  Proof.
    intros.
    unfold assignNames.
    unfold assignNames_loc.
    rewrite hmap_spec.
    reflexivity.
  Qed.

  Ltac fold_folds :=
    repeat change (hmap (historyToName ?Γ)) with
      (assignNames Γ) in *.

  (** ** Rewriting Principles for <<assignNames>> *)
  (********************************************************************)
  Section historyToName_rw.

    Context (Γ: list name).

    Lemma assignNames_nil:
      assignNames Γ nil = nil.
    Proof.
      reflexivity.
    Qed.

    Lemma assignNames_cons (u: A) (pre: list A):
      assignNames Γ (u :: pre) =
        fresh Γ :: assignNames (Γ ++ [fresh Γ]) pre.
    Proof.
      unfold assignNames.
      rewrite hmap_cons.
      fequal.
      - rewrite historyToName_nil.
        reflexivity.
      - rewrite historyToName_nil.
        fequal.
        ext [x y].
        unfold preincr, incr, compose.
        unfold_ops @Monoid_op_list.
        unfold historyToName.
        rewrite List.app_assoc.
        reflexivity.
    Qed.

    Lemma assignNames_preincr
      (history: list atom):
      hmap (historyToName Γ ⦿ history) =
        assignNames (Γ ++ history).
    Proof.
      ext l.
      generalize dependent Γ.
      generalize dependent history.
      induction l; intros.
      - cbn.
        reflexivity.
      - rewrite hmap_cons.
        unfold assignNames.
        rewrite hmap_cons.
        fequal.
        { unfold preincr, incr, compose.
          change (history ● []) with (history ++ []).
          rewrite List.app_nil_r.
          cbn.
          rewrite List.app_nil_r.
          reflexivity.
        }
        { rewrite preincr_preincr.
          rewrite IHl.
          unfold assignNames.
          rewrite IHl.
          change (?l1 ● ?l2) with (l1 ++ l2).
          unfold assignNames.
          rewrite historyToName_preincr.
          rewrite List.app_assoc.
          reflexivity.
        }
    Qed.

  End historyToName_rw.

  (** *** Distributing <<assignNames>> over a context *)
  (********************************************************************)
  (* Tailored for use when the list is a nominal binding context decomposition *)
  Section assignNames_decompose.

    Context (Γ: list name) {l1 l2: list A} {u: A}.

    Corollary assignNames_decompose:
      assignNames Γ (l1 ++ [u] ++ l2) =
        let init := assignNames Γ l1 in
        let mid := [historyToName Γ (init , u)] in
        let tail := assignNames (Γ ++ init ++ mid) l2
        in init ++ mid ++ tail.
    Proof.
      intros.
      unfold historyToName at 1.
      unfold assignNames.
      rewrite hmap_decompose.
      rewrite assignNames_preincr.
      reflexivity.
    Qed.

  End assignNames_decompose.

  (** ** Freshness for <<assignNames_loc>> and <<assignNames>> *)
  (********************************************************************)
  Lemma assignNames_fresh (Γ: list name): forall (prefix: list A),
    forall (a: name),
      a ∈ Γ ->
      ~ a ∈ (assignNames Γ prefix).
  Proof.
    introv Hin.
    unfold historyToName.
    enough (cut: forall (x: atom), x ∈ assignNames Γ prefix -> x <> a).
    { intro contra.
      specialize (cut a).
      apply cut; auto.
    }
    apply hmap_ind.
    intros u h Hnotin.
    specialize (historyToName_fresh Γ (h, u)).
    intro Hfresh.
    intro contra.
    subst. contradiction.
  Qed.

  Lemma assignNames_loc_fresh (Γ: list name) (prefix: list A) (u: A):
    ~ assignNames_loc Γ (prefix, u) ∈ Γ.
  Proof.
    intros.
    unfold assignNames_loc.
    intro contra.
    unfold hadapt in contra.
    specialize (historyToName_fresh Γ
                  (hmap (historyToName Γ) prefix, u)).
    intro Hyp.
    apply Hyp.
    assumption.
  Qed.

End listToName.
