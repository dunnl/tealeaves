
(* ================================================================= *)
(** ** Introduction *)

(** [introv] is used to name only non-dependent hypothesis.
 - If [introv] is called on a goal of the form [forall x, H],
   it should introduce all the variables quantified with a
   [forall] at the head of the goal, but it does not introduce
   hypotheses that preceed an arrow constructor, like in [P -> Q].
 - If [introv] is called on a goal that is not of the form
   [forall x, H] nor [P -> Q], the tactic unfolds definitions
   until the goal takes the form [forall x, H] or [P -> Q].
   If unfolding definitions does not produces a goal of this form,
   then the tactic [introv] does nothing at all. *)

(* [introv_rec] introduces all visible variables.
   It does not try to unfold any definition. *)

Ltac introv_rec :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; introv_rec
  | |- _ => idtac
  end.

(* [introv_noarg] forces the goal to be a [forall] or an [->],
   and then calls [introv_rec] to introduces variables
   (possibly none, in which case [introv] is the same as [hnf]).
   If the goal is not a product, then it does not do anything. *)

Ltac introv_noarg :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => introv_rec
  | |- ?G => hnf;
     match goal with
     | |- ?P -> ?Q => idtac
     | |- forall _, _ => introv_rec
     end
  | |- _ => idtac
  end.

  (* simpler yet perhaps less efficient imlementation *)
  Ltac introv_noarg_not_optimized :=
    intro; match goal with H:_|-_ => revert H end; introv_rec.

(* [introv_arg H] introduces one non-dependent hypothesis
   under the name [H], after introducing the variables
   quantified with a [forall] that preceeds this hypothesis.
   This tactic fails if there does not exist a hypothesis
   to be introduced. *)
(* Note: __ in introv means "intros" *)

Ltac introv_arg H :=
  hnf; match goal with
  | |- ?P -> ?Q => intros H
  | |- forall _, _ => intro; introv_arg H
  end.

(* [introv I1 .. IN] iterates [introv Ik] *)

Tactic Notation "introv" :=
  introv_noarg.
Tactic Notation "introv" simple_intropattern(I1) :=
  introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
  introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.

(** [intros_all] repeats [intro] as long as possible. Contrary to [intros],
    it unfolds any definition on the way. Remark that it also unfolds the
    definition of negation, so applying [intros_all] to a goal of the form
    [forall x, P x -> ~Q] will introduce [x] and [P x] and [Q], and will
    leave [False] in the goal. *)

Tactic Notation "intros_all" :=
  repeat intro.

(** [intros_hnf] introduces an hypothesis and sets in head normal form *)

Tactic Notation "intro_hnf" :=
  intro; match goal with H: _ |- _ => hnf in H end.

(* ================================================================= *)
(** ** Proving Equalities *)

(** The tactic [fequal] enhances Coq's tactic [f_equal], which does not
    simplify equalities between tuples, nor between dependent pairs of
    the form [exist _ _] or [existT _ _]. For support of dependent pairs,
    the file [LibEqual] must be imported.

    Subgoals solvable by [reflexivity] are automatically discharged.
    See also the the variant [fequals], which discharges more subgoals. *)

(** Note: only [args_eq_2] is actually useful for the implementation of
    [fequal], if we rely on Coq's [f_equal] tactic for other arities.
    We provide these lemmas to show the pattern of lemmas to exploit
    for implementing [fequal] independently of [f_equal]. *)

Section FuncEq.
Variables (A1 A2 A3 A4 A5 A6 A7 B : Type).

Lemma args_eq_1 : forall (f:A1->B) x1 y1,
  x1 = y1 ->
  f x1 = f y1.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_2 : forall (f:A1->A2->B) x1 y1 x2 y2,
  x1 = y1 -> x2 = y2 ->
  f x1 x2 = f y1 y2.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_3 : forall (f:A1->A2->A3->B) x1 y1 x2 y2 x3 y3,
  x1 = y1 -> x2 = y2 -> x3 = y3 ->
  f x1 x2 x3 = f y1 y2 y3.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_4 : forall (f:A1->A2->A3->A4->B) x1 y1 x2 y2 x3 y3 x4 y4,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 ->
  f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_5 : forall (f:A1->A2->A3->A4->A5->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 ->
  f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_6 : forall (f:A1->A2->A3->A4->A5->A6->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 ->
  f x1 x2 x3 x4 x5 x6 = f y1 y2 y3 y4 y5 y6.
Proof using. intros. subst. auto. Qed.

Lemma args_eq_7 : forall (f:A1->A2->A3->A4->A5->A6->A7->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 ->
  f x1 x2 x3 x4 x5 x6 x7 = f y1 y2 y3 y4 y5 y6 y7.
Proof using. intros. subst. auto. Qed.

End FuncEq.

Ltac fequal_post :=
  try solve [ reflexivity ].

(** [fequal_support_for_exist], implemented in [LibEqual], is meant
   to simplify goals of the form [exist _ _ = exist _ _ ] and
   [existT _ _ = existT _ _], by exploiting proof irrelevance. *)

Ltac fequal_support_for_exist tt :=
  fail.

(** For a n-ary tuple, [fequal], unlike [f_equal] enforces a recursive call
    on the (n-1)-ary tuple associated with the right component. *)

Ltac fequal_base :=
  match goal with
  | |- (_,_,_) = (_,_,_) =>  apply args_eq_2; [ fequal_base | ]
  | |- _ => first
            [ fequal_support_for_exist tt
            | apply args_eq_1
            | apply args_eq_2
            | apply args_eq_3
            | apply args_eq_4
            | apply args_eq_5
            | apply args_eq_6
            | apply args_eq_7
            | f_equal (* fallback to Coq [f_equal] *) ]
  end.

Tactic Notation "fequal" :=
  fequal_base; fequal_post.

(** [fequals] is the same as [fequal] except that it tries and solve
    all trivial subgoals, using [reflexivity] and [congruence]
    (as well as the proof-irrelevance principle).
    [fequals] applies to goals of the form [f x1 .. xN = f y1 .. yN]
    and produces some subgoals of the form [xi = yi]). *)

Ltac fequals_post :=
  try solve [ reflexivity | congruence].

Tactic Notation "fequals" :=
  fequal; fequals_post.

(** [fequals_rec] calls [fequals] recursively.
    It is equivalent to [repeat (progress fequals)]. *)

Tactic Notation "fequals_rec" :=
  repeat (progress fequals).


Ltac get_head E :=
  match E with
  | ?E' ?x => get_head E'
  | _ => constr:(E)
  end.
