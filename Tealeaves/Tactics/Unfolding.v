(*|
##########
Unfold.v
##########

|*)

(** * Support for unfolding specific operations *)
(******************************************************************************)
From Tealeaves.Tactics Require Export
  LibTactics.

Ltac head_of expr :=
  match expr with
  | ?f ?x => head_of f
  | ?head => head
  | _ => fail
  end.

Ltac head_of_matches expr head :=
  match expr with
  | ?f ?x =>
    head_of_matches f head
  | head => idtac
  | _ => fail
  end.

Goal False.
  Fail head_of_matches 0 S. (* Tactic failure. *)
  head_of_matches (S 0) S. (* Success *)
  head_of_matches 5 S. (* Success *)
Abort.

(** ** Unfolding operational typeclasses *)
(******************************************************************************)
(** Unfold operational typeclasses in the goal *)
Ltac unfold_operational_tc inst :=
  repeat (match goal with
          | |- context[?op ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op maybe_inst) with maybe_inst
          | |- context[?op ?F ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F maybe_inst) with maybe_inst
          | |- context[?op ?F ?G ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G inst) with maybe_inst
          | |- context[?op ?F ?G ?H ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G H inst) with maybe_inst
          | |- context[?op ?F ?G ?H ?I ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G H I inst) with maybe_inst
          | |- context[?op ?F ?G ?H ?I ?J ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G H I J inst) with maybe_inst
          | |- context[?op ?F ?G ?H ?I ?J ?K ?maybe_inst] =>
            head_of_matches maybe_inst inst;
            change (op F G H I J K inst) with maybe_inst
          end); unfold inst.

(** Unfold operational typeclasses in hypotheses *)
Ltac unfold_operational_tc_hyp :=
  repeat (match goal with
          | H : context[?op ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op maybe_inst) with maybe_inst in H
          | H :context[?op ?F ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F maybe_inst) with maybe_inst
          | H :context[?op ?F ?G ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G inst) with maybe_inst
          | H :context[?op ?F ?G ?H ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G H inst) with maybe_inst
          | H :context[?op ?F ?G ?H ?I ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G H I inst) with maybe_inst
          | H :context[?op ?F ?G ?H ?I ?J ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G H I J inst) with maybe_inst
          | H :context[?op ?F ?G ?H ?I ?J ?K ?maybe_inst] |- _ =>
            head_of_matches maybe_inst inst;
            change (op F G H I J K inst) with maybe_inst
          end); unfold inst.

Tactic Notation "unfold_ops" constr(inst) :=
  unfold_operational_tc inst.

Tactic Notation "unfold_ops" constr(inst) constr(inst1) :=
  unfold_ops inst; unfold_ops inst1.

Tactic Notation "unfold_ops" constr(inst) constr(inst1) constr(inst2) :=
  unfold_ops inst; unfold_ops inst1 inst2.

Tactic Notation "unfold_ops" constr(inst) "in" "*" :=
  unfold_operational_tc inst;
    unfold_operational_tc_hyp inst.

Tactic Notation "unfold_ops" constr(inst) constr(inst1) "in" "*" :=
  unfold_ops inst in *; unfold_ops inst1 in *.

Tactic Notation "unfold_ops" constr(inst) constr(inst1) constr(inst2) "in" "*" :=
  unfold_ops inst in *; unfold_ops inst1 in *; unfold_ops inst2 in *.

(** ** Unfolding all operational typeclasses *)
(******************************************************************************)
Ltac unfold_all_transparent_tcs :=
  repeat (match goal with
          | |- context[?op ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op inst) with x
          | |- context[?op ?F ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F inst) with x
          | |- context[?op ?F ?G ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G inst) with x
          | |- context[?op ?F ?G ?H ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H inst) with x
          | |- context[?op ?F ?G ?H ?I ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I inst) with x
          | |- context[?op ?F ?G ?H ?I ?J ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I J inst) with x
          | |- context[?op ?F ?G ?H ?I ?J ?K ?inst] =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I J K inst) with x
          end); cbn beta zeta.

Ltac unfold_all_transparent_tcs_hyp :=
  repeat (match goal with
          | H :context[?op ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op inst) with x
          | H :context[?op ?F ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F inst) with x
          | H :context[?op ?F ?G ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G inst) with x
          | H :context[?op ?F ?G ?H ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H inst) with x
          | H :context[?op ?F ?G ?H ?I ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I inst) with x
          | H :context[?op ?F ?G ?H ?I ?J ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I J inst) with x
          | H :context[?op ?F ?G ?H ?I ?J ?K ?inst] |- _ =>
            let hd := get_head inst in
            let x := eval unfold hd at 1 in inst in
                change (op F G H I J K inst) with x
          end); cbn beta zeta.

Tactic Notation "unfold" "transparent" "tcs" :=
  unfold_all_transparent_tcs.

Tactic Notation "unfold" "transparent" "tcs" "in" "*" :=
  unfold_all_transparent_tcs; unfold_all_transparent_tcs_hyp.
