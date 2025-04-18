(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* WARNING WARNING WARNING WARNING *)
(* #[local] Unset Guard Checking disables termination checking and potentially makes the logic inconsistent. *)
(* #[local] Unset Guard Checking désactive la vérification de terminaison et peut rendre la logique inconsistante. *)
(* #[local] Unset Guard Checking deaktiviert die Terminierungsprüfung und kann die Logik inkonsistent machen. *)       (* #[local] Unset Guard Checking desactiva la comprobación de terminación y puede volver inconsistente la lógica. *)
(* #[local] Unset Guard Checking probationem terminationis abrogat et logicam fortasse inconsistetem reddit. *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)

#[local] Unset Guard Checking.

From Tealeaves Require Export
  Examples.LambdaNominal.Syntax.

Fixpoint remove (x: name) (l: list name) : list name :=
  match l with
  | nil => nil
  | cons y rest =>
      if x == y then remove x rest else cons y (remove x rest)
  end.

Fixpoint FV (t: term name name): list name :=
  match t with
  | tvar v => [ v ]
  | tap t1 t2 => FV t1 ++ FV t2
  | lam b t => remove b (FV t)
  end.

Fixpoint substAvoid
  (l: list name) (* l is the avoid set *)
  (x : name) (u : term name name)
  (t : term name name)
  {struct t}
  : term name name :=
  match t with
  | tvar y => if y == x then u else tvar y
  | tap t1 t2 =>
      tap (substAvoid l x u t1) (substAvoid l x u t2)
  | lam b t =>
      if b == x then lam b t
      else let z := (freshen l b: name) in
           lam z (substAvoid (l ++ [z]) x u (substAvoid (l ++ [z]) b (tvar z) t))
  end.

Definition subst_CORRECT (x : name) (u : term name name) (t : term name name) :=
  substAvoid ([x] ++ FV t ++ FV u) x u t.

Definition subst_INCORRECT (x : name) (u : term name name) (t : term name name) :=
  substAvoid (FV t ++ FV u) x u t.

Section demo.

  Notation "'x'" := 0.
  Notation "'y'" := 1.
  Notation "'z'" := 2.
  Notation "'v'" := 3.

  Example idfn := (λ v, `v).
  Example input := (λ x, λ x, `z · `x).
  Example output := subst_INCORRECT y idfn input.
  Example correct_output := (λ x, λ y, `z · `y).
  Example actual_output := (λ x, λ y, `z · (λ v, `v)).

  Goal output = actual_output.
    cbv.
    reflexivity.
  Qed.

  Example tryagain := subst_CORRECT y idfn input.
  Example tryagain_output := (λ x, λ v, `z · `v).

  Goal tryagain = tryagain_output.
    reflexivity.
  Qed.

Goal subst_INCORRECT y (λ v, `v) (λ x, λ x, `z · `x) = (λ x, λ y, `z · `y).
  Fail reflexivity.
Abort.

Goal subst_INCORRECT y (λ v, `v) (λ x, λ x, `z · `x) = (λ x, λ y, `z · (λ v, `v)).
  reflexivity.
Qed.

Goal subst_CORRECT y (λ v, `v) (λ x, λ x, `z · `x) = (λ x, λ v, `z · `v).
  reflexivity.
Qed.

End demo.


