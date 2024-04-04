Definition DEBUG : bool := false.

Tactic Notation "debug" string(x) :=
  let debug := eval compute in DEBUG in
  (match debug with
  | true => idtac x
  | false => idtac
   | _ => idtac "debug pattern match failed with ";
         idtac x
   end).
