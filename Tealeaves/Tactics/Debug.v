Definition DEBUG : bool := true.

Tactic Notation "ltac_trace" string(x) :=
  let debug := eval compute in DEBUG in
    (match debug with
     | true => idtac x
     | false => idtac
     | _ => idtac "debug pattern match failed with ";
           idtac x;
           fail
     end).

Ltac print_goal :=
  match goal with
  | |- ?g =>
      let debug := eval compute in DEBUG in
        (match debug with
         | true => idtac g
         | _ => idtac
         end)
  end.
