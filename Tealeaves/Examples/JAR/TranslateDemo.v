From Tealeaves.Examples Require Import Lambda.Confluence.
From Tealeaves.Backends Require Import LN DB.
From Tealeaves.Backends.Adapters Require Import LNtoDB DBtoLN Roundtrips.LNDB.

Import List.ListNotations.

Check LNtokey: lam LN -> key.
Check toLN: key -> lam nat -> option (lam LN).
Check toDB: key -> lam LN  -> option (lam nat).

Definition x: atom := 0.
Definition y: atom := 1.
Definition z: atom := 2.
Definition a: atom := 3.
Definition b: atom := 4.

Module de_bruijn.

  Example term1: lam nat := app (tvar 0) (tvar 1).
  Example term2: lam nat := abs (app (tvar 0) (tvar 1)).
  Example term3: lam nat := app (abs (app (tvar 1) (tvar 0))) (app (tvar 1) (tvar 0)).
  (* ^ example from paper *)

  Example k: key := [x ; y].

  Compute toLN k term1.
  Compute map (toDB k) (toLN k term1).

  Compute toLN k term2.
  Compute map (toDB k) (toLN k term2).

  Compute toLN k term3.
  Compute map (toDB k) (toLN k term3).

End de_bruijn.

Module locally_nameless.

  Example term1: lam LN := app (tvar (Bd 0)) (tvar (Fr x)).
  Example term2: lam LN := abs (app (tvar (Bd 0)) (tvar (Fr x))).
  Example term3: lam LN := abs (app (tvar (Fr z)) (tvar (Fr x))).
  Example term4: lam LN :=
    abs (app
           (abs (abs (app
                        (tvar (Fr z))
                        (tvar (Fr x)))))
           (app
              (tvar (Fr y))
              (tvar (Fr a)))).

  Import List.ListNotations.

  Example k: key := [b; z; a; y; x].

  Compute toDB k term1.
  Compute map (toLN k) (toDB k term1).

  Compute toDB k term2.
  Compute map (toLN k) (toDB k term2).

  Compute toDB k term3.
  Compute map (toLN k) (toDB k term3).

  Compute toDB k term4.
  Compute map (toLN k) (toDB k term4).

  Goal map (toLN k) (toDB k term4) = Some (Some term4).
    reflexivity.
  Qed.

End locally_nameless.
