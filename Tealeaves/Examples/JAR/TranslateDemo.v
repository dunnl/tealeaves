From Tealeaves.Examples Require Import Lambda.Confluence.
From Tealeaves.Backends Require Import LN DB.
From Tealeaves.Backends.Adapters Require Import LNtoDB DBtoLN Roundtrips.LNDB.

Check toLN: key -> lam nat -> option (lam LN).
Check toDB: key -> lam LN  -> option (lam nat).

Definition x: atom := 0.
Definition y: atom := 1.
Definition z: atom := 2.
Definition a: atom := 3.
Definition b: atom := 4.

Example term1: lam LN := app (tvar (Bd 0)) (tvar (Fr x)).
Example term2: lam LN := abs (app (tvar (Bd 0)) (tvar (Fr x))).
Example term3: lam LN := abs (app (tvar (Fr z)) (tvar (Fr x))).
Example term4: lam LN := abs (app (abs (abs (app (tvar (Fr z)) (tvar (Fr x))))) (app (tvar (Fr y)) (tvar (Fr a)))).

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
