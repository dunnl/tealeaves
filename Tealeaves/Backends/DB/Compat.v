Autosubst




(*
  (** The main automation tactics. *)
Require Import Autosubst_Basics Autosubst_MMap Autosubst_Classes.

(** Derived substitution lemmas. *)

Section LemmasForSubst.

Context {term : Type} {Ids_term : Ids term}
        {Rename_term : Rename term} {Subst_term : Subst term}
        {SubstLemmas_term : SubstLemmas term}.

Implicit Types (s t : term) (sigma tau theta : var -> term) (xi : var -> var).
*)

(* Local Variables: *)
(* coq-load-path: (("." "Autosubst")) *)
(* End: *)
