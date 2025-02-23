(* Require the Autosubst library *)
From Autosubst Require Import Autosubst.


Inductive term: Type :=
| tvar (x: var)
| tapp (t1 t2: term)
| tabs (t: {bind term}).

Instance Ids_term: Ids term. Proof. derive. Defined.
Instance Rename_term: Rename term. Proof. derive. Defined.
Instance Subst_term: Subst term. Proof. derive. Defined.
Instance SubstLemmas_term: SubstLemmas term. derive. Qed.

Print SubstLemmas.

Instance substLemmas_term: SubstLemmas term.
Proof. apply SubstLemmas_Ind; intros; simpl; congruence. Qed.
