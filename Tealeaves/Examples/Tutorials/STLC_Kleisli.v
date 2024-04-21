
(*|
========================================
Simplification automation
========================================
|*)

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Helper lemmas for proving the DTM laws
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|*)

Section rw.

  Context
    {G : Type -> Type} `{Map G} `{Pure G} `{Mult G}
    {v1 v2 : Type} (f: nat * v1 -> G (term v2)).

  Definition binddt_term_rw1: forall x,
      BD f (tvar x) = f (0, x) := ltac:(reflexivity).

  Definition binddt_term_rw2: forall τ body,
      binddt f (@lam _ τ body) =
        (P (λ τ) <⋆> BD (f ⦿ 1) body)
    := ltac:(reflexivity).

  Definition binddt_term_rw3: forall t1 t2,
      binddt f (@app _ t1 t2) =
        (P (@app v2) <⋆> BD f t1 <⋆> BD f t2)
    := ltac:(reflexivity).

  Lemma binddt_pointfree_lam: forall τ,
    BD f ∘ (@lam v1 τ) =
      (precompose (BD (f ⦿ 1)) ∘ ap G ∘ P) (@lam v2 τ).
  Proof.
    reflexivity.
  Qed.

  Lemma binddt_pointfree_app :
    compose (BD f) ∘ @app v1 =
      (compose (precompose (BD f) ∘ ap G) ∘ precompose (BD f) ∘ ap G ∘ P) (@app v2).
  Proof.
    reflexivity.
  Qed.

End rw.

Ltac simplify_binddt_term :=
  match goal with
  | |- context[BD ?f (tvar ?y)] =>
      ltac_trace "simplify_binddt_term_tvar";
      rewrite binddt_term_rw1
  | |- context[((BD ?f) ((λ) ?τ ?body))] =>
      ltac_trace "simplify_binddt_term_abs";
      rewrite binddt_term_rw2
  | |- context[((BD ?f) (app ?t1 ?t2))] =>
      ltac_trace "simplify_binddt_term_app";
      rewrite binddt_term_rw3
  end.

Ltac simplify_binddt_term_lazy unit :=
  simplify_binddt_term.

(*
Ltac derive_dtm_law :=
  derive_dtm_law_with_simplify_binddt simplify_binddt_term_lazy.
*)

(*
change does not work as well as rewrite because it the right-hand side
seems to do its own typeclass resolution rather than taking the information from the match (which seems not completely unreasonable in general *)
(*
Ltac binddt_term_1 :=
  change ((BD ?f) (tvar ?x)) with (f (0, x)).

Ltac binddt_term_2 :=
  change ((BD ?f) ((λ) ?τ ?body)) with
    (P ((λ) τ) <⋆> BD (f ⦿ 1) body).

Ltac binddt_term_3 :=
  change ((BD ?f) (app ?t1 ?t2)) with
    (P (@app _) <⋆> BD f t1 <⋆> BD f t2).
 *)

(*|
========================================
An overview of the DTM axioms
========================================
|*)

Section laws.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Composition with unit (left unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The "composition with unit" law (or left unit law) establishes that
the atomic expression `ret term v`

1. consists just of variable `v`
2. inside an empty binding context

In this law, `ret (list β ×)` is the operation which lifts any `v`
into an empty binding context to get `([], v)`. A simpler way of
writing the left unit law is then

`binddt f (ret term v) = f ([], v)`

The proof of this rule ought to follow merely from the definitions of
`binddt` and `ret`.  In the course of proofs about `binddt f t` by
induction of the syntax of expression `t`, the left unit law acts as
a base case.

.. coq::
   :name: dtm1
|*)
  Theorem dtm1_stlc:
    forall `{Applicative G} (A B : Type),
       forall f : nat * A -> G (term B),
         binddt f ∘ ret  = f ∘ ret (T := (nat ×)).
  Proof.
    reflexivity.
  Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Identity law (right unit law)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The identity law (or right unit law) establishes that applying the
substitution rule

`pure F ∘ ret term ∘ extract ((list β) ×)`

to each of the variables in expression `t` acts as the pure effect on
`t`. The substitution rule is the one which at each variable

1. throws away the binding context: `list β * v -> v`
2. coerces the variable into an atomic expression: `v -> term v`
3. and lifts the result into `F` with the `pure` effect: `term v -> F (term v)`

.. coq::
   :name: dtm2
|*)

Theorem dtm2_stlc: forall A: Type,
      binddt (T := term) (U := term)
        (G := fun A => A) (ret (T := term) ∘ extract (W := (nat ×))) = @id (term A).
Proof.
  derive_dtm_law.
Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~
Composition law
~~~~~~~~~~~~~~~~~~~~~~~~

The composition law states the following:

`map F (binddt g) ∘ binddt f = binddt (g ⋆ f)`

The right-hand side may be written more explicitly as

`binddt (fun '(w, x) => map F (binddt (F := G) (g ∘ incr w)) (f (w, x))))`

This law is an analogue of the ordinary monad composition law

`bind g ∘ bind f = bind (bind g ∘ f)`.

Both are loosely of the form

`bind g ∘ bind f = bind (g ∗ f)`

A close comparison shows the rules differ in two respects:

1. The call to `g` in `bind g` is replaced with a call to `(g ∘ incr
   w)` where `w` is the context seen by the function `f`.
2. The call to `binddt (g ∘ incr w)` is wrapped in `map F`. This is
   required to map over the applicative effect of type `F` generated
   by the application of `f`.

.. coq::
   :name: dtm3
|*)
Theorem dtm3_stlc :
  forall `{Applicative G1} `{Applicative G2},
  forall `(g : nat * B -> G2 (term C)) `(f : nat * A -> G1 (term B)),
    map (binddt g) ∘ binddt f = binddt (G := G1 ∘ G2) (g ⋆7 f).
Proof.
  derive_dtm_law.
Qed.

(*|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Applicative homomorphism law
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This law states that `binddt` is parametric with respect to
applicative functors in the sense that it commutes with their
homomorphisms. It is (probably?) a free theorem, so it is not actually
a restriction on implementations of `binddt` (cite Gibbons).


.. coq::
   :name: dtm4
|*)

  Theorem dtm4_stlc :
    forall (G1 G2 : Type -> Type)
      (H1 : Map G1) (H2 : Mult G1) (H3 : Pure G1)
      (H4 : Map G2) (H5 : Mult G2) (H6 : Pure G2)
      (ϕ : forall A : Type, G1 A -> G2 A),
      ApplicativeMorphism G1 G2 ϕ ->
      forall (A B : Type) (f : nat * A -> G1 (term B)),
        ϕ (term B) ∘ binddt f = binddt (ϕ (term B) ∘ f).
  Proof.
    derive_dtm_law.
  Qed.

  #[export] Instance DTM_STLC:
    DecoratedTraversableMonad nat term.
  Proof.
    derive_dtm.
  match goal with
  | |- DecoratedTraversableMonad ?W ?T =>
      constructor;
      try (timeout 1 typeclasses eauto);
      try (match goal with
           | |- DecoratedTraversableRightPreModule ?W ?T ?U =>
               constructor
           end);
      derive_dtm_law
  end.
      match goal with
      | |- DecoratedTraversableRightPreModule ?W ?T ?U =>
          constructor
      end.
      derive_dtm_law.
  end.

  match goal with
  | |- DecoratedTraversableMonad ?W ?T =>
      constructor
  end.

  try (timeout 1 typeclasses eauto).

      match goal with
      | |- DecoratedTraversableRightPreModule ?W ?T ?U =>
          constructor;
          derive_dtm_law
      end

  constructor. typeclasses eauto.
         intros.
         Set Printing All.
  match goal with
  | |- context[(binddt (T := ?T) (U := ?U) ?f ∘ ret)] =>
      idtac "setup_dtm_proof_guess_law1";
      derive_dtm1
  end.

        setup_dtm_proof.
         derive_dtm1.
    {| kdtm_binddt0 := @dtm1_stlc;
    |}.

  #[export] Instance DTMPre_STLC:
    DecoratedTraversableRightPreModule nat term term :=
    {| kdtm_binddt1 := dtm2_stlc;
      kdtm_binddt2 := @dtm3_stlc;
      kdtm_morph := @dtm4_stlc;
    |}.

  #[export] Instance DTM_STLC:
    DecoratedTraversableMonad nat term :=
    {| kdtm_binddt0 := @dtm1_stlc;
    |}.

  #[export] Instance DTMFull_STLC:
    DecoratedTraversableMonadFull nat term
    := DecoratedTraversableMonadFull_DecoratedTraversableMonad nat term.

End laws.

