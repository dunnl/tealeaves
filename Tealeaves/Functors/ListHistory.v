From Tealeaves Require Export
  Classes.Functor
  Functors.List
  Classes.Monoid
  Classes.Kleisli.DecoratedMonad.

Import List.ListNotations.
Import Monoid.Notations.

(* Map a context-sensitive function over the list, where the context is the prefix of the list up to the point considered. hfold = fold with history. *)
Fixpoint hmap {A B : Type} (f : list A * A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons a rest => cons (f (Ƶ, a)) (hmap (preincr f [a]) rest)
  end.

Lemma hmap_cons {A B : Type} (f : list A * A -> B) (a : A) (l : list A) :
  hmap f (a :: l) = cons (f (Ƶ, a)) (hmap (preincr f [a]) l).
Proof.
  reflexivity.
Qed.

Lemma hmap_app : forall {WA WB : Type}
                    (ρf : list WA * WA -> WB)
                    (wa wa' : list WA),
    hmap ρf (wa ● wa') =
      hmap ρf wa ● hmap (preincr ρf wa) wa'.
Proof.
  intros. generalize dependent ρf. induction wa; intros ρf.
  - change (@nil WA) with (Ƶ : list WA) at 1 3.
    rewrite monoid_id_r.
    rewrite preincr_zero.
    reflexivity.
  - cbn. fequal. rewrite IHwa.
    rewrite preincr_preincr.
    reflexivity.
Qed.

(** ** Alternative presentation *)
Module Hmap_alt.

  Fixpoint hmap_rec {A B : Type} (f : list A * A -> B) (ctx : list A) (l : list A) : list B :=
    match l with
    | nil => nil
    | cons a rest => cons (f (ctx, a)) (hmap_rec f (ctx ● [a]) rest)
    end.

  Lemma hmap_rec_cons {A B : Type} (f : list A * A -> B) (ctx : list A) (a : A) (l : list A) :
    hmap_rec f ctx (a :: l) = cons (f (ctx, a)) (hmap_rec f (ctx ++ [a]) l).
  Proof.
    reflexivity.
  Qed.

  Definition hmap' {A B : Type} (f : list A * A -> B) : list A -> list B :=
    hmap_rec f nil.

  Lemma hmap_rec_spec : forall {A B} (f : list A * A -> B) a, hmap (preincr f a) = hmap_rec f a.
  Proof.
    intros. ext l.
    generalize dependent a. induction l.
    - intros. reflexivity.
    - intros. cbn.
      rewrite preincr_preincr.
      rewrite IHl.
      unfold preincr, compose, incr.
      rewrite monoid_id_l.
      reflexivity.
  Qed.

  Lemma hmap_spec : forall {A B} (f : list A * A -> B), hmap f = hmap' f.
  Proof.
    intros. replace f with (preincr f Ƶ) at 1 by (now rewrite preincr_zero).
    apply hmap_rec_spec.
  Qed.

End Hmap_alt.
