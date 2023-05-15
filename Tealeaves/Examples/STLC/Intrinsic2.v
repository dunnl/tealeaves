
From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Classes.Comonad
  Functors.Writer.
From Tealeaves Require
  Classes.Monad
  Classes.Kleisli.Decorated.Monad.

Export Decorated.Monad (preincr).

Import Monoid.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ T W G A B C D F M.

(** * The <<prepromote>> operation *)
(** A decorated monad is a decorated functor whose monad operations
    are compatible with the decorated structure. *)
(******************************************************************************)
Implicit Types (A B : nat -> Type).

Open Scope nat_scope.

Definition preincr {A B : nat -> Type} (n : nat) `(f : forall (n : nat), A n -> B n) : forall (m : nat), A (n + m) -> B (n + m) :=
  (fun m a => f (n + m) a).

Lemma preincr_zero `{Monoid W} : forall `(f : forall (n : nat), A n -> B n),
    preincr 0 f = f.
Proof.
  intros. unfold preincr.
  ext m a. fequal.
Qed.

(*
Definition delta (A : nat -> Type) (n : nat) : nat -> Type :=
  (fun m => A (n + m)).
 *)

Notation "'delta' A 'by' n" := (fun m => (A (n + m))) (at level 10).

(*
Lemma preincr_preincr1 `{Monoid W} : forall `(f : forall (n : nat), A n  -> B n) (m1 : nat) (m2 : nat),
    preincr m2 (preincr m1 f) = preincr (m1 + m2) f.
Proof.
  intros. unfold preincr.
  reassociate ->.
  now rewrite (incr_incr).
Qed.

Lemma preincr_ret `{Monoid W} : forall `(f : W * A -> B) (w : W),
    preincr w f ∘ ret (W ×) = f ∘ pair w.
Proof.
  intros. ext a. cbv.
  change (op w unit0) with (w ● Ƶ).
  now simpl_monoid.
Qed.

Lemma preincr_extract `{Monoid W} : forall `(f : A -> B) (w : W),
    preincr w (f ∘ extract (W ×)) = f ∘ extract (W ×).
Proof.
  intros. now ext [w' a].
Qed.

Lemma preincr_extract2 `{Monoid W} : forall (A : Type) (w : W),
    preincr w (extract (W ×)) = extract (W ×) (A := A).
Proof.
  intros. now ext [w' a].
Qed.
*)


Section operations.

  Context
    (T : (nat -> Type) -> Type)
      (F : (nat -> Type) -> Type).

  Definition TL : (nat -> Type) -> (nat -> Type) :=
    fun A n => T (delta A by n).

  Class Return :=
    ret : forall (A : nat -> Type), A 0 -> T A.

  Class Binddt :=
    binddt :
      forall (G : Type -> Type)
        `{Fmap G} `{Pure G} `{Mult G}
        (A B : nat -> Type),
        (forall (n : nat), A n -> G (T (delta B by n))) -> F A -> G (F B).

End operations.

Definition kcompose_dtm
  {A B C : nat -> Type}
  `{Fmap G1} `{Pure G1} `{Mult G1}
  `{Fmap G2} `{Pure G2} `{Mult G2}
  `{Binddt T T}
  (g : forall (n : nat), B n -> G2 (T (delta C by n)))
  (f : forall (n : nat), A n -> G1 (T (delta B by n)))
  : (forall (n : nat), A n -> G1 (G2 (T C))) :=
  fun n a => fmap G1 (binddt T T G2 (delta B by n) (delta C by n) (preincr n g)) (f n a).

#[local] Infix "⋆dtm" := kcompose_dtm (at level 60) : tealeaves_scope.

Section class.

  Context
      (T : (nat -> Type) -> Type)
      `{Return T}
      `{Binddt T T}.

  Class Monad :=
    {
      kdtm_binddt0 : forall (A B : nat -> Type) `{Applicative G} (f : forall (n : nat), A n -> G (T (delta B n))),
        binddt T T G A B f ∘ ret T A = f 0;
      kdtm_morph : forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : forall n, A n -> G1 (T (delta B n))),
        ϕ (T B) ∘ binddt T T G1 A B f = binddt T T G2 A B (fun n a => ϕ (T (delta B n)) (f n a));
      kdtm_binddt1 : forall (A : nat -> Type),
        binddt T T (fun X => X) A A (fun n => ret T (fun m => A (n + m))) = @id (T A);
    }.
      kdtm_binddt2 :
      forall (A B C : Type) `{Applicative G1} `{Applicative G2}
        (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
        fmap G1 (binddt W T T G2 B C g) ∘ binddt W T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (g ⋆dtm f);
    }.

End class.

#[global] Arguments binddt {W}%type_scope {T}%function_scope (F)%function_scope
  {Binddt} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
