(** This file defines typeclasses *)
From Tealeaves Require Export
  Prelude
  Classes.Applicative
  Classes.Monoid
  Classes.Functor.

#[local] Generalizable Variables F G A B W T U ϕ.

Import Product.Notations.
Import Monoid.Notations.
Import Functor.Notations.
Import Monoid.Notations.
Import Product.Notations.

Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

(** * Operational typeclasses for comonads *)
(******************************************************************************)
Section operations.

  Context
    (W : Type -> Type).

  Class Extract :=
    extract : W ⇒ (fun A => A).

  Class Cobind :=
    cobind : forall (A B : Type), (W A -> B) -> W A -> W B.

End operations.

Section kc4.

  Context
    (W : Type -> Type)
    `{Cobind W}.

  Definition kc4
    {A B C : Type}
    `(g : W B -> C)
    `(f : W A -> B)
    : (W A -> C) :=
    g ∘ cobind W A B f.

End kc4.

#[local] Infix "⋆4" := (kc4 _) (at level 60) : tealeaves_scope.

Section Comonad.

  Context
    `(W : Type -> Type)
    `{Cobind W}
    `{Extract W}.

  Class Comonad :=
    { kcom_cobind0 : forall `(f : W A -> B),
        extract W B ∘ cobind W A B f = f;
      kcom_cobind1 : forall (A : Type),
        cobind W A A (extract W A) = @id (W A);
      kcom_cobind2 : forall (A B C : Type) (g : W B -> C) (f : W A -> B),
        cobind W B C g ∘ cobind W A B f = cobind W A C (g ⋆4 f)
    }.

End Comonad.

(** * Operational typeclasses for DTM hierarchy *)
(******************************************************************************)
Section operations.

  Context
    (M : Type)
    (T : Type -> Type)
    (U : Type -> Type).

    Class Return :=
      ret : (fun A => A) ⇒ T.

    Class Traverse := traverse :
        forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (A -> G B) -> T A -> G (T B).

    Class Mapd := mapd :
        forall (A B : Type),
          (M * A -> B) -> T A -> T B.

    Class Mapdt := mapdt :
        forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (M * A -> G B) -> T A -> G (T B).

    Class Bind :=
      bind : forall (A B : Type), (A -> T B) -> U A -> U B.

    Class Bindd := bindd :
        forall (A B : Type),
          (M * A -> T B) -> U A -> U B.

    Class Bindt := bindt :
        forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (A -> G (T B)) -> U A -> G (U B).

    Class Binddt := binddt :
        forall (G : Type -> Type)
          `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (M * A -> G (T B)) -> U A -> G (U B).

End operations.

#[export] Instance Extract_env {E : Type} : Extract (E ×) :=
  fun A '(e, a) => a.

#[export] Instance Cobind_env {E : Type} : Cobind (E ×) :=
  fun A B (f : E * A -> B) '(e, a) => (e, f (e, a)).

#[export] Instance Return_writer {M : Type} `{Monoid_unit M} : Return (prod M) :=
  fun A (a : A) => (Ƶ, a).

(** * Kleisli-style typeclasses for structured functors *)
(******************************************************************************)

(** ** Monad *)
(******************************************************************************)

Section kc.

  Context
    (T : Type -> Type)
    `{Return T}
    `{Bind T T}.

  Definition kc1
    {A B C : Type}
    (g : B -> T C)
    (f : A -> T B) :
    (A -> T C) :=
    bind T T B C g ∘ f.

End kc.

#[local] Infix "⋆1" := (kc1 _) (at level 60) : tealeaves_scope.

Section class.

  Context
    (T : Type -> Type)
    `{Return T}
    `{Bind T T}.

  Class Monad :=
    { (* left unit law of the monoid *)
      kmon_bind0 : forall (A B : Type) (f : A -> T B),
        bind T T A B f ∘ ret T A = f;
      (* right unit law of the monoid *)
      kmon_bind1 : forall (A : Type),
        bind T T A A (ret T A) = @id (T A);
      (* associativity of the monoid *)
      kmon_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind T T B C g ∘ bind T T A B f = bind T T A C (g ⋆1 f);
    }.

End class.

(** *** Monad Homomorphisms *)
(******************************************************************************)
Section class.

  Context
    (T U : Type -> Type)
      `{Return T} `{Bind T T}
      `{Return U} `{Bind U U}.

  Class MonadHom (ϕ : forall (A : Type), T A -> U A) :=
    { kmon_hom_bind : forall (A B : Type) (f : A -> T B),
        ϕ B ∘ bind T T A B f = bind U U A B (ϕ B ∘ f) ∘ ϕ A;
      kmon_hom_ret : forall (A : Type),
        ϕ A ∘ ret T A = ret U A;
    }.

End class.

(** *** Right modules *)
(******************************************************************************)
Section class.

  Context
    (T : Type -> Type)
    (U : Type -> Type)
    `{Return T} `{Bind T T} `{Bind T U}.

  Class RightModule :=
    { kmod_monad :> Monad T;
      kmod_bind1 : forall (A : Type),
        bind T U A A (ret T A) = @id (U A);
      kmod_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
        bind T U B C g ∘ bind T U A B f = bind T U A C (g ⋆1 f);
    }.

End class.

(** ** Decorated functor *)
(******************************************************************************)

(* Here would go kc4 *)

Section class.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Mapd E T}.

  Class DecoratedFunctor :=
    { dfun_mapd1 : forall (A : Type),
        mapd E T A A (extract (E ×) A) = @id (T A);
      dfun_mapd2 : forall (A B C : Type) (g : E * B -> C) (f : E * A -> B),
        mapd E T B C g ∘ mapd E T A B f = mapd E T A C (g ⋆4 f);
    }.

End class.

(** ** Decorated monad *)
(******************************************************************************)
Section kc.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Bindd W T T}
    `{Monoid_op W}.

  Definition kc5 {A B C : Type} :
    (W * B -> T C) ->
    (W * A -> T B) ->
    (W * A -> T C) :=
    fun g f '(w, a) => bindd W T T B C (g ⦿ w) (f (w, a)).

End kc.

#[local] Infix "⋆5" := (kc5 _ _) (at level 60) : tealeaves_scope.

Section class.

  Context
    {W : Type}
    (T : Type -> Type)
    `{Return T}
    `{Bindd W T T}
    `{Monoid_op W} `{Monoid_unit W}.

  Class DecoratedMonad :=
    { kmond_monoid :> Monoid W;
      kmond_bindd0 : forall (A B : Type) (f : W * A -> T B),
        bindd W T T A B f  ∘ ret T A = f ∘ ret (W ×) A;
      kmond_bindd1 : forall (A : Type),
        bindd W T T A A (ret T A ∘ extract (W ×) A) = @id (T A);
      kmond_bindd2 : forall (A B C : Type) (g : W * B -> T C) (f : W * A -> T B),
        bindd W T T B C g ∘ bindd W T T A B f = bindd W T T A C (g ⋆5 f);
    }.

End class.

(** ** Traversable functor *)
(******************************************************************************)

(* Here would go kc2 *)

Section class.

  Context
    (T : Type -> Type)
    `{Traverse T}.

  Class TraversableFunctor :=
    { trf_traverse_id : forall (A : Type),
        traverse T (fun A => A) A A id = @id (T A);
      trf_traverse_traverse :
      forall (G1 G2 : Type -> Type)
        `{Applicative G1}
        `{Applicative G2}
        {A B C : Type}
        (g : B -> G2 C) (f : A -> G1 B),
        map G1 (T B) (G2 (T C)) (traverse T G2 B C g) ∘ traverse T G1 A B f =
          traverse T (G1 ∘ G2) A C (map G1 B (G2 C) g ∘ f);
      trf_traverse_morphism : forall `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : A -> G1 B),
        ϕ (T B) ∘ traverse T G1 A B f = traverse T G2 A B (ϕ B ∘ f);
    }.

End class.

(** ** Traversable monad *)
(******************************************************************************)
Section kc.

  Context
    (T : Type -> Type)
    `{Bindt T T}.

  Definition kc3
    {A B C : Type}
    (G1 G2 : Type -> Type)
    `{Map G1} `{Pure G1} `{Mult G1}
    `{Map G2} `{Pure G2} `{Mult G2} :
    (B -> G2 (T C)) ->
    (A -> G1 (T B)) ->
    (A -> G1 (G2 (T C))) :=
    fun g f => map G1 (T B) (G2 (T C)) (bindt T T G2 B C g) ∘ f.

End kc.

#[local] Infix "⋆3" := (kc3 _ _ _) (at level 60) : tealeaves_scope.

Section class.

  Context
    (T : Type -> Type)
    `{Return T}
    `{Bindt T T}.

  Class TraversableMonad :=
    { ktm_bindt0 : forall (A B : Type) `{Applicative G} (f : A -> G (T B)),
        bindt T T G A B f ∘ ret T A = f;
      ktm_bindt1 : forall (A : Type),
        bindt T T (fun A => A) A A (ret T A) = @id (T A);
      ktm_bindt2 : forall (G1 G2 : Type -> Type) `{Applicative G1} `{Applicative G2} (A B C : Type)
        (g : B -> G2 (T C)) (f : A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (bindt T T G2 B C g) ∘ bindt T T G1 A B f =
          bindt T T (G1 ∘ G2) A C (g ⋆3 f);
      ktm_morph : forall `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : A -> G1 (T B)),
          ϕ (T B) ∘ bindt T T G1 A B f = bindt T T G2 A B (ϕ (T B) ∘ f);
    }.

End class.

(** ** Decorated traversable functor *)
(******************************************************************************)
Section kc.

  Context
    (E : Type).

  Definition kc6
    {A B C}
    (G1 G2 : Type -> Type)
    `{Map G1} `{Pure G1} `{Mult G1}
    `{Map G2} `{Pure G2} `{Mult G2} :
    (E * B -> G2 C) ->
    (E * A -> G1 B) ->
    (E * A -> G1 (G2 C)) :=
    fun g f => map G1 (E * B) (G2 C) g ∘ strength G1 ∘ cobind (prod E) A (G1 B) f.

End kc.

#[local] Infix "⋆6" := (kc6 _ _ _) (at level 60) : tealeaves_scope.

Section class.

  Context
    (E : Type)
    (T : Type -> Type)
    `{Mapdt E T}.

  Class DecoratedTraversableFunctor :=
    { kdtfun_mapdt1 : forall (A : Type),
        mapdt E T (fun A => A) A A (extract (E ×) A) = @id (T A);
      kdtfun_mapdt2 : forall (G1 G2 : Type -> Type)
                        `{Applicative G1} `{Applicative G2}
                        (A B C : Type)
                        `(g : E * B -> G2 C) `(f : E * A -> G1 B),
        map G1 (T B) (G2 (T C)) (mapdt E T G2 B C g) ∘ mapdt E T G1 A B f = mapdt E T (G1 ∘ G2) A C (g ⋆6 f);
      kdtfun_morph : forall `{ApplicativeMorphism G1 G2 ϕ} `(f : E * A -> G1 B),
        mapdt E T G2 A B (ϕ B ∘ f) = ϕ (T B) ∘ mapdt E T G1 A B f;
    }.

End class.

(** ** Decorated traversable monad *)
(******************************************************************************)
Section kc.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Return T}
    `{Binddt W T T}
    `{op: Monoid_op W} `{unit: Monoid_unit W}.

  Definition kc7
    {A B C}
    (G1 G2 : Type -> Type)
    `{Map G1} `{Pure G1} `{Mult G1}
    `{Map G2} `{Pure G2} `{Mult G2} :
    (W * B -> G2 (T C)) ->
    (W * A -> G1 (T B)) ->
    (W * A -> G1 (G2 (T C))) :=
    fun g f '(w, a) => map G1 (T B) (G2 (T C)) (binddt W T T G2 B C (g ⦿ w)) (f (w, a)).

End kc.

#[local] Infix "⋆7" := (kc7 _ _ _ _) (at level 60) : tealeaves_scope.

Section class.

  Context
    (W : Type)
    (T : Type -> Type)
    `{Return T}
    `{Binddt W T T}
    `{op: Monoid_op W} `{unit: Monoid_unit W}.

  Class DTM :=
    { kdtm_monoid :> Monoid W;
      kdtm_binddt0 : forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : W * A -> G (T B)),
        binddt W T T G A B f ∘ ret T A = f ∘ ret (W ×) A;
      kdtm_binddt1 : forall (A : Type),
        binddt W T T (fun A => A) A A (ret T A ∘ extract (W ×) A) = @id (T A);
      kdtm_binddt2 :
      forall (G1 G2 : Type -> Type) `{Applicative G1} `{Applicative G2}
        (A B C : Type)
        (g : W * B -> G2 (T C)) (f : W * A -> G1 (T B)),
        map G1 (T B) (G2 (T C)) (binddt W T T G2 B C g) ∘ binddt W T T G1 A B f =
          binddt W T T (G1 ∘ G2) A C (g ⋆7 f);
      kdtm_morph : forall (G1 G2 : Type -> Type) `{morph : ApplicativeMorphism G1 G2 ϕ} `(f : W * A -> G1 (T B)),
        ϕ (T B) ∘ binddt W T T G1 A B f = binddt W T T G2 A B (ϕ (T B) ∘ f);
    }.

End class.

Module Notations.

  Infix "⋆1" := (kc1 _) (at level 60) : tealeaves_scope.
  Infix "⋆3" := (kc3 _ _ _) (at level 60) : tealeaves_scope.
  Infix "⋆4" := (kc4 _) (at level 60) : tealeaves_scope.
  Infix "⋆5" := (kc5 _ _) (at level 60) : tealeaves_scope.
  Infix "⋆6" := (kc6 _ _ _) (at level 60) : tealeaves_scope.
  Infix "⋆7" := (kc7 _ _ _ _) (at level 60) : tealeaves_scope.

End Notations.
