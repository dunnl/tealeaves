(*|
This file contains typeclasses for categories, categories, and monads.
In Tealeaves we mostly used definitions specialized to the category of
Coq types and functors rather than using this typeclass, but it is
available for future abstract nonsense.
|*)

(** The implementation here closely resembles that of math-classes, see *)
(** # <a href="https://github.com/coq-community/math-classes"> https://github.com/coq-community/math-classes</a># *)
(** but this development focuses more on monad-related abstractions
    such as modules and comonads. *)
From Tealeaves Require Export
     Prelude.

Declare Scope category_scope.
Delimit Scope category_scope with cat.
Open Scope category_scope.

#[local] Generalizable Variables C D E F G T U a.

(** * Categories *)
(******************************************************************************)

(** ** Operational typeclasses *)
(******************************************************************************)
Class Arrows (Obj : Type) : Type :=
  homset : Obj -> Obj -> Type.

Class Identities Obj `{Arrows Obj} :=
  catid : forall (x : Obj), homset x x.

Class Composition Obj `{Arrows Obj} :=
  comp : forall (x y z : Obj), homset y z -> homset x y -> homset x z.

(** ** Notations *)
(******************************************************************************)
Module Notations.
  Infix "⟶" := (homset) (at level 90, right associativity) : category_scope.
  Infix "⊙":= (comp _ _ _) (at level 40, left associativity) : category_scope.
  Notation "F ⇒ G" := (forall a : _, homset (F a) (G a)) (at level 50) : category_scope.
End Notations.

Import Notations.

(** ** Category typeclass *)
(******************************************************************************)
Section category.

  Context
    (Obj : Type)
    `{Arrows Obj}
    `{! Identities Obj}
    `{! Composition Obj}.

  Class Category :=
    { cat_assoc {w x y z} (c : y ⟶ z) (b : x ⟶ y) (a : w ⟶ x) :
        c ⊙ (b ⊙ a) = (c ⊙ b) ⊙ a;
      cat_id_r {x y} (a : x ⟶ y):
        a ⊙ catid x = a;
      cat_id_l {x y} (a : x ⟶ y) :
        catid y ⊙ a = a;
    }.

End category.

(** * Functors *)
(******************************************************************************)
Section functor.

  Context
    `{Category C}
    `{Category D}
    (F : C -> D).

  Open Scope category_scope.

  Class Fmap : Type  :=
    fmap: forall {a b : C} (f : a ⟶ b), F a ⟶ F b.

  #[local] Arguments fmap {Fmap a b} (_)%cat.

  (* don't register category fields as coercions to avoid loops *)
  Class Functor `(Fmap) : Prop :=
    { func_src : Category C;
      func_tgt : Category D;
      fmap_id : forall a : C,
          fmap (catid a) = catid (F a);
      fmap_fmap : forall a b c (f : a ⟶ b) (g : b ⟶ c),
          fmap g ⊙ fmap f = fmap (g ⊙ f);
    }.

End functor.

(** ** Natural transformations *)
(******************************************************************************)
Section natural_transformation.


  Generalizable All Variables.

  Context
    `{Category C}
    `{Category D}
    `{! Fmap (C := C) (D := D) F}
    `{! Fmap (C := C) (D := D) G}
    `{! Functor (F : C -> D) _}
    `{! Functor (G : C -> D) _}.

  Class Natural (η : forall x, F x ⟶ G x) :=
    naturality : forall {x y} (f : x ⟶ y),
      fmap G f ⊙ η x = η y ⊙ fmap F f.

End natural_transformation.

(** ** Monoidal structure on endofunctors *)
(** Endofunctors are closed under composition and identities. This gives
    monoidal structure on the category of endofunctors but we do not need to
    formalize that far. *)
(******************************************************************************)
Section endofunctor_id.

  Context
    `{Category C}.

  #[export] Instance Fmap_one : Fmap (fun x => x) :=
    (fun (a b : C) (f : a ⟶ b) => f).

  Definition fmap_id_one : forall (a : C),
      fmap (fun x => x) (catid a) = catid a := ltac:(reflexivity).

  Definition fmap_fmap_one a b c (f : a ⟶ b) (g : b ⟶ c) :
    fmap (fun x => x) g ⊙ fmap (fun x => x) f = fmap (fun x => x) (g ⊙ f) := ltac:(reflexivity).

  #[export] Program Instance Functor_one : Functor (fun x => x) _ :=
    {| fmap_id := fmap_id_one;
       fmap_fmap := fmap_fmap_one;
    |}.

End endofunctor_id.

Section endofunctor_composition.

  Context
    `{Category C}
    `{Category D}
    `{Category E}
    `{! Fmap (C := C) (D := D) F}
    `{! Fmap (C := D) (D := E) G}
    `{! Functor (F : C -> D) _}
    `{! Functor (G : D -> E) _}.

  #[export] Instance Fmap_compose : Fmap (G ∘ F) :=
    fun a b f => fmap G (fmap F f).

  Lemma fmap_id_compose : forall (a : C),
      fmap (G ∘ F) (catid a) = catid (G (F a)).
  Proof.
    intros ?; unfold fmap, Fmap_compose.
    now rewrite (fmap_id F), (fmap_id G).
  Qed.

  Lemma fmap_fmap_compose (a b c : C) (f : a ⟶ b) (g : b ⟶ c) :
    fmap (G ∘ F) g ⊙ fmap (G ∘ F) f = fmap (G ∘ F) (g ⊙ f).
  Proof.
    unfold fmap, Fmap_compose, compose.
    now rewrite (fmap_fmap G), (fmap_fmap F).
  Qed.

  #[export] Instance Functor_compose : Functor (G ∘ F) _ :=
    {| fmap_id := fmap_id_compose;
       fmap_fmap := fmap_fmap_compose;
    |}.

End endofunctor_composition.

(** * Monads and modules *)
(******************************************************************************)
Section monad_operations.

  Context
    `{Category C}
    (T : C -> C).

  Class Join := join : T ∘ T ⇒ T.

  Class Return := ret : (fun x => x) ⇒ T.

End monad_operations.

Section monad.

  Context
    `{Category C}
      (T : C -> C)
    `{! Fmap (C := C) (D := C) T}
    `{! Functor T _}
    `{! Return T} `{! Join T}.

  Class Monad :=
    { mon_functor :> Functor T _;
      mon_ret_natural :> Natural (ret T);
      mon_join_natural :> Natural (join T);
      mon_join_fmap_ret :
        `(join T a ⊙ (fmap T (ret T a)) = catid (T a));
      mon_join_ret :
        `(join T a ⊙ (ret T (T a)) = catid (T a));
      mon_join_join :
        `(join T a ⊙ (join T (T a)) = join T a ⊙ (fmap T (join T a)));
    }.

End monad.

Section monad_homomorphism.

  Context
    `{Category C}
    `{! Fmap (C := C) (D := C) T}
    `{! Fmap (C := C) (D := C) U}
    `{! Functor (T : C -> C) _}
    `{! Functor (U : C -> C) _}
    `{! Return T} `{! Join T}
    `{! Return U} `{! Join U}
    `{! Monad T} `{! Monad U}.

  Class Monad_Hom (mhom : forall a, T a ⟶ U a) :=
    { mhom_domain : Monad T;
      mhom_codomain : Monad U;
      mhom_natural : Natural mhom;
      mhom_ret :
        `(mhom a ⊙ (ret T a) = ret U a);
      mhom_join :
        `(mhom a ⊙ (join T a) = join U a ⊙ (mhom (U a) ⊙ (fmap T (mhom a))));
    }.

End monad_homomorphism.

(** ** Right modules of endofunctors  *)
(******************************************************************************)
Section RightModule.

  Context
    {C D : Type}
    (F : C -> D)
    (T : C -> C)
    `{Monad C T}
    `{Category D}
    `{! Fmap (C := C) (D := D) F}
    `{! Functor F _ }.

  Class RightAction := right_action : F ∘ T ⇒ F.

  Class RightModule `{RightAction} :=
    { rmod_monad :> Monad T;
      rmod_object :> Functor F _;
      rmod_natural : Natural (right_action);
      rmod_ret :
        `(right_action a ⊙ fmap F (ret T a) = catid (F a));
      rmod_join :
        `(right_action a ⊙ right_action (T a) = right_action a ⊙ fmap F (join T a));
    }.

End RightModule.

(** ** The [bind] operation *)
(******************************************************************************)
Section bind.

  Context
    {C D : Type}
    (F : C -> D)
    (T : C -> C)
    `{RightModule C D F T}.

  Class Bind := bind : forall {a b : C} (f : a ⟶ T b), F a ⟶ F b.

  #[local] Arguments bind {Bind a b} (_)%cat.

  Definition compose_kleisli {a b c : C} :
    (b ⟶ T c) -> (a ⟶ T b) -> a ⟶ T c :=
    fun g f => join T c ⊙ (fmap T g ⊙ f).

End bind.

Module KleisliNotation.
  Notation "g ⋆ f" := (compose_kleisli _ g f) (at level 60) : category_scope.
End KleisliNotation.

Import KleisliNotation.

Section module_bind.

  Context
    `{RightModule C D F T}
    `{! Category C}
    `{! Category D}.

  #[export] Instance Bind_Module : Bind F T :=
    fun {a b} {f : a ⟶ T b} => right_action F T b ⊙ fmap F f.

  Context
    {a b c : C}.

  Lemma bind_ret_fmap : forall (f : a ⟶ b),
      bind F T (ret T b ⊙ f) = fmap F f.
  Proof.
    intros. unfold bind, Bind_Module.
    rewrite <- (fmap_fmap F).
    rewrite (cat_assoc D).
    rewrite (rmod_ret F T).
    rewrite (cat_id_l D).
    reflexivity.
  Qed.

  Lemma bind_functorial : forall (f : a ⟶ T b) (g : b ⟶ T c),
      bind F T (g ⋆ f) = (bind F T g) ⊙ (bind F T f).
  Proof.
    intros f g. unfold bind, Bind_Module.
    unfold compose_kleisli.
    rewrite <- (fmap_fmap F).
    rewrite <- (fmap_fmap F).
    repeat rewrite (cat_assoc D).
    rewrite <- (rmod_join F T).
    change (fmap F (fmap T g)) with (fmap (F ∘ T) g).
    repeat rewrite <- (cat_assoc D).
    rewrite (cat_assoc D (right_action F T (T c)) _ _).
    rewrite <- (naturality (Natural := rmod_natural F T) g).
    now repeat rewrite <- (cat_assoc D).
  Qed.

  Lemma bind_fmap : forall (g : b ⟶ T c) (f : a ⟶ b),
      bind F T g ⊙ (fmap F f) = bind F T (g ⊙ f).
  Proof.
    intros.
    unfold bind, Bind_Module.
    rewrite <- (fmap_fmap F).
    now rewrite <- (cat_assoc D).
  Qed.

  Lemma bind_ret_l :
    bind F T (ret T a) = catid (F a).
  Proof.
    intros. unfold bind, Bind_Module.
    now rewrite (rmod_ret F T).
  Qed.

End module_bind.
