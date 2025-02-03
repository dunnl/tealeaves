From Tealeaves Require Export
  Tactics.Prelude
  Functors.Identity
  Classes.Categorical.Monad (Return, ret).

Import Functor.Notations.

#[local] Generalizable Variable T.

(** * Monads *)
(**********************************************************************)

(** ** Operations *)
(**********************************************************************)
Class Bind (T U: Type -> Type) :=
  bind: forall (A B: Type), (A -> T B) -> U A -> U B.

#[global] Arguments bind {T} {U}%function_scope {Bind}
  {A B}%type_scope _%function_scope _.

(** ** Kleisli Composition *)
(**********************************************************************)
Definition kc {T: Type -> Type} `{Return T} `{Bind T T}
  {A B C: Type} (g: B -> T C) (f: A -> T B): (A -> T C) :=
  @bind T T _ B C g ∘ f.

#[local] Infix "⋆" := (kc) (at level 60): tealeaves_scope.

(** ** Typeclasses *)
(**********************************************************************)
Class RightPreModule
  (T U: Type -> Type)
  `{Return T} `{Bind T T} `{Bind T U} :=
  { kmod_bind1: forall (A: Type),
      bind (U := U) ret = @id (U A);
    kmod_bind2: forall (A B C: Type) (g: B -> T C) (f: A -> T B),
      bind (U := U) g ∘ bind f = bind (g ⋆ f);
  }.

Class Monad (T: Type -> Type)
  `{Return_T: Return T}
  `{Bind_TT: Bind T T} :=
  { kmon_bind0: forall (A B: Type) (f: A -> T B),
      bind f ∘ ret = f;
    kmon_premod :> RightPreModule T T;
  }.

Class RightModule (T: Type -> Type) (U: Type -> Type)
  `{Return_T: Return T}
  `{Bind_TT: Bind T T}
  `{Bind_TU: Bind T U} :=
  { kmod_monad :> Monad T;
    kmod_premod :> RightPreModule T U;
  }.

#[local] Instance RightModule_Monad
  (T: Type -> Type)
  `{Monad_T: Monad T}: RightModule T T :=
  {| kmod_monad := Monad_T;
  |}.

(* right unit law of the monoid *)
Lemma kmon_bind1 `{Monad T}: forall (A: Type),
    @bind T T _ A A (@ret T _ A) = @id (T A).
Proof.
  apply kmod_bind1.
Qed.

(* associativity of the monoid *)
Lemma kmon_bind2 `{Monad T}:
  forall (A B C: Type) (g: B -> T C) (f: A -> T B),
    @bind T T _ B C g ∘ @bind T T _ A B f = @bind T T _ A C (g ⋆ f).
Proof.
  apply kmod_bind2.
Qed.

(** ** Kleisli Category Laws *)
(**********************************************************************)
Section Monad_Kleisli_category.

  Context
    `{Monad T}.

  #[local] Generalizable Variables A B C D.

  (** *** Left identity law *)
  Theorem kleisli_id_l: forall `(f: A -> T B),
      (@ret T _ B) ⋆ f = f.
  Proof.
    intros. unfold kc.
    rewrite kmon_bind1.
    reflexivity.
  Qed.

  (** *** Right identity law *)
  Theorem kleisli_id_r: forall `(g: B -> T C),
      g ⋆ (@ret T _ B) = g.
  Proof.
    intros. unfold kc.
    rewrite kmon_bind0.
    reflexivity.
  Qed.

  (** *** Associativity law *)
  Theorem kleisli_assoc:
    forall `(h: C -> T D) `(g: B -> T C) `(f: A -> T B),
      h ⋆ (g ⋆ f) = (h ⋆ g) ⋆ f.
  Proof.
    intros. unfold kc at 3.
    rewrite <- kmon_bind2.
    reflexivity.
  Qed.

End Monad_Kleisli_category.

(** ** Monad Homomorphisms *)
(**********************************************************************)
Class MonadHom (T U: Type -> Type)
  `{Return T} `{Bind T T}
  `{Return U} `{Bind U U}
  (ϕ: forall (A: Type), T A -> U A) :=
  { kmon_hom_bind: forall (A B: Type) (f: A -> T B),
      ϕ B ∘ bind f = bind (ϕ B ∘ f) ∘ ϕ A;
    kmon_hom_ret: forall (A: Type),
      ϕ A ∘ ret (T := T) = ret;
  }.

Class RightModuleHom (T U V: Type -> Type)
  `{Return T} `{Bind T U} `{Bind T V}
  (ϕ: forall (A: Type), U A -> V A) :=
  { kmod_hom_bind: forall (A B: Type) (f: A -> T B),
      ϕ B ∘ @bind T U _ A B f = @bind T V _ A B f ∘ ϕ A;
  }.

Class ParallelRightModuleHom (T T' U U': Type -> Type)
  `{Return T} `{Bind T U} `{Bind T' U'}
  (ψ: forall (A: Type), T A -> T' A)
  (ϕ: forall (A: Type), U A -> U' A) :=
  { kmodpar_hom_bind: forall (A B: Type) (f: A -> T B),
      ϕ B ∘ @bind T U _ A B f = @bind T' U' _ A B (ψ B ∘ f) ∘ ϕ A;
  }.


(** * Derived Structures *)
(**********************************************************************)

(** ** Derived Operations *)
(**********************************************************************)
Module DerivedOperations.

  #[export] Instance Map_Bind (T U: Type -> Type)
    `{Return_T: Return T}
    `{Bind_TU: Bind T U}: Map U :=
  fun A B (f: A -> B) => @bind T U Bind_TU A B (@ret T Return_T B ∘ f).

End DerivedOperations.

Class Compat_Map_Bind
  (T: Type -> Type)
  (U: Type -> Type)
  `{Return_T: Return T}
  `{Map_U: Map U}
  `{Bind_TU: Bind T U}: Prop :=
  compat_map_bind:
    @Map_U = @DerivedOperations.Map_Bind T U Return_T Bind_TU.

#[export] Instance Compat_Map_Bind_Monad (T U: Type -> Type)
  `{Return_T: Return T} `{Bind_TU: Bind T U}:
  @Compat_Map_Bind T U Return_T
    (@DerivedOperations.Map_Bind T U Return_T Bind_TU) Bind_TU.
Proof.
  reflexivity.
Qed.

Lemma map_to_bind {T U: Type -> Type}
  `{Return_T: Return T}
  `{Map_U: Map U}
  `{Bind_TU: Bind T U}
  `{! Compat_Map_Bind T U}: forall {A B: Type} (f: A -> B),
    @map U Map_U A B f = @bind T U Bind_TU A B (@ret T Return_T B ∘ f).
Proof.
  rewrite compat_map_bind.
  reflexivity.
Qed.

(** ** Derived Kleisli Composition laws *)
(**********************************************************************)
Section derived_kleisli_composition_laws.

  Context
    `{Monad T} `{Map T} `{! Compat_Map_Bind T T}.

  #[local] Generalizable Variables A B C D.

  (** *** Special cases for Kleisli composition *)
  (********************************************************************)
  Lemma kc_00: forall `(g: B -> C) `(f: A -> B),
      (ret ∘ g) ⋆ (ret ∘ f) = ret ∘ (g ∘ f).
  Proof.
    intros. unfold kc.
    reassociate <-.
    rewrite kmon_bind0.
    reflexivity.
  Qed.

  Lemma kc_10: forall `(g: B -> T C) `(f: A -> B),
      g ⋆ (ret ∘ f) = g ∘ f.
  Proof.
    intros. unfold kc.
    reassociate <-.
    rewrite kmon_bind0.
    reflexivity.
  Qed.

  Lemma kc_01: forall `(g: B -> C) `(f: A -> T B),
      (ret ∘ g) ⋆ f = map g ∘ f.
  Proof.
    intros. unfold kc.
    rewrite map_to_bind.
    reflexivity.
  Qed.

  (** *** Other rules for Kleisli composition *)
  (********************************************************************)
  Lemma kc_asc1: forall `(g: B -> C) `(h: C -> T D) `(f: A -> T B),
      (h ∘ g) ⋆ f = h ⋆ (map g ∘ f).
  Proof.
    intros. unfold kc.
    reassociate <-.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    rewrite kc_10.
    reflexivity.
  Qed.

  Lemma kc_asc2: forall `(f: A -> B) `(g: B -> T C) `(h: C -> T D),
      h ⋆ (g ∘ f) = (h ⋆ g) ∘ f.
  Proof.
    intros. unfold kc.
    reflexivity.
  Qed.

End derived_kleisli_composition_laws.

(** ** Derived Composition Laws *)
(**********************************************************************)
Section derived_instances.

  #[local] Generalizable Variables U A B C.

  Context
    `{RightModule_TU: RightPreModule T U}
    `{Map_U: Map U}
    `{Map_T: Map T}
    `{! Compat_Map_Bind T U}
    `{! Compat_Map_Bind T T}
    `{Monad_T: ! Monad T}.

  (** *** Composition between [bind] and [map] *)
  (********************************************************************)
  Lemma bind_map: forall `(g: B -> T C) `(f: A -> B),
      bind (U:= U) g ∘ map f = bind (g ∘ f).
  Proof.
    intros.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    rewrite kc_10.
    reflexivity.
  Qed.

  Corollary map_bind: forall `(g: B -> C) `(f: A -> T B),
      map g ∘ bind (U := U) f = bind (map g ∘ f).
  Proof.
    intros.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    rewrite map_to_bind.
    reflexivity.
  Qed.

  (** *** Functor laws *)
  (********************************************************************)
  Lemma map_id: forall (A: Type),
      map (F := U) (@id A) = id.
  Proof.
    intros.
    rewrite map_to_bind.
    change (?f ∘ id) with f.
    rewrite kmod_bind1.
    reflexivity.
  Qed.

  Lemma map_map: forall (A B C: Type) (f: A -> B) (g: B -> C),
      map g ∘ map f = map (F := U) (g ∘ f).
  Proof.
    intros.
    rewrite map_to_bind.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    rewrite kc_00.
    rewrite map_to_bind.
    reflexivity.
  Qed.

End derived_instances.

(** ** Derived Typeclass Instances *)
(**********************************************************************)
Module DerivedInstances.
  #[local] Generalizable Variables U.

  #[export] Instance Functor_RightModule
    `{RightModule_TU: RightModule T U}
    `{Map_U: Map U}
    `{! Compat_Map_Bind T U}:
    Functor U (Map_F := Map_U) :=
    {| fun_map_id := map_id;
       fun_map_map := map_map;
    |}.

  #[export] Instance Functor_Monad
    `{Monad_T: Monad T}
    `{Map_T: Map T}
    `{! Compat_Map_Bind T T}:
    Functor T := Functor_RightModule.

  Include DerivedOperations.

End DerivedInstances.

(** ** Naturality Properties *)
(**********************************************************************)

(** *** Return *)
#[export] Instance Natural_Return
  `{Monad_T: Monad T} `{Map_T: Map T}
  `{! Compat_Map_Bind T T}:
  Natural (@ret T Return_T).
Proof.
  constructor.
  - apply Functor_I.
  - apply DerivedInstances.Functor_Monad.
  - intros.
    rewrite map_to_bind.
    rewrite kmon_bind0.
    unfold_ops @Map_I.
    reflexivity.
Qed.


(** *** Monad Homomorphisms *)
#[export] Instance Natural_MonadHom
  `{Monad T1} `{Monad T2}
  `{Map T1} `{Map T2}
  `{! Compat_Map_Bind T1 T1}
  `{! Compat_Map_Bind T2 T2}
  (ϕ: forall (A: Type), T1 A -> T2 A)
  `{! MonadHom T1 T2 ϕ}: Natural ϕ.
Proof.
  constructor.
  - apply DerivedInstances.Functor_Monad.
  - apply DerivedInstances.Functor_Monad.
  - intros.
    rewrite map_to_bind.
    rewrite <- (kmon_hom_ret (T := T1) (U := T2)) at 1.
    rewrite map_to_bind.
    rewrite (kmon_hom_bind (T := T1) (U := T2)).
    reflexivity.
Qed.

(** * Notations *)
(**********************************************************************)
Module Notations.
  Infix "⋆" := (kc) (at level 60): tealeaves_scope.
End Notations.
