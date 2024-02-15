From Tealeaves Require Export
  Tactics.Prelude
  Classes.Functor
  Functors.Identity.

#[local] Generalizable Variables F G A B C D W T U ϕ.
Import Functor.Notations.

(** * Monads *)
(******************************************************************************)

(** ** Operations *)
(******************************************************************************)
Class Return (T : Type -> Type) :=
  ret : (fun A => A) ⇒ T.

Class Bind (T U : Type -> Type) :=
  bind : forall (A B : Type), (A -> T B) -> U A -> U B.

#[global] Arguments ret {T}%function_scope {Return} {A}%type_scope.
#[global] Arguments bind {T} {U}%function_scope {Bind} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc1 {T : Type -> Type} `{Return T} `{Bind T T}
  {A B C : Type} (g : B -> T C) (f : A -> T B) : (A -> T C) :=
  @bind T T _ B C g ∘ f.

#[local] Infix "⋆1" := (kc1) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class RightPreModule
  (T U : Type -> Type)
  `{Return T} `{Bind T T} `{Bind T U} :=
  { kmod_bind1 : forall (A : Type),
      @bind T U _ A A (@ret T _ A) = @id (U A);
    kmod_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
      @bind T U _ B C g ∘ @bind T U _ A B f = @bind T U _ A C (g ⋆1 f);
  }.

Class Monad (T : Type -> Type)
  `{Return_inst : Return T}
  `{Bind_inst : Bind T T} :=
  { (* left unit law of the monoid *)
    kmon_bind0 : forall (A B : Type) (f : A -> T B),
      @bind T T _ A B f ∘ @ret T _ A = f;
    kmon_premod :> RightPreModule T T;
  }.

(* right unit law of the monoid *)
Lemma kmon_bind1 `{Monad T} : forall (A : Type),
    @bind T T _ A A (@ret T _ A) = @id (T A).
Proof.
  apply kmod_bind1.
Qed.

(* associativity of the monoid *)
Lemma kmon_bind2 `{Monad T} : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
    @bind T T _ B C g ∘ @bind T T _ A B f = @bind T T _ A C (g ⋆1 f).
Proof.
  apply kmod_bind2.
Qed.

(** ** Homomorphisms *)
(******************************************************************************)
Class MonadHom (T U : Type -> Type)
  `{Return T} `{Bind T T}
  `{Return U} `{Bind U U}
  (ϕ : forall (A : Type), T A -> U A) :=
  { kmon_hom_bind : forall (A B : Type) (f : A -> T B),
      ϕ B ∘ @bind T T _ A B f = @bind U U _ A B (ϕ B ∘ f) ∘ ϕ A;
    kmon_hom_ret : forall (A : Type),
      ϕ A ∘ @ret T _ A = @ret U _ A;
  }.

(** ** Right modules *)
(******************************************************************************)
Class RightModule (T : Type -> Type) (U : Type -> Type)
  `{Return T} `{Bind T T} `{Bind T U} :=
  { kmod_monad :> Monad T;
    kmod_premod :> RightPreModule T U;
  }.

(** ** Homomorphisms *)
(******************************************************************************)
Class RightModuleHom (T U V : Type -> Type)
  `{Return T} `{Bind T U} `{Bind T V}
  (ϕ : forall (A : Type), U A -> V A) :=
  { kmod_hom_bind : forall (A B : Type) (f : A -> T B),
      ϕ B ∘ @bind T U _ A B f = @bind T V _ A B f ∘ ϕ A;
  }.

Class ParallelRightModuleHom (T T' U V : Type -> Type)
  `{Return T} `{Bind T U} `{Bind T' V}
  (ψ : forall (A : Type), T A -> T' A)
  (ϕ : forall (A : Type), U A -> V A) :=
  { kmodpar_hom_bind : forall (A B : Type) (f : A -> T B),
      ϕ B ∘ @bind T U _ A B f = @bind T' V _ A B (ψ B ∘ f) ∘ ϕ A;
  }.

(** * Derived instances *)
(******************************************************************************)
Section Map_Bind.
  #[local] Instance Map_Bind {T U}
    `{Return T} `{Bind T U} : Map U :=
  fun A B (f : A -> B) => @bind T U _ A B (@ret T _ B ∘ f).
End Map_Bind.

Class Compat_Map_Bind
  (U : Type -> Type)
  (T : Type -> Type)
  `{H_map : Map U}
  `{H_return : Return T}
  `{H_bind : Bind T U} : Prop :=
  compat_map_bind :
    @map U H_map = @map U (@Map_Bind T U H_return H_bind).

#[export] Instance Compat_Map_Bind_Self
  `{Return T} `{Bind T U} :
  @Compat_Map_Bind U T (@Map_Bind T U _ _) _ _.
Proof.
  reflexivity.
Qed.

Lemma map_to_bind
  `{Return T} `{Bind T U} `{Map U}
  `{! Compat_Map_Bind U T} : forall `(f : A -> B),
    @map U _ A B f = @bind T U _ A B (@ret T _ B ∘ f).
Proof.
  rewrite compat_map_bind.
  reflexivity.
Qed.

Class MonadFull (T : Type -> Type)
  `{Return_inst : Return T}
  `{Map_inst : Map T}
  `{Bind_inst : Bind T T} :=
  { kmonf_kmon :> Monad T;
    kmonf_map_to_bind :> Compat_Map_Bind T T;
  }.

Class RightModuleFull (T : Type -> Type) (U : Type -> Type)
  `{Return_inst : Return T}
  `{Bind_T_inst : Bind T T}
  `{Bind_U_inst : Bind T U}
  `{Map_T_inst : Map T}
  `{Map_U_inst : Map U}
  :=
  { kmodf_mod :> RightModule T U;
    kmodf_compat :> Compat_Map_Bind U T;
    kmodf_monad :> MonadFull T;
  }.

Section instances.

  #[local] Instance MonadFull_Monad (T : Type -> Type)
    `{Monad_inst : Monad T} :
  MonadFull T (Map_inst := Map_Bind) :=
  {| kmonf_map_to_bind := _;
  |}.

  #[local] Instance RightModule_Monad (T : Type -> Type)
    `{Monad_inst : Monad T} :
    RightModule T T :=
    {| kmod_monad := _;
    |}.

  #[local] Instance RightModuleFull_RightModule
    (T U : Type -> Type)
    `{RightMod_inst : RightModule T U} :
    RightModuleFull T U
      (Map_T_inst := Map_Bind)
      (Map_U_inst := Map_Bind) :=
    {| kmodf_monad :=
        MonadFull_Monad T (Monad_inst := kmod_monad)
    |}.

End instances.

(** * Kleisli category laws *)
(******************************************************************************)
Section Monad_kleisli_category.

  Context
    (T : Type -> Type)
    `{Monad T}
    {A B C D : Type}.

  (** ** Left identity law *)
  (******************************************************************************)
  Theorem kleisli_id_l : forall (f : A -> T B),
      (@ret T _ B) ⋆1 f = f.
  Proof.
    intros. unfold kc1. now rewrite (@kmon_bind1 T).
  Qed.

  (** ** Right identity law *)
  (******************************************************************************)
  Theorem kleisli_id_r : forall (g : B -> T C),
      g ⋆1 (@ret T _ B) = g.
  Proof.
    intros. unfold kc1. now rewrite (@kmon_bind0 T).
  Qed.

  (** ** Associativity law *)
  (******************************************************************************)
  Theorem kleisli_assoc : forall (h : C -> T D) (g : B -> T C) (f : A -> T B),
      h ⋆1 (g ⋆1 f) = (h ⋆1 g) ⋆1 f.
  Proof.
    intros. unfold kc1 at 3.
    now rewrite <- (@kmon_bind2 T).
  Qed.

End Monad_kleisli_category.

(** * Derived functor instance *)
(******************************************************************************)
Section derived_instances.

  Context
    `{module : RightModule T U}
    `{map_U : Map U} `{map_T : Map T}
    `{! Compat_Map_Bind U T}
    `{! Compat_Map_Bind T T}.

  (** ** Composition between [bind] and [map] *)
  (******************************************************************************)
  Lemma bind_map : forall `(g : B -> T C) `(f : A -> B),
      bind (U := U) g ∘ map f = bind (g ∘ f).
  Proof.
    intros.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    unfold kc1.
    reassociate <-.
    rewrite kmon_bind0.
    reflexivity.
  Qed.

  Corollary map_bind : forall `(g : B -> C) `(f : A -> T B),
      map g ∘ bind (U := U) f = bind (map g ∘ f).
  Proof.
    intros.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    rewrite map_to_bind.
    reflexivity.
  Qed.

  (** ** Functor laws *)
  (******************************************************************************)
  Lemma map_id : forall (A : Type),
      map (F := U) (@id A) = id.
  Proof.
    intros.
    rewrite map_to_bind.
    change (?f ∘ id) with f.
    rewrite kmod_bind1.
    reflexivity.
  Qed.

  Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
      map g ∘ map f = map (F := U) (g ∘ f).
  Proof.
    intros.
    rewrite 3(map_to_bind).
    rewrite kmod_bind2.
    unfold kc1.
    reassociate <- on left.
    rewrite kmon_bind0.
    reflexivity.
  Qed.

  #[export] Instance Functor_RightModule : Functor U :=
    {| fun_map_id := map_id;
      fun_map_map := map_map;
    |}.

End derived_instances.

(** * Other theory *)
(******************************************************************************)
Section theory.

  Context
    `{Monad T}
     `{Map_inst : Map T}
    `{! Compat_Map_Bind T T}.

  #[export] Instance Functor_Monad : Functor T :=
    @Functor_RightModule T T _ _ _
      (RightModule_Monad T) _ _.

  (** ** Naturality of <<ret>> *)
  (******************************************************************************)
  #[export] Instance mon_ret_natural :
    Natural (@ret T _).
  Proof.
    constructor; try typeclasses eauto.
    intros.
    rewrite map_to_bind.
    rewrite kmon_bind0.
    reflexivity.
  Qed.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Lemma kc1_00 : forall `(g : B -> C) `(f : A -> B),
      (ret ∘ g) ⋆1 (ret ∘ f) = ret ∘ (g ∘ f).
  Proof.
    intros. unfold kc1.
    reassociate <-. now rewrite (kmon_bind0).
  Qed.

  Lemma kc1_10 : forall `(g : B -> T C) `(f : A -> B),
      g ⋆1 (ret ∘ f) = g ∘ f.
  Proof.
    intros. unfold kc1.
    reassociate <-. now rewrite (kmon_bind0).
  Qed.

  Lemma kc1_01 : forall `(g : B -> C) `(f : A -> T B),
      (ret ∘ g) ⋆1 f = map g ∘ f.
  Proof.
    intros. unfold kc1.
    rewrite map_to_bind.
    reflexivity.
  Qed.

  (** ** Other rules for Kleisli composition *)
  (******************************************************************************)
  Lemma kc1_asc1 : forall `(g : B -> C) `(h : C -> T D) `(f : A -> T B),
      (h ∘ g) ⋆1 f = h ⋆1 (map g ∘ f).
  Proof.
    intros. unfold kc1.
    reassociate <-.
    rewrite (bind_map (module := RightModule_Monad T)).
    reflexivity.
  Qed.

  Lemma kc1_asc2 : forall `(f : A -> B) `(g : B -> T C) `(h : C -> T D),
      h ⋆1 (g ∘ f) = (h ⋆1 g) ∘ f.
  Proof.
    intros. unfold kc1.
    reflexivity.
  Qed.

End theory.

(** * Naturality of homomorphisms *)
(******************************************************************************)
#[export] Instance Natural_MonadHom
  `{Monad T1} `{Monad T2}
  `{Map T1} `{Map T2}
  `{! MonadFull T1 }
  `{! MonadFull T2 }
  `{! MonadHom T1 T2 ϕ} : Natural ϕ.
Proof.
  constructor; try typeclasses eauto.
  intros.
  rewrite map_to_bind.
  rewrite map_to_bind.
  rewrite (kmon_hom_bind (T := T1) (U := T2)).
  reassociate <- on right.
  rewrite (kmon_hom_ret (T := T1) (U := T2)).
  reflexivity.
Qed.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆1" := (kc1) (at level 60) : tealeaves_scope.
End Notations.
