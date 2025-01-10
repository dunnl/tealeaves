From Tealeaves Require Export
  Classes.Kleisli.Monad.

#[local] Generalizable Variables F G A B C D W T U ϕ.
Import Monad.Notations.
Import Functor.Notations.

(** * Derived instances *)
(******************************************************************************)

(** ** Map operation *)
(******************************************************************************)
#[export] Instance Map_Bind (T U: Type -> Type)
  `{Return T} `{Bind T U}: Map U :=
  fun A B (f: A -> B) => @bind T U _ A B (@ret T _ B ∘ f).

Class Compat_Map_Bind
  (U: Type -> Type)
  (T: Type -> Type)
  `{Map_U: Map U}
  `{Return_T: Return T}
  `{Bind_U: Bind T U}: Prop :=
  compat_map_bind: @Map_U = @Map_Bind T U Return_T Bind_U.

#[export] Instance Compat_Map_Bind_Self
  `{Return T} `{Bind T U}:
  @Compat_Map_Bind U T (@Map_Bind T U _ _) _ _.
Proof.
  reflexivity.
Qed.

Lemma map_to_bind
  `{Return T} `{Bind T U} `{Map U}
  `{! Compat_Map_Bind U T}: forall `(f: A -> B),
    @map U _ A B f = @bind T U _ A B (@ret T _ B ∘ f).
Proof.
  rewrite compat_map_bind.
  reflexivity.
Qed.

(** ** Full typeclasses *)
(******************************************************************************)
Class MonadFull (T: Type -> Type)
  `{Return_T: Return T}
  `{Map_T: Map T}
  `{Bind_T: Bind T T} :=
  { kmonf_kmon:> Monad T;
    kmonf_map_to_bind:> Compat_Map_Bind T T;
  }.

Class RightModuleFull (T: Type -> Type) (U: Type -> Type)
  `{Return_T: Return T}
  `{Bind_T: Bind T T}
  `{Bind_TU: Bind T U}
  `{Map_T: Map T}
  `{Map_U: Map U}
  :=
  { kmodf_mod :> RightModule T U;
    kmodf_compat :> Compat_Map_Bind U T;
    kmodf_monad :> MonadFull T;
  }.

Section instances.

  #[local] Instance MonadFull_Monad (T: Type -> Type)
    `{Monad_T: Monad T} :
  MonadFull T (Map_T := Map_Bind T T) :=
  {| kmonf_map_to_bind := _;
  |}.

  #[local] Instance RightModule_Monad (T: Type -> Type)
    `{Monad_T: Monad T} :
    RightModule T T :=
    {| kmod_monad := _;
    |}.

  #[local] Instance RightModuleFull_RightModule
    (T U: Type -> Type)
    `{RightModule_TU: RightModule T U}:
    RightModuleFull T U
      (Map_T := Map_Bind T T)
      (Map_U := Map_Bind T U) :=
    {| kmodf_monad :=
        MonadFull_Monad T (Monad_T := kmod_monad)
    |}.

End instances.

(** * Kleisli category laws *)
(******************************************************************************)
Section Monad_kleisli_category.

  Context
    `{Monad T}.

  (** ** Left identity law *)
  (******************************************************************************)
  Theorem kleisli_id_l: forall `(f: A -> T B),
      (@ret T _ B) ⋆1 f = f.
  Proof.
    intros. unfold kc1. now rewrite (@kmon_bind1 T).
  Qed.

  (** ** Right identity law *)
  (******************************************************************************)
  Theorem kleisli_id_r: forall `(g: B -> T C),
      g ⋆1 (@ret T _ B) = g.
  Proof.
    intros. unfold kc1. now rewrite (@kmon_bind0 T).
  Qed.

  (** ** Associativity law *)
  (******************************************************************************)
  Theorem kleisli_assoc: forall `(h: C -> T D) `(g: B -> T C) `(f: A -> T B),
      h ⋆1 (g ⋆1 f) = (h ⋆1 g) ⋆1 f.
  Proof.
    intros. unfold kc1 at 3.
    now rewrite <- (@kmon_bind2 T).
  Qed.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Lemma kc1_00: forall `(g: B -> C) `(f: A -> B),
      (ret ∘ g) ⋆1 (ret ∘ f) = ret ∘ (g ∘ f).
  Proof.
    intros. unfold kc1.
    reassociate <-.
    now rewrite (kmon_bind0).
  Qed.

  Lemma kc1_10: forall `(g: B -> T C) `(f: A -> B),
      g ⋆1 (ret ∘ f) = g ∘ f.
  Proof.
    intros. unfold kc1.
    reassociate <-.
    now rewrite (kmon_bind0).
  Qed.

  Lemma kc1_01: forall `(g: B -> C) `(f: A -> T B),
      (ret ∘ g) ⋆1 f = map g ∘ f.
  Proof.
    intros. unfold kc1.
    rewrite map_to_bind.
    reflexivity.
  Qed.

  (** ** Other rules for Kleisli composition *)
  (******************************************************************************)
  Lemma kc1_asc1: forall `(g: B -> C) `(h: C -> T D) `(f: A -> T B),
      (h ∘ g) ⋆1 f = h ⋆1 (map g ∘ f).
  Proof.
    intros. unfold kc1.
    reassociate <-.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    rewrite kc1_10.
    reflexivity.
  Qed.

  Lemma kc1_asc2: forall `(f: A -> B) `(g: B -> T C) `(h: C -> T D),
      h ⋆1 (g ∘ f) = (h ⋆1 g) ∘ f.
  Proof.
    intros. unfold kc1.
    reflexivity.
  Qed.

End Monad_kleisli_category.

(** * Derived functor instance *)
(******************************************************************************)
Section derived_instances.

  Context
    `{RightModule_TU: RightModule T U}
    `{map_U: Map U} `{map_T: Map T}
    `{! Compat_Map_Bind U T}
    `{! Compat_Map_Bind T T}.

  (** ** Composition between [bind] and [map] *)
  (******************************************************************************)
  Lemma bind_map: forall `(g: B -> T C) `(f: A -> B),
      bind (U:= U) g ∘ map f = bind (g ∘ f).
  Proof.
    intros.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    rewrite kc1_10.
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
    rewrite map_to_bind.
    rewrite map_to_bind.
    rewrite kmod_bind2.
    rewrite kc1_00.
    rewrite map_to_bind.
    reflexivity.
  Qed.

  #[export] Instance Functor_RightModule: Functor U :=
    {| fun_map_id := map_id;
      fun_map_map := map_map;
    |}.

End derived_instances.

#[export] Instance Functor_Monad `{Monad T} `{Map_T: Map T}
  `{! Compat_Map_Bind T T}: Functor T (map_instance := Map_T) :=
  @Functor_RightModule T T _ _ _ (RightModule_Monad T) _ _.

#[export] Instance mon_ret_natural `{Monad T}:
  Natural (@ret T _).
Proof.
  constructor; try typeclasses eauto.
  intros.
  rewrite map_to_bind.
  rewrite kmon_bind0.
  unfold_ops @Map_I.
  reflexivity.
Qed.

(** * Naturality of homomorphisms *)
(******************************************************************************)
#[export] Instance Natural_MonadHom
  `{Monad T1} `{Monad T2}
  `{Map T1} `{Map T2}
  `{! MonadFull T1 }
  `{! MonadFull T2 }
  `{! MonadHom T1 T2 ϕ}: Natural ϕ.
Proof.
  constructor; try typeclasses eauto.
  intros.
  rewrite map_to_bind.
  rewrite <- (kmon_hom_ret (T := T1) (U := T2)) at 1.
  rewrite map_to_bind.
  rewrite (kmon_hom_bind (T := T1) (U := T2)).
  reflexivity.
Qed.
