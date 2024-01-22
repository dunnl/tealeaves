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

Class Bind (U T : Type -> Type) :=
  bind : forall (A B : Type), (A -> U B) -> T A -> T B.

#[global] Arguments ret {T}%function_scope {Return} {A}%type_scope.
#[global] Arguments bind {U} {T}%function_scope {Bind} {A B}%type_scope _%function_scope _.

(** ** Kleisli composition *)
(******************************************************************************)
Definition kc1 {T : Type -> Type} `{Return T} `{Bind T T}
  {A B C : Type} (g : B -> T C) (f : A -> T B) : (A -> T C) :=
  @bind T T _ B C g ∘ f.

#[local] Infix "⋆1" := (kc1) (at level 60) : tealeaves_scope.

(** ** Typeclass *)
(******************************************************************************)
Class Monad (T : Type -> Type)
  `{Return_inst : Return T}
  `{Bind_inst : Bind T T} :=
  { (* left unit law of the monoid *)
    kmon_bind0 : forall (A B : Type) (f : A -> T B),
      @bind T T _ A B f ∘ @ret T _ A = f;
    (* right unit law of the monoid *)
    kmon_bind1 : forall (A : Type),
      @bind T T _ A A (@ret T _ A) = @id (T A);
    (* associativity of the monoid *)
    kmon_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
      @bind T T _ B C g ∘ @bind T T _ A B f = @bind T T _ A C (g ⋆1 f);
  }.

Class MonadFull (T : Type -> Type)
  `{Return_inst : Return T}
  `{Map_inst : Map T}
  `{Bind_inst : Bind T T} :=
  { kmonf_kmon :> Monad T;
    kmonf_map_to_bind : forall `(f : A -> B),
      @map T Map_inst A B f = @bind T T Bind_inst A B (ret ∘ f);
  }.

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
Class RightModule  (T : Type -> Type) (U : Type -> Type)
  `{Return T} `{Bind T T} `{Bind T U} :=
  { kmod_monad :> Monad T;
    kmod_bind1 : forall (A : Type),
      @bind T U _ A A (@ret T _ A) = @id (U A);
    kmod_bind2 : forall (A B C : Type) (g : B -> T C) (f : A -> T B),
     @bind T U _ B C g ∘@bind T U _ A B f = @bind T U _ A C (g ⋆1 f);
  }.

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

(** * Derived instances *)
(******************************************************************************)
Section derived_instances.

  Context
    (T : Type -> Type)
    `{MonadFull T}.

  (** ** Composition between [bind] and [map] *)
  (******************************************************************************)
  Lemma bind_map : forall `(g : B -> T C) `(f : A -> B),
      bind g ∘ map f = bind (g ∘ f).
  Proof.
    intros. rewrite (kmonf_map_to_bind).
    rewrite (kmon_bind2). unfold kc1.
    reassociate <-. now rewrite (kmon_bind0).
  Qed.

  Corollary map_bind : forall `(g : B -> C) `(f : A -> T B),
      map g ∘ bind f = bind (map g ∘ f).
  Proof.
    intros. rewrite (kmonf_map_to_bind).
    now rewrite (kmon_bind2).
  Qed.

  (** ** Functor laws *)
  (******************************************************************************)
  Lemma map_id : forall (A : Type),
      map (@id A) = id.
  Proof.
    intros.
    rewrite (kmonf_map_to_bind).
    change (?f ∘ id) with f.
    now rewrite kmon_bind1.
  Qed.

  Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
      map g ∘ map f = map (g ∘ f).
  Proof.
    intros.
    rewrite 3(kmonf_map_to_bind).
    rewrite (kmon_bind2 (T := T)).
    unfold kc1.
    reassociate <- on left.
    now rewrite (kmon_bind0 (T := T)).
  Qed.

  #[export] Instance Functor_Monad : Functor T :=
    {| fun_map_id := map_id;
      fun_map_map := map_map;
    |}.

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
    rewrite (kmonf_map_to_bind).
    reflexivity.
  Qed.

  (** ** Other rules for Kleisli composition *)
  (******************************************************************************)
  Lemma kc1_asc1 : forall `(g : B -> C) `(h : C -> T D) `(f : A -> T B),
      (h ∘ g) ⋆1 f = h ⋆1 (map g ∘ f).
  Proof.
    intros. unfold kc1.
    reassociate <-.
    rewrite bind_map.
    reflexivity.
  Qed.

  Lemma kc1_asc2 : forall `(f : A -> B) `(g : B -> T C) `(h : C -> T D),
      h ⋆1 (g ∘ f) = (h ⋆1 g) ∘ f.
  Proof.
    intros. unfold kc1.
    reflexivity.
  Qed.

  (** ** Naturality of <<ret>> *)
  (******************************************************************************)
  #[export] Instance mon_ret_natural : Natural (@ret T _).
  Proof.
    constructor; try typeclasses eauto.
    intros.
    rewrite (kmonf_map_to_bind).
    rewrite (kmon_bind0).
    reflexivity.
  Qed.

End derived_instances.

(** ** Naturality of homomorphisms *)
(******************************************************************************)
#[export] Instance Natural_MonadHom  `{MonadFull T1} `{MonadFull T2} `{! MonadHom T1 T2 ϕ} : Natural ϕ.
Proof.
  constructor; try typeclasses eauto. intros.
  rewrite (kmonf_map_to_bind (T := T1)).
  rewrite (kmonf_map_to_bind (T := T2)).
  rewrite (kmon_hom_bind (T := T1) (U := T2)).
  reassociate <-.
  rewrite (kmon_hom_ret (T := T1) (U := T2)).
  reflexivity.
Qed.

#[local] Instance Map_Bind (T : Type -> Type)
  `{Return T} `{Bind T T} : Map T :=
  fun A B (f : A -> B) => @bind T T _ A B (@ret T _ B ∘ f).

Lemma map_to_bind `{Return T} `{Bind T T} : forall `(f : A -> B),
    @map T _ A B f = @bind T T _ A B (@ret T _ B ∘ f).
Proof.
  reflexivity.
Qed.

#[local] Instance MonadFull_Monad (T : Type -> Type)
  `{Monad T} : MonadFull T (Map_inst := Map_Bind T) :=
  {| kmonf_map_to_bind := ltac:(reflexivity);
  |}.

(** * Notations *)
(******************************************************************************)
Module Notations.
  Infix "⋆1" := (kc1) (at level 60) : tealeaves_scope.
End Notations.
