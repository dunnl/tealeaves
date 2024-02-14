From Tealeaves Require Export
  Functors.Writer.

Import Monoid.Notations.
Import Product.Notations.
Import Kleisli.Comonad.Notations.

#[local] Generalizable Variables E T.

(** * Decorated functors *)
(******************************************************************************)

(** ** <<Mapd>> operation *)
(******************************************************************************)
Class Mapd (E : Type) (T : Type -> Type) := mapd :
    forall (A B : Type), (E * A -> B) -> T A -> T B.

#[global] Arguments mapd {E}%type_scope {T}%function_scope
  {Mapd} {A B}%type_scope _%function_scope _.

(** ** "Kleisli" composition *)
(** Kleisli composition is [kc4] as for comonads *)
(******************************************************************************)

(** ** Typeclasses *)
(******************************************************************************)
Class DecoratedFunctor (E : Type) (T : Type -> Type) `{Mapd E T} :=
  { dfun_mapd1 : forall (A : Type),
      @mapd E T _ A A (extract) = @id (T A);
    dfun_mapd2 : forall (A B C : Type) (g : E * B -> C) (f : E * A -> B),
      @mapd E T _ B C g ∘ @mapd E T _ A B f = @mapd E T _ A C (g ⋆4 f);
  }.

(** ** Decoration-preserving natural transformations *)
(******************************************************************************)
Class DecoratedNatural
  (E : Type) (T1 T2 : Type -> Type)
  (ϕ : forall A : Type, T1 A -> T2 A)
  `{Mapd E T1} `{Mapd E T2} :=
  { dec_natural :
      forall (A B : Type) (f : E * A -> B), mapd f ∘ ϕ A = ϕ B ∘ mapd f;
  }.

(** * Derived instances *)
(******************************************************************************)
Section derived_instances.

  Definition Map_Mapd `{Mapd_inst : Mapd E T} : Map T :=
  fun (A B : Type) (f : A -> B) => @mapd E T _ A B (f ∘ extract).

  Class Compat_Map_Mapd
    `{Map_inst : Map T}
    `{Mapd_inst : Mapd E T} : Prop :=
    compat_map_mapd :
      @map T Map_inst = @map T (@Map_Mapd E T Mapd_inst).

  #[export] Instance Compat_Map_Mapd_Self
    `{Mapd E T} :
    Compat_Map_Mapd (Map_inst := Map_Mapd).
  Proof.
    reflexivity.
  Qed.

  Corollary map_to_mapd
    `{Compat_Map_Mapd E T} : forall (A B : Type) (f : A -> B),
      map f = mapd (f ∘ extract).
  Proof.
    rewrite compat_map_mapd.
    reflexivity.
  Qed.

End derived_instances.

Class DecoratedFunctorFull (E : Type) (T : Type -> Type)
  `{Mapd E T} `{Map T} :=
  { dfunf_df :> DecoratedFunctor E T;
    dfunf_map_compat :> Compat_Map_Mapd;
  }.

Definition DecoratedFunctorFull_DecoratedFunctor
  `{DecoratedFunctor E T} :
  `{DecoratedFunctorFull E T} :=
  {| dfunf_df := _ |}.

(** * Derived instances *)
(******************************************************************************)
Section derived_instances.

  Context
    `{DecoratedFunctor E T}
    `{Map_inst : Map T}
    `{! Compat_Map_Mapd}.

  (** ** Composition in special cases *)
  (******************************************************************************)
  Lemma map_mapd :
    forall (A B C : Type)
      (g : B -> C)
      (f : E * A -> B),
      map g ∘ mapd f = mapd (g ∘ f).
  Proof.
    intros.
    rewrite map_to_mapd.
    rewrite dfun_mapd2.
    rewrite kc4_04.
    reflexivity.
  Qed.

  Lemma mapd_map: forall (A B C : Type)
                    (g : E * B -> C)
                    (f : A -> B),
      mapd g ∘ map f = mapd (g ∘ map f).
  Proof.
    intros.
    rewrite map_to_mapd.
    rewrite dfun_mapd2.
    rewrite kc4_40.
    reflexivity.
  Qed.

  Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
      map g ∘ map f = map (F := T) (g ∘ f).
  Proof.
    intros.
    do 3 rewrite map_to_mapd.
    rewrite dfun_mapd2.
    rewrite kc4_00.
    reflexivity.
  Qed.

  Lemma map_id : forall (A : Type),
      map (@id A) = @id (T A).
  Proof.
    intros.
    rewrite map_to_mapd.
    unfold id, compose.
    rewrite dfun_mapd1.
    reflexivity.
  Qed.

  (** ** Typeclass instances *)
  (******************************************************************************)
  #[export] Instance: Classes.Functor.Functor T :=
    {| fun_map_id := map_id;
       fun_map_map := map_map;
    |}.

End derived_instances.
