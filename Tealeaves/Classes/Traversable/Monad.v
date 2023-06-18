From Tealeaves Require Export
  Classes.Monoid
  Classes.Applicative
  Classes.Monad
  Classes.Traversable.Functor.

Import Monad.Notations.
Import Traversable.Functor.Notations.

#[local] Generalizable Variables T G A B C D ϕ M.

#[local] Arguments map F%function_scope {Map} (A B)%type_scope f%function_scope _.

(** * Traversable monad *)
(******************************************************************************)
Section operations.

  Context
    (M : Type)
    (T : Type -> Type)
    (U : Type -> Type).

    Class Bindt := bindt :
        forall (G : Type -> Type) `{Map G} `{Pure G} `{Mult G}
          (A B : Type),
          (A -> G (T B)) -> U A -> G (U B).

End operations.

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
    { ktm_bindt0 : forall (G : Type -> Type) `{Applicative G} (A B : Type) (f : A -> G (T B)),
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

Section kc3_special_cases.

  Context
    (T : Type -> Type)
    `{TraversableMonad T}.

  Lemma kc3_22 : forall `{Applicative G1} `{Applicative G2} `(g : B -> G2 C) `(f : A -> G1 B),
      (map G2 C (T C) (ret T C) ∘ g) ⋆3 (map G1 B (T B) (ret T B) ∘ f) =
        map (G1 ∘ G2) C (T C) (ret T C) ∘ map G1 B (G2 C) g ∘ f.
  Proof.
    intros.
    unfold kc3.
    reassociate <-.
    rewrite (fun_map_map G1).
    unfold_ops @Map_compose.
    unfold_compose_in_compose.
    rewrite (fun_map_map G1).
    rewrite (ktm_bindt0 T G2).
    reflexivity.
  Qed.

  Corollary kc3_00 : forall `(g : B -> C) `(f : A -> B),
      (ret T C ∘ g) ⋆3 (ret T B ∘ f) = ret T C ∘ (g ∘ f).
  Proof.
    intros.
    unfold kc3.
    change (map (fun A => A) _ _ ?f) with f.
    reassociate <-.
    rewrite (ktm_bindt0 T (fun A => A)).
    reflexivity.
  Qed.

  Lemma kc3_30 : forall `{Applicative G2} `(g : B -> G2 (T C)) `(f : A -> B),
      g ⋆3 (ret T B ∘ f) = g ∘ f.
  Proof.
    intros. unfold kc3.
    reassociate <- on left.
    change (map (fun A => A) _ _ ?g) with g.
    now rewrite (ktm_bindt0 T).
  Qed.

End kc3_special_cases.

(** * Derived instances *)
(******************************************************************************)
Module DerivedInstances.

  Section operations.

    Context
      (T : Type -> Type)
      `{Bindt T T}
      `{Return T}.

    #[export] Instance Map_Bindt : Map T :=
      fun (A B : Type) (f : A -> B) => bindt T T (fun A => A) A B (ret T B ∘ f).
    #[export] Instance Bind_Bindt: Bind T T :=
      fun A B f => bindt T T (fun A => A) A B f.
    #[export] Instance Traverse_Bindt: Traverse T :=
      fun G _ _ _ A B f => bindt T T G A B (map G _ _ (ret T B) ∘ f).

  End operations.

  Section special_cases.

    Context
      (W : Type)
      (T : Type -> Type)
      `{Return T}
      `{Bindt T T}
      (G : Type -> Type)
      `{Applicative G}.

    (** *** Rewriting rules for special cases of <<bindt>> *)
    (******************************************************************************)
    Lemma bind_to_bindt `(f : A -> T B):
      bind T T A B f = bindt T T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    Lemma traverse_to_bindt `(f : A -> G B):
      traverse T G A B f = bindt T T G A B (map G B (T B) (ret T B) ∘ f).
    Proof.
      reflexivity.
    Qed.

    Lemma map_to_bindt `(f : A -> B):
      map T A B f = bindt T T (fun A => A) A B (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<traverse>> *)
    (******************************************************************************)
    Lemma map_to_traverse `(f : A -> B):
      map T A B f = traverse T (fun A => A) A B f.
    Proof.
      reflexivity.
    Qed.

    (** *** Rewriting rules for special cases of <<bind>> *)
    (******************************************************************************)
    Lemma map_to_bind `(f : A -> B):
      map T A B f = bind T T A B (ret T B ∘ f).
    Proof.
      reflexivity.
    Qed.

  End special_cases.

  (** ** Special cases for Kleisli composition *)
  (******************************************************************************)
  Section kc3_special_cases.

    Context
      (T : Type -> Type)
      `{TraversableMonad T}
      `{Applicative G3}
      `{Applicative G2}
      `{Applicative G1}.
    (*
    t/m:
    00 0 no t or m
    01 1 no m
    10 2 no t
    11 3 everything
     *)

    Lemma kc3_22 : forall `(g : B -> G2 C) `(f : A -> G1 B),
        (map G2 C (T C) (ret T C) ∘ g) ⋆3 (map G1 B (T B) (ret T B) ∘ f) =
          map (G1 ∘ G2) C (T C) (ret T C) ∘ (map G1 B (G2 C) g ∘ f).
    Proof.
      intros. unfold kc3.
      reassociate <-.
      rewrite (fun_map_map G1).
      reassociate <-.
      unfold_ops @Map_compose.
      unfold_compose_in_compose.
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt0 T G2).
      reflexivity.
    Qed.

    Lemma kc3_11 : forall `(g : B -> T C) `(f : A -> T B),
        kc3 T (fun A => A) (fun A => A) g f = (g ⋆1 f).
    Proof.
      intros. unfold kc3, kc1.
      reflexivity.
    Qed.

    Lemma kc3_00 : forall `(g : B -> C) `(f : A -> B),
        kc3 T (fun A => A) (fun A => A) (ret T C ∘ g) (ret T B ∘ f) = ret T C ∘ g ∘ f.
    Proof.
      intros. unfold kc3.
      reassociate <-.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (ktm_bindt0 T (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_32 : forall `(g : B -> G2 (T C)) `(f : A -> G1 B),
        g ⋆3 map G1 B (T B) (ret T B) ∘ f = map G1 B (G2 (T C)) g ∘ f.
    Proof.
      intros. unfold kc3.
      reassociate <-.
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt0 T G2).
      reflexivity.
    Qed.

    Lemma kc3_31 : forall `(g : B -> G2 (T C)) `(f : A -> T B),
        kc3 T (fun A => A) G2 g f = bindt T T G2 B C g ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_30 : forall `(g : B -> G2 (T C)) `(f : A -> B),
        kc3 T (fun A => A) G2 g (ret T B ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (ktm_bindt0 T G2).
      reflexivity.
    Qed.

    Lemma kc3_23 : forall `(g : B -> G2 C) `(f : A -> G1 (T B)),
        (map G2 C (T C) (ret T C) ∘ g) ⋆3 f = map G1 (T B) (G2 (T C)) (traverse T G2 B C g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_13 : forall `(g : B -> T C) `(f : A -> G1 (T B)),
        kc3 T G1 (fun A => A) g f = map G1 (T B) (T C) (bind T T B C g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_03 : forall `(g : B -> C) `(f : A -> G1 (T B)),
        kc3 T G1 (fun A => A) (ret T C ∘ g) f = map G1 (T B) (T C) (map T B C g) ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_21 : forall `(g : B -> G2 C) `(f : A -> T B),
        (map G2 C (T C) (ret T C) ∘ g) ⋆3 (f : A -> (fun A => A)(T B)) =
          traverse T G2 B C g ∘ f.
    Proof.
      reflexivity.
    Qed.

    Lemma kc3_20 : forall `(g : B -> G2 C) `(f : A -> B),
        kc3 T (fun A => A) G2 (map G2 C (T C) (ret T C) ∘ g) (ret T B ∘ f) = map G2 C (T C) (ret T C) ∘ g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (ktm_bindt0 T G2).
      reflexivity.
    Qed.

    Lemma kc3_12 : forall `(g : B -> T C) `(f : A -> G1 B),
        kc3 T G1 (fun A => A) g (map G1 B (T B) (ret T B) ∘ f) = (map G1 B (T C) g ∘ f).
    Proof.
      intros. unfold kc3. reassociate <-.
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt0 T (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_02 : forall `(g : B -> C) `(f : A -> G1 B),
        kc3 T G1 (fun A => A) (ret T C ∘ g) (map G1 B (T B) (ret T B) ∘ f) =
          map G1 C (T C) (ret T C) ∘ map G1 B C g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reassociate <-; rewrite (fun_map_map G1).
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt0 T (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_01 : forall `(g : B -> C) `(f : A -> T B),
        kc3 T (fun A => A) (fun A => A) (ret T C ∘ g) f =
          map T B C g ∘ f.
    Proof.
      intros.
      unfold kc3.
      reflexivity.
    Qed.

    Lemma kc3_10 : forall `(g : B -> T C) `(f : A -> B),
        kc3 T (fun A => A) (fun A => A) g (ret T B ∘ f) = g ∘ f.
    Proof.
      intros. unfold kc3. reassociate <-.
      change (map (fun A => A) _ _ ?f) with f.
      rewrite (ktm_bindt0 T (fun A => A)).
      reflexivity.
    Qed.

    Lemma kc3_id_l : forall `(g : A -> G2 (T B)),
        kc3 T (fun A => A) G2 g (ret T A) = g.
    Proof.
      intros. change (ret T A) with (ret T A ∘ id).
      now rewrite (kc3_30).
    Qed.

    Lemma kc3_id_r : forall `(f : A -> G1 (T B)),
        kc3 T G1 (fun A => A) (ret T B) f = f.
    Proof.
      intros.
      change (ret T B) with (ret T B ∘ id).
      rewrite (kc3_03).
      rewrite (map_to_bindt).
      change (ret T B ∘ id) with (ret T B).
      rewrite (ktm_bindt1 T).
      rewrite (fun_map_id G1).
      reflexivity.
    Qed.

    Lemma kc3_assoc : forall `(h : C -> G3 (T D)) `(g : B -> G2 (T C)) `(f : A -> G1 (T B)),
        h ⋆3 (g ⋆3 f : A -> (G1 ∘ G2) (T C)) =
          (h ⋆3 g : B -> (G2 ∘ G3) (T D)) ⋆3 f.
    Proof.
      intros.
      unfold kc3.
      unfold_ops @Map_compose.
      unfold_compose_in_compose.
      ext a.
      unfold compose at 1 2.
      compose near (f a) on left.
      rewrite (fun_map_map G1).
      rewrite (ktm_bindt2 T G2 G3).
      unfold compose at 2 3.
      reflexivity.
    Qed.

  End kc3_special_cases.

  Lemma bindt_app_l (T : Type -> Type) `{TraversableMonad T}:
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T T _ ((fun A => A) ∘ G) (Map_compose (fun A => A) G) (Pure_compose (fun A => A) G) (Mult_compose (fun A => A) G) A B f = bindt T T G A B f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity2.
  Qed.

  Lemma bindt_app_r (T : Type -> Type) `{TraversableMonad T}:
    forall (G : Type -> Type) {A B : Type} `{Applicative G} (f : A -> G (T B)),
      @bindt T T _ (G ∘ (fun A => A)) (Map_compose G (fun A => A)) (Pure_compose G (fun A => A)) (Mult_compose G (fun A => A)) A B f = bindt T T G A B f.
  Proof.
    intros. fequal. now rewrite Mult_compose_identity1.
  Qed.

  (** ** Composition with lesser Kleisli operations *)
  (******************************************************************************)
  Section composition_special_cases.

    Context
      (T : Type -> Type)
     `{TraversableMonad T}
      (G1 : Type -> Type)
      (G2 : Type -> Type)
      `{Applicative G1}
      `{Applicative G2}
      (A B C : Type).

#[local] Arguments bindt                 T {U}%function_scope {Bindt}    G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments traverse              T%function_scope     {Traverse} G%function_scope {H H0 H1} {A B}%type_scope _%function_scope _.
#[local] Arguments bind                  T {U}%function_scope {Bind}                                {A B}%type_scope _%function_scope _.
#[local] Arguments map F%function_scope {Map} {A B}%type_scope f%function_scope _.

  (** *** Composition with <<traverse>> *)
  (******************************************************************************)
  Lemma traverse_bindt : forall (g : B -> G2 C) (f : A -> G1 (T B)),
      map G1 (traverse T G2 g) ∘ bindt T G1 f =
        bindt T (G1 ∘ G2) (map G1 (traverse T G2 g) ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt).
    rewrite (ktm_bindt2 T G1 G2).
    reflexivity.
  Qed.

  Lemma bindt_traverse : forall (g : B -> G2 (T C)) (f : A -> G1 B),
      map G1 (bindt T G2 g) ∘ traverse T G1 f =
        bindt T (G1 ∘ G2) (map G1 g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt).
    rewrite (ktm_bindt2 T G1 G2).
    rewrite (kc3_32 T).
    reflexivity.
  Qed.

  (** *** Composition with <<bind>> *)
  (******************************************************************************)
  Lemma bind_bindt : forall (g : B -> T C) (f : A -> G1 (T B)),
      map G1 (bind T g) ∘ bindt T G1 f =
        bindt T G1 (map G1 (bind T g) ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt).
    rewrite (ktm_bindt2 T G1 (fun A => A)).
    rewrite (bindt_app_r T G1).
    reflexivity.
  Qed.

  Lemma bindt_bind : forall (g : B -> G2 (T C)) (f : A -> T B),
      bindt T G2 g ∘ bind T f =
        bindt T G2 (bindt T G2 g ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt).
    change (bindt T G2 g) with (map (fun A => A) (bindt T G2 g)).
    rewrite (ktm_bindt2 T (fun A => A) G2).
    rewrite (bindt_app_l T G2).
    reflexivity.
  Qed.

  (** *** Composition with <<map>> *)
  (******************************************************************************)
  Lemma map_bindt : forall (g : B -> C) (f : A -> G1 (T B)),
      map G1 (map T g) ∘ bindt T G1 f = bindt T G1 (map G1 (map T g) ∘ f).
  Proof.
    intros.
    rewrite (map_to_bindt T).
    rewrite (ktm_bindt2 T G1 (fun A => A)).
    rewrite (bindt_app_r T G1).
    reflexivity.
  Qed.

  Lemma bindt_map : forall (g : B -> G2 (T C)) (f : A -> B),
      bindt T G2 g ∘ map T f = bindt T G2 (g ∘ f).
  Proof.
    intros.
    rewrite (map_to_bindt T).
    change (bindt T G2 g) with (map (fun A => A) (bindt T G2 g)).
    rewrite (ktm_bindt2 T (fun A => A) G2).
    rewrite (bindt_app_l T G2).
    rewrite (kc3_30 T).
    reflexivity.
  Qed.

  (** *** Composition between <<traverse>> and <<bind>> *)
  (******************************************************************************)
  Lemma traverse_bind : forall (g : B -> G2 C) (f : A -> T B),
      traverse T G2 g ∘ bind T f =
        bindt T G2 (traverse T G2 g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    rewrite (bind_to_bindt T).
    change (bindt T G2 ?g) with (map (fun A => A) (bindt T G2 g)).
    rewrite (ktm_bindt2 T (fun A => A) G2).
    rewrite (bindt_app_l T G2).
    rewrite (kc3_21 T).
    reflexivity.
  Qed.

  Lemma bind_traverse : forall (g : B -> T C) (f : A -> G1 B),
      map G1 (bind T g) ∘ traverse T G1 f =
        bindt T G1 (map G1 g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    rewrite (bind_to_bindt T).
    rewrite (ktm_bindt2 T G1 (fun A => A)).
    rewrite (bindt_app_r T G1).
    rewrite (kc3_12 T).
    reflexivity.
  Qed.

  Lemma bind_bind : forall (g : B -> T C) (f : A -> T B),
      bind T g ∘ bind T f =
        bind T (g ⋆1 f).
  Proof.
    intros.
    do 2 rewrite (bind_to_bindt T).
    change (bindt T ?G g) with (map (fun A => A) (bindt T G g)).
    rewrite (ktm_bindt2 T (fun A => A) (fun A => A)).
    rewrite (bindt_app_r T (fun A => A)).
    rewrite (kc3_11 T).
    reflexivity.
  Qed.

  Lemma traverse_traverse : forall (g : B -> G2 C) (f : A -> G1 B),
      map G1 (traverse T G2 g) ∘ traverse T G1 f =
        traverse T (G1 ∘ G2) (map G1 g ∘ f).
  Proof.
    intros.
    do 2 rewrite (traverse_to_bindt T).
    rewrite (ktm_bindt2 T G1 G2).
    rewrite (kc3_22 T).
    reflexivity.
  Qed.

  (** *** Composition between <<traverse>> and <<map>> *)
  (******************************************************************************)
  Lemma map_traverse : forall (A B C : Type)
                          (g : B -> C)
                          (f : A -> G1 B),
      map G1 (map T g) ∘ traverse T G1 f =
        traverse T G1 (map G1 g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    rewrite (map_to_bindt T).
    rewrite (ktm_bindt2 T G1 (fun A => A)).
    rewrite (bindt_app_r T G1).
    rewrite (kc3_02 T).
    reflexivity.
  Qed.

  Lemma traverse_map: forall (A B C : Type)
                         (g : B -> G2 C)
                         (f : A -> B),
      traverse T G2 g ∘ map T f =
        traverse T G2 (g ∘ f).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    rewrite (map_to_bindt T).
    change (bindt T G2 ?g) with (map (fun A => A) (bindt T G2 g)).
    rewrite (ktm_bindt2 T (fun A => A) G2).
    rewrite (bindt_app_l T G2).
    rewrite (kc3_20 T).
    reflexivity.
  Qed.

  (** *** Composition between <<bind>> and <<map>> *)
  (******************************************************************************)
  Lemma bind_map : forall (A B C : Type)
                     (g : B -> T C)
                     (f : A -> B),
      bind T g ∘ map T f = bind T (g ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt T).
    rewrite (map_to_bindt T).
    change (bindt T ?G g) with (map (fun A => A) (bindt T G g)).
    rewrite (ktm_bindt2 T (fun A => A) (fun A => A)).
    rewrite (bindt_app_r T (fun A => A)).
    rewrite (kc3_10 T).
    reflexivity.
  Qed.

  Lemma map_bind : forall (A B C : Type)
                         (g : B -> C)
                         (f : A -> T B),
      map T g ∘ bind T f = bind T (map T g ∘ f).
  Proof.
    intros.
    rewrite (bind_to_bindt T).
    rewrite (map_to_bindt T).
    change (bindt T (fun A => A) (?r ∘ g)) with (map (fun A => A) (bindt T (fun A => A) (r ∘ g))).
    rewrite (ktm_bindt2 T (fun A => A) (fun A => A)).
    rewrite (bindt_app_r T (fun A => A)).
    rewrite (kc3_01 T).
    reflexivity.
  Qed.

  Lemma map_map : forall (A B C : Type) (f : A -> B) (g : B -> C),
      map T g ∘ map T f = map T (g ∘ f).
  Proof.
    intros.
    do 3 rewrite (map_to_bindt T).
    change (bindt T (fun A => A) (?r ∘ g)) with (map (fun A => A) (bindt T (fun A => A) (r ∘ g))).
    rewrite (ktm_bindt2 T (fun A => A) (fun A => A)).
    rewrite (bindt_app_r T (fun A => A)).
    rewrite (kc3_00 T).
    reflexivity.
  Qed.

  (** *** Identity laws *)
  (******************************************************************************)
  Lemma bind_id : forall (A : Type),
      bind T (ret T A) = @id (T A).
  Proof.
    intros.
    rewrite (bind_to_bindt T).
    now rewrite (ktm_bindt1 T).
  Qed.

  Lemma traverse_id : forall (A : Type),
      traverse T (fun A => A) (@id A) = @id (T A).
  Proof.
    intros.
    rewrite (traverse_to_bindt T).
    change (?g ∘ id) with g.
    change (map (fun A => A) ?f) with f.
    now rewrite (ktm_bindt1 T).
  Qed.

  Lemma map_id : forall (A : Type),
      map T (@id A) = @id (T A).
  Proof.
    intros.
    rewrite (map_to_bindt T).
    change (?g ∘ id) with g.
    now rewrite (ktm_bindt1 T).
  Qed.

  (** *** Composition with <<ret>> *)
  (******************************************************************************)
  Lemma bind_ret : forall (A B : Type) (f : A -> T B),
      bind T f ∘ ret T A = f.
  Proof.
    intros. rewrite (bind_to_bindt).
    rewrite (ktm_bindt0 T (fun A => A)).
    reflexivity.
  Qed.

  (** *** Composition with applicative morphisms *)
  (******************************************************************************)
  Lemma traverse_morphism : forall `{! ApplicativeMorphism G1 G2 ϕ} (A B : Type) (f : A -> G1 B),
      ϕ (T B) ∘ traverse T G1 f = traverse T G2 (ϕ B ∘ f).
  Proof.
    intros. do 2 rewrite (traverse_to_bindt).
    rewrite (ktm_morph T).
    reassociate <-.
    fequal. ext a.
    inversion ApplicativeMorphism0.
    unfold compose; cbn. rewrite appmor_natural.
    reflexivity.
  Qed.

  End composition_special_cases.

  Section instances.

    Context
      (T : Type -> Type)
      `{TraversableMonad T}.

    #[export] Instance Functor_TM : Functor T :=
      {| fun_map_id := map_id T;
        fun_map_map := map_map T;
      |}.

    #[export] Instance Monad_TM : Monad T :=
      {| kmon_bind0 := bind_ret T;
        kmon_bind1 := bind_id T;
        kmon_bind2 := bind_bind T;
      |}.

    #[export] Instance Traversable_TM : TraversableFunctor T :=
      {| trf_traverse_id := traverse_id T;
        trf_traverse_traverse := traverse_traverse T;
        trf_traverse_morphism := traverse_morphism T;
      |}.

    #[export] Instance Natural_ret_TM : Natural (ret T).
    Proof.
      constructor.
      - typeclasses eauto.
      - typeclasses eauto.
      - intros. rewrite (map_to_bindt T).
        rewrite (ktm_bindt0 T (fun A => A)).
        reflexivity.
    Qed.

  End instances.

End DerivedInstances.

Module Notations.

  Infix "⋆3" := (kc3 _ _ _) (at level 60) : tealeaves_scope.

End Notations.
