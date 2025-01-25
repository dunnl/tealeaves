From Tealeaves Require Export
  Classes.Categorical.Applicative.

Import Applicative.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ F G A B C.

(** * Commutative and Idempotent Elements and Functors *)
(**********************************************************************)

(** ** The Center of an Applicative Functor *)
(**********************************************************************)
Class Center (G : Type -> Type)
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
  (A: Type) (a: G A): Prop :=
    { appcenter_left: forall (B: Type) (x: G B),
        x ⊗ a = map (fun '(x, y) => (y, x)) (a ⊗ x);
      appcenter_right: forall (B: Type) (x: G B),
        a ⊗ x = map (fun '(x, y) => (y, x)) (x ⊗ a);
    }.

(** ** The Idempotent Elements of an Applicative Functor *)
(**********************************************************************)
Class Idempotent (G : Type -> Type)
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
  (A: Type) (a: G A): Prop :=
  { appidem: a ⊗ a = map (fun a => (a, a)) a;
  }.

Class IdempotentCenter (G : Type -> Type)
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
  (A: Type) (a: G A): Prop :=
  { appic_idem :> Idempotent G A a;
    appic_center :> Center G A a;
  }.

(** ** Commutative Idempotent Applicative Functors *)
(**********************************************************************)
Class ApplicativeCommutativeIdempotent (G : Type -> Type)
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G} :=
  { appci_applicative :> Applicative G;
    appci_appic :> forall (A : Type) (a : G A),
        IdempotentCenter G A a;
  }.

#[global] Arguments appcenter_left {G}%function_scope {mapG pureG multG}
  {A}%type_scope (a) {Center} {B}%type_scope x.
#[global] Arguments appcenter_right {G}%function_scope {mapG pureG multG}
  {A}%type_scope (a) {Center} {B}%type_scope x.
#[global] Arguments appidem {G}%function_scope {mapG pureG multG}
  {A}%type_scope (a) {Idempotent}.

(** ** Rewriting Laws for C-I Applicative Funtors *)
(**********************************************************************)
Lemma ap_ci:
  forall `{ApplicativeCommutativeIdempotent G} {A B: Type}
    (f: G (A -> B)) (a: G A),
    f <⋆> a = (map evalAt a) <⋆> f.
Proof.
  intros.
  unfold ap.
  (* left or right doesn't matter *)
  rewrite (appcenter_right f a).
  compose near (a ⊗ f).
  rewrite (fun_map_map).
  rewrite (app_mult_natural_l G).
  compose near (a ⊗ f) on right.
  rewrite (fun_map_map).
  fequal.
  ext [x y].
  cbn. reflexivity.
Qed.

Lemma ap_ci2:
  forall `{ApplicativeCommutativeIdempotent G}
    {A B C: Type} (f: G (A -> B -> C)) (a: G A) (b: G B),
    f <⋆> a <⋆> b = (map flip f) <⋆> b <⋆> a.
Proof.
  intros.
  unfold ap.
  (* left *)
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a ⊗ b).
  rewrite (fun_map_map).
  (* right *)
  rewrite (app_mult_natural_l G).
  compose near (map flip f ⊗ b ⊗ a).
  rewrite (fun_map_map).
  rewrite (app_mult_natural_l G).
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ b ⊗ a).
  rewrite (fun_map_map).
  rewrite <- (app_assoc_inv G _ _ _ f b a).
  compose near (f ⊗ (b ⊗ a)) on right.
  rewrite (fun_map_map).

  rewrite (appcenter_left a b).

  rewrite (app_mult_natural_r G).
  compose near (f ⊗ (a ⊗ b)) on right.
  rewrite fun_map_map.
  rewrite <- (app_assoc _ _ _ f a b).
  compose near (f ⊗ a ⊗ b) on right.
  rewrite (fun_map_map).
  fequal.
  ext [[xf xa] xb].
  reflexivity.
Qed.

Definition dup {A:Type} := fun (a: A) => (a, a).

Definition double_input {A B: Type} (f: A -> A -> B): A -> B :=
  uncurry f ∘ dup.

Lemma ap_cidup:
  forall `{ApplicativeCommutativeIdempotent G}
    {A B: Type} (f: G (A -> A -> B)) (a: G A),
    f <⋆> a <⋆> a = (map double_input f) <⋆> a.
Proof.
  intros.
  unfold ap.
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a ⊗ a).
  rewrite (fun_map_map).
  rewrite <- (app_assoc_inv G).
  rewrite (appidem a).
  rewrite (app_mult_natural_r G).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  (* rhs *)
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  fequal.
  ext [x y].
  cbn. reflexivity.
Qed.

Definition penguin {A B: Type}
  `{G: Type -> Type} `{Map G} `{Mult G} `{Pure G}:
  forall (a: G A) (b: G B), G B :=
  fun a b => (map (F := G) (const (@id B)) a) <⋆> b.

Infix "|⋆>" := penguin (at level 50).

(** ** Rewriting Laws for C-I Elements *)
(**********************************************************************)
Lemma ap_swap {A B: Type} {G: Type -> Type}
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
  `{appG: ! Applicative G}
  (f: G (A -> B)) (a: G A)
  `{center_a: ! Center G A a}:
    f <⋆> a = (map evalAt a) <⋆> f.
Proof.
  unfold ap.
  rewrite (appcenter_left a).
  compose near (a ⊗ f).
  rewrite (fun_map_map).
  rewrite (app_mult_natural_l G).
  compose near (a ⊗ f) on right.
  rewrite (fun_map_map).
  fequal.
  ext [x y].
  cbn. reflexivity.
Qed.

Lemma ap_contract {A B: Type} {G: Type -> Type}
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
  `{appG: ! Applicative G}
  (f: G (A -> A -> B))
  (a: G A)
  `{idem_a: ! Idempotent G A a}:
  f <⋆> a <⋆> a = (map double_input f) <⋆> a.
Proof.
  unfold ap.
  unfold ap.
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a ⊗ a).
  rewrite (fun_map_map).
  rewrite <- (app_assoc_inv G).
  rewrite (appidem a).
  rewrite (app_mult_natural_r G).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  (* rhs *)
  rewrite (app_mult_natural_l G).
  compose near (f ⊗ a).
  rewrite (fun_map_map).
  fequal.
  ext [x y].
  cbn. reflexivity.
Qed.
