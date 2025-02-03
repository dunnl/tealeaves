From Tealeaves Require Export
  Classes.Categorical.Applicative.
From Tealeaves Require Import
  Classes.Comonoid.

Import Applicative.Notations.
Import Product.Notations.

#[local] Generalizable Variables ϕ F G A B C.

(** * Commutative and Idempotent Elements and Functors *)
(**********************************************************************)

(** ** The Center of an Applicative Functor *)
(**********************************************************************)
Class Center (G: Type -> Type)
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
  (A: Type) (a: G A): Prop :=
    { appcenter_left: forall (B: Type) (x: G B),
        x ⊗ a = map (fun '(x, y) => (y, x)) (a ⊗ x);
      appcenter_right: forall (B: Type) (x: G B),
        a ⊗ x = map (fun '(x, y) => (y, x)) (x ⊗ a);
    }.

(** ** The Idempotent Elements of an Applicative Functor *)
(**********************************************************************)
Class Idempotent (G: Type -> Type)
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
  (A: Type) (a: G A): Prop :=
  { appidem: a ⊗ a = map (fun a => (a, a)) a;
  }.

Class IdempotentCenter (G: Type -> Type)
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
  (A: Type) (a: G A): Prop :=
  { appic_idem :> Idempotent G A a;
    appic_center :> Center G A a;
  }.

#[global] Arguments appcenter_left {G}%function_scope {mapG pureG multG}
  {A}%type_scope (a) {Center} {B}%type_scope x.
#[global] Arguments appcenter_right {G}%function_scope {mapG pureG multG}
  {A}%type_scope (a) {Center} {B}%type_scope x.
#[global] Arguments appidem {G}%function_scope {mapG pureG multG}
  {A}%type_scope (a) {Idempotent}.

(** ** Rewriting Laws for C-I Elements *)
(**********************************************************************)
Section rewriting_commutative_idempotent_element.

  Context
    {G: Type -> Type}
    `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G}
    `{appG: ! Applicative G}.

  Lemma ap_swap
    {A B: Type}
    {f: G (A -> B)}
    {a: G A}
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

  Lemma ap_flip1
    {A B C: Type}
    {f: G (A -> B -> C)}
    {lhs: G A}
    {rhs: G B}
    `{center_rhs: ! Center G B rhs}:
    f <⋆> lhs <⋆> rhs =
      (map flip f) <⋆> rhs <⋆> lhs.
  Proof.
    (* LHS *)
    rewrite ap_swap.
    rewrite map_to_ap.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    (* RHS *)
    rewrite (ap_swap (f := map flip f) (a := rhs)).
    rewrite map_to_ap.
    rewrite map_to_ap.
    rewrite <- ap4.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    rewrite ap3.
    rewrite <- ap4.
    rewrite ap2.
    rewrite ap2.
    reflexivity.
  Qed.

  Lemma ap_flip2
    {A B C: Type}
    {f: G (A -> B -> C)}
    {lhs: G A}
    {rhs: G B}
    `{center_lhs: ! Center G A lhs}:
    f <⋆> lhs <⋆> rhs =
      (map flip f) <⋆> rhs <⋆> lhs.
  Proof.
    (* LHS *)
    rewrite (ap_flip1 (rhs := lhs)).
    compose near f.
    rewrite fun_map_map.
    change (flip ∘ flip) with (@id (A -> B -> C)).
    rewrite fun_map_id.
    reflexivity.
  Qed.

  (* compose flip = (fun f a c b => f a b c) *)
  Corollary ap_flip_x3
    {A B C D: Type}
    {f: G (A -> B -> C -> D)}
    {a: G A}
    {lhs: G B}
    {rhs: G C}
    `{center_rhs: ! Center G C rhs}:
    f <⋆> a <⋆> lhs <⋆> rhs =
      map (compose flip) f <⋆> a <⋆> rhs <⋆> lhs.
  Proof.
    rewrite ap_flip1.
    rewrite map_ap.
    reflexivity.
  Qed.

  Corollary ap_flip_x4
    {A B C D E: Type}
    {f: G (A -> B -> C -> D -> E)}
    {a: G A}
    {b: G B}
    {lhs: G C}
    {rhs: G D}
    `{center_rhs: ! Center G D rhs}:
    f <⋆> a <⋆> b <⋆> lhs <⋆> rhs =
      map (compose (compose flip)) f <⋆> a <⋆> b <⋆> rhs <⋆> lhs.
  Proof.
    rewrite ap_flip1.
    rewrite map_ap.
    rewrite map_ap.
    reflexivity.
  Qed.

  Corollary ap_flip_x5
    {A B C D E F: Type}
    {f: G (A -> B -> C -> D -> E -> F)}
    {a: G A}
    {b: G B}
    {c: G C}
    {lhs: G D}
    {rhs: G E}
    `{center_rhs: ! Center G E rhs}:
      f <⋆> a <⋆> b <⋆> c <⋆> lhs <⋆> rhs =
      map (compose (compose (compose flip))) f <⋆>
        a <⋆> b <⋆> c <⋆> rhs <⋆> lhs.
  Proof.
    rewrite ap_flip1.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    reflexivity.
  Qed.

  Corollary ap_flip_x6
    {A B C D E F J: Type}
    {f: G (A -> B -> C -> D -> E -> F -> J)}
    {a: G A}
    {b: G B}
    {c: G C}
    {d: G D}
    {lhs: G E}
    {rhs: G F}
    `{center_rhs: ! Center G F rhs}:
    f <⋆> a <⋆> b <⋆> c <⋆> d <⋆> lhs <⋆> rhs =
      map (compose (compose (compose (compose flip)))) f <⋆>
        a <⋆> b <⋆> c <⋆> d <⋆> rhs <⋆> lhs.
  Proof.
    rewrite ap_flip1.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    reflexivity.
  Qed.

  Definition double_input {A B: Type} (f: A -> A -> B): A -> B :=
    uncurry f ∘ dup.

  Lemma ap_contract
    {A B: Type}
    {f: G (A -> A -> B)}
    {contract: G A}
    `{idem_contract: ! Idempotent G A contract}:
    f <⋆> contract <⋆> contract = (map double_input f) <⋆> contract.
  Proof.
    unfold ap.
    unfold ap.
    rewrite (app_mult_natural_l G).
    compose near (f ⊗ contract ⊗ contract).
    rewrite (fun_map_map).
    rewrite <- (app_assoc_inv G).
    rewrite (appidem contract).
    rewrite (app_mult_natural_r G).
    compose near (f ⊗ contract).
    rewrite (fun_map_map).
    compose near (f ⊗ contract).
    rewrite (fun_map_map).
    (* rhs *)
    rewrite (app_mult_natural_l G).
    compose near (f ⊗ contract).
    rewrite (fun_map_map).
    fequal.
    ext [x y].
    cbn. reflexivity.
  Qed.

  Corollary ap_contract2
    {A B C: Type}
    {f: G (A -> B -> B -> C)}
    {a: G A}
    {contract: G B}
    `{idem_contract: ! Idempotent G B contract}:
    f <⋆> a <⋆> contract <⋆> contract =
      (map (compose double_input) f) <⋆> a <⋆> contract.
  Proof.
    rewrite ap_contract.
    rewrite map_ap.
    reflexivity.
  Qed.

  Corollary ap_contract3
    {A B C D: Type}
    {f: G (A -> B -> C -> C -> D)}
    {a: G A}
    {b: G B}
    {contract: G C}
    `{idem_contract: ! Idempotent G C contract}:
    f <⋆> a <⋆> b <⋆> contract <⋆> contract =
      (map (compose (compose double_input)) f) <⋆> a <⋆> b <⋆> contract.
  Proof.
    rewrite ap_contract.
    rewrite map_ap.
    rewrite map_ap.
    reflexivity.
  Qed.

  Corollary ap_contract4
    {A B C D E: Type}
    {f: G (A -> B -> C -> D -> D -> E)}
    {a: G A}
    {b: G B}
    {c: G C}
    {contract: G D}
    `{idem_contract: ! Idempotent G D contract}:
    f <⋆> a <⋆> b <⋆> c <⋆> contract <⋆> contract =
      (map (compose (compose (compose double_input))) f) <⋆>
        a <⋆> b <⋆> c <⋆> contract.
  Proof.
    rewrite ap_contract.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    reflexivity.
  Qed.

  Corollary ap_contract5
    {A B C D E F: Type}
    {f: G (A -> B -> C -> D -> E -> E -> F)}
    {a: G A}
    {b: G B}
    {c: G C}
    {d: G D}
    {contract: G E}
    `{idem_contract: ! Idempotent G E contract}:
    f <⋆> a <⋆> b <⋆> c <⋆> d <⋆> contract <⋆> contract =
      (map (compose (compose (compose (compose double_input)))) f) <⋆>
        a <⋆> b <⋆> c <⋆> d <⋆> contract.
  Proof.
    rewrite ap_contract.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    reflexivity.
  Qed.

  Corollary ap_contract6
    {A B C D E F J: Type}
    {f: G (A -> B -> C -> D -> E -> F -> F -> J)}
    {a: G A}
    {b: G B}
    {c: G C}
    {d: G D}
    {e: G E}
    {contract: G F}
    `{idem_contract: ! Idempotent G F contract}:
    f <⋆> a <⋆> b <⋆> c <⋆> d <⋆> e <⋆> contract <⋆> contract =
      (map (compose (compose (compose (compose (compose double_input))))) f) <⋆>
        a <⋆> b <⋆> c <⋆> d <⋆> e <⋆> contract.
  Proof.
    rewrite ap_contract.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    rewrite map_ap.
    reflexivity.
  Qed.

End rewriting_commutative_idempotent_element.

(** ** Commutative Idempotent Applicative Functors *)
(**********************************************************************)
Class ApplicativeCommutativeIdempotent (G: Type -> Type)
  `{mapG: Map G} `{pureG: Pure G} `{multG: Mult G} :=
  { appci_applicative :> Applicative G;
    appci_appic :> forall (A: Type) (a: G A),
        IdempotentCenter G A a;
  }.

(** ** Rewriting Laws for C-I Applicative Funtors *)
(**********************************************************************)
Section rewrite_commutative_idempotent_functor.

  Context
    `{ApplicativeCommutativeIdempotent G}.

  Lemma ap_ci_swap
    {A B: Type}
    {f: G (A -> B)}
    {a: G A}:
    f <⋆> a = (map evalAt a) <⋆> f.
  Proof.
    now rewrite ap_swap.
  Qed.

  Lemma ap_ci_flip:
    forall {A B C: Type} (f: G (A -> B -> C)) (a: G A) (b: G B),
      f <⋆> a <⋆> b = (map flip f) <⋆> b <⋆> a.
  Proof.
    intros.
    now rewrite ap_flip1.
  Qed.

  Lemma ap_ci_contract:
    forall {A B: Type} (f: G (A -> A -> B)) (a: G A),
      f <⋆> a <⋆> a = (map double_input f) <⋆> a.
  Proof.
    intros.
    now rewrite ap_contract.
  Qed.

End rewrite_commutative_idempotent_functor.
