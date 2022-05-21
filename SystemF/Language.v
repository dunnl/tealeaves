(** * The index [K] *)
(******************************************************************************)
Inductive K2 : Type := KType | KTerm.

Instance Keq : EqDec K2 eq.
Proof.
  change (forall x y : K2, {x = y} + {x <> y}).
  decide equality.
Defined.

Instance I2 : Index := {| K := K2 |}.

(** * SystemF syntax and typeclass instances *)
(******************************************************************************)
Parameter base_typ : Type.

Section syntax.

  Context
    {V : Type}.

  Inductive typ : Type :=
  | ty_c : base_typ -> typ
  | ty_v : V -> typ
  | ty_C : typ -> typ
  | ty_ar : typ -> typ -> typ
  | ty_univ : typ -> typ.

  Inductive term : Type :=
  | tm_var : V -> term
  | tm_abs : typ -> term -> term
  | tm_app : term -> term -> term
  | tm_tab : term -> term
  | tm_tap : term -> typ -> term.

End syntax.

(** Clear the implicit arguments to the type constructors. This keeps <<V>>
    implicit for the constructors. *)
Arguments typ V : clear implicits.
Arguments term V : clear implicits.

(** [SystemF] codifies the syntax as a K-partitioned monad system. *)
Definition SystemF (k : K)  (v : Type) : Type :=
  match k with
  | KType => typ v
  | KTerm => term v
  end.

(** ** <<binddt>> operations *)
(******************************************************************************)
Section operations.

  Context
    `{Applicative F}.

  Fixpoint bind_type {A B : Type} (f : forall k, list K2 * A -> F (SystemF k B)) (t : typ A) : F (typ B) :=
    match t with
    | ty_c t => pure F (ty_c t)
    | ty_v a => f KType (nil, a)
    | ty_C t => pure F ty_C <⋆> bind_type f t
    | ty_univ body => pure F (ty_univ) <⋆> (bind_type (hmmm f (inc ([KType]))) body)
    | ty_ar t1 t2 => pure F (ty_ar) <⋆> (bind_type f t1) <⋆> (bind_type f t2)
    end.

  Fixpoint bind_term {A B} (f  : forall k, list K2 * A -> F (SystemF k B)) (t : term A) : F (term B) :=
    match t with
    | tm_var a => f KTerm (nil, a)
    | tm_app t1 t2 => pure F tm_app <⋆> bind_term f t1 <⋆> bind_term f t2
    | tm_abs ty body => pure F (tm_abs)
                            <⋆> bind_type (hmmm f (inc ([KTerm]))) ty
                            <⋆> bind_term (hmmm f (inc ([KTerm]))) body
    | tm_tab body => pure F tm_tab <⋆> (bind_term (hmmm f (inc ([KType])))  body)
    | tm_tap t1 ty => pure F tm_tap <⋆> bind_term f t1 <⋆> bind_type f ty
    end.

End operations.

Instance: MReturn SystemF :=
  fun A k => match k with
          | KType => ty_v
          | KTerm => tm_var
          end.

Instance MBind_type : MBind (list K2) SystemF typ := @bind_type.
Instance MBind_term : MBind (list K2) SystemF term := @bind_term.
Instance MBind_SystemF: forall k, MBind (list K2) SystemF (SystemF k) :=
  ltac:(intros [|]; typeclasses eauto).

Lemma mod_bind_ret_term : forall (A : Type) (t : typ A),
    mbind (F := fun x => x) typ (hmmm (mret SystemF) (extract (prod (list K2)))) t = t.
Proof.
  intros. induction t.
  - easy.
  - easy.
  - now rewrite <- IHt at 2.
  - rewrite <- IHt1 at 2. rewrite <- IHt2 at 2.
    cbn. fequal.
  - rewrite <- IHt at 2. cbn.
    unfold_ops @Pure_I; unfold id.
    repeat fequal. ext [|] [w a]; easy.
Qed.

Lemma mod_bind_bind_type : forall
    `{Applicative F}
    `{Applicative G}
    `(f : forall k, list K2 * A -> F (SystemF k B))
    `(g : forall k, list K2 * B -> G (SystemF k C)),
    fmap F (mbind typ g) ∘ mbind typ f = mbind (F := F ∘ G) typ (g ⋆ f).
Proof.
  intros. ext t. unfold compose. induction t.
  - cbn. now rewrite (app_pure_natural F).
  - cbn. change_right (fmap F (mbind typ (g ◻ const (inc []))) (f KType ([], v))).
    do 2 fequal. now ext [|] [w a].
  - cbn.
    rewrite ap6. rewrite (app_pure_natural F).
    rewrite (ap_compose_2 G F).
    rewrite (app_pure_natural F).
    rewrite <- IHt.
    rewrite ap5.
    now rewrite fmap_to_ap.
  - cbn.
    rewrite <- IHt1. rewrite <- IHt2. clear IHt1; clear IHt2.
    do 2 rewrite ap6.
    do 2 rewrite (ap_compose_2 G F).
    do 2 rewrite <- ap7.
    do 2 rewrite ap6.
    do 2 (compose near (pure (F ○ G) (ty_ar (V := C)));
          try rewrite (fun_fmap_fmap F)).
    unfold compose.
    do 2 (compose near (pure (F ○ G) (ty_ar (V := C)));
          try rewrite (fun_fmap_fmap F)).
    unfold compose.
    do 2 fequal.
    do 2 rewrite (app_pure_natural F).
    fequal.
  - admit.
Admitted.

(** * Properties of <<shift>
