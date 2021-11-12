(** * Introduction *)
(** For syntax theory, one typically wants to provide [ListableMonad]
    and [ListableModule] instances, which are then used to instantiate
    [ListableMFunctor] (which plays more of an internal role). *)

(* use fully qualified names, see coq issue 14539 *)
Require Import Tealeaves.Functors.
Require Import Tealeaves.Sets.
Require Import Tealeaves.Quantifiable.
Require Import Tealeaves.Listable.

Import Sets.Notations.
Import List.Notations.
Import Quantifiable.Notations.
Local Open Scope list_scope.
Local Open Scope tealeaves_scope.

From Tealeaves Require Import
     Multisorted.Functors
     Multisorted.MSets
     Multisorted.Quantifiable
     Multisorted.MList.

Import Multisorted.Category.Notations.
Import Multisorted.MSets.Notations.
Import Multisorted.Quantifiable.Notations.
Local Open Scope tealeaves_multi_scope.

(** * The [shape] operation *)
(** [shape] replaces each leaf of a term <<t : F A>> with the sole element of
    type [unit].  *)
(******************************************************************************)
Definition shape F `{Mfmap F} {A} : F A -> F unit :=
  mfmap F (fun _ _ => tt).

(** As one would intuitively expect, mapping a function over a term <<t : F A>>
    preserves the shape of <<t>>. *)
Lemma shape_mfmap_ `{MFunctor F} : forall A B (f : A -k-> B),
    shape F ∘ mfmap F f = shape F.
Proof.
  intros. unfold shape. now rewrite (mfmap_mfmap F).
Qed.

Corollary shape_mfmap `{MFunctor F} : forall A B (f : A -k-> B) (t : F A),
    shape F (mfmap F f t) = shape F t.
Proof.
  intros. compose near t on left. now rewrite (shape_mfmap_).
Qed.

Theorem shape_shape `{MFunctor F} : forall A,
    shape F ∘ shape (A:=A) F = shape F.
Proof.
  intros. unfold shape.
  now rewrite (mfmap_mfmap F).
Qed.

(** * The [tolist] operation *)
Class Tomlist `{ix : Index} (F : Type -> Type) :=
    tomlist : forall {A : Type}, F A -> mlist A.

Arguments tomlist {ix} F%function_scope {Tomlist} {A}%type_scope _.


(** * Typeclasses for listable type constructors *)
(******************************************************************************)
Section listable_type_constructor_classes.

  Context
    `{ix : Index}.

  (** ** Listable functors *)
  (** A listable functor is a functor with a well-behaved (natural)
      [tomlist] operation that satisfies a properness condition: two
      F-terms with the same shape and same contents must be the
      same. *)

  Class ListableMFunctor (F : Type -> Type) `{! Mfmap F} `{! Tomlist F}  :=
    { lfun_natural :> Natural (@tomlist _ F _);
      lfun_functor :> MFunctor F _;
    }.

  (** ** [tomlist]-preserving natural transformations *)
  Class MlistreservingTransformation
        {F T : Type -> Type}
        `{! Mfmap F} `{! Tomlist F}
        `{! Mfmap T} `{! Tomlist T}
        (η : forall A, F A -> T A) :=
    { ltrans_natural : Natural η;
      ltrans_commute : forall A, tomlist F = tomlist T ∘ η A;
    }.

  (** ** Listable monads *)
  (** A listable monad a monad with a well-behaved [tomlist] operation. The
  definition below is minimal; to justify it we prove below that an instance of
  [ListableMonad] is indeed a [ListableMFunctor] (specifically that the monad
  self-action forms a [ListableModule], whose carrier is always a listable
  functor). *)
  Section listable_monad_class.

    Context
      (T : K -> Type -> Type)
      `{! Mreturn T}
      `{forall k, Mbind (T k) T}
      `{forall k, Tomlist (T k)}.

    Class ListableMMonad : Prop :=
      { lmmon_monad :> MMonad T;
        lmmon_mret : forall {A k},
            tomlist (T k) ∘ mret T k (A:=A) = mret (const mlist) k;
        lmmon_mbind : forall k {A B} (f : forall k, A -> T k B),
            tomlist (T k) ∘ mbind (T k) f =
            mbind mlist (fun k => tomlist (T k) ∘ f k) ∘ tomlist (T k);
      }.

  End listable_monad_class.

  (** ** Listable modules *)
  (** A listable module is a module in which both the functor and monad are
  listable. We give a minimized definition, and to justify this we prove below
  that the carrier <<F>> of [ListableModule F T] is indeed a [ListableMFunctor]. *)
  Section listable_module_class.

    Context
      (F : Type -> Type)
      (T : K -> Type -> Type)
      `{! Tomlist F}
      `{! Mreturn T}
      `{! forall k, Mbind (T k) T}
      `{! Mbind F T}
      `{ forall k, Tomlist (T k)}.

    Class ListableRightModule : Prop :=
      { lrmod_rmod :> RightModule F T;
        lrmod_monad :> ListableMMonad T;
        lrmod_mbind : forall {A B} (f : forall k, A -> T k B),
            tomlist F ∘ mbind F f = mbind mlist (fun k => tomlist (T k) ∘ f k) ∘ tomlist F;
      }.

  End listable_module_class.

End listable_type_constructor_classes.

(** * Typeclass inclusions *)
(******************************************************************************)
(** ** Listable monads are listable modules *)
(** To avoid cycles between [ListableModule] and [ListableMonad], we hide this
    typeclass instance from global resolution. *)
Section listable_module_of_monad.

  Context
    `{ListableMMonad T}.

  Instance Listable_Module_MMonad {k} : ListableRightModule (T k) T :=
    {| lrmod_mbind := fun A B => lmmon_mbind T k;
       lrmod_rmod := Module_MMonad k;
    |}.

End listable_module_of_monad.

(** ** Carriers of listable modules form listable functors *)
(** As expected, the carrier <<F>> of listable module is indeed a
     [ListableMFunctor]. This boils down to showing that naturality of
     [tomlist] can be inferred from the compatibility conditions with
     [ret] and [bind]. *)
Section listable_functor_of_module.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{ListableRightModule (ix:=ix) F T}.

  #[global] Instance Natural_module_tomlist : Natural (@tomlist ix F _).
  Proof.
    introv. unfold_mfmap @Mfmap_rmod.
    rewrite (lrmod_mbind F T). do 2 fequal.
    ext k. reassociate <- on right.
    now rewrite (lmmon_mret T).
  Qed.

  #[global] Instance Listable_Functor_Module : ListableMFunctor F := {}.

End listable_functor_of_module.

(** * Reasoning principles for [shape] *)
(******************************************************************************)
Section shape_lemmas.

  Context
    `{Index}.

  Lemma shape_nil : forall A,
      shape mlist (@nil (K * A)) = @nil (K * unit).
  Proof.
    reflexivity.
  Qed.

  Lemma shape_one : forall A (k : K) (a : A),
      shape mlist [ (k, a) ] = [ (k, tt) ].
  Proof.
    reflexivity.
  Qed.

  Lemma shape_cons : forall A (k : K) (a : A) (l : mlist A),
      shape mlist ((k, a) :: l) = (k, tt) :: shape mlist l.
  Proof.
    reflexivity.
  Qed.

  Lemma shape_app : forall A (l1 l2 : mlist A),
      shape mlist (l1 ++ l2) = shape mlist l1 ++ shape mlist l2.
  Proof.
    intros. unfold shape. now rewrite mfmap_mlist_app.
  Qed.

  Lemma shape_nil_iff : forall A (l : mlist A),
      shape mlist l = @nil (Tag unit) <-> l = [].
  Proof.
    induction l as [| a ? ?]. easy.
    split; intro contra; destruct a; now inverts contra.
  Qed.

  Theorem shape_inv_app_r : forall A (l1 l2 r1 r2: mlist A),
      shape mlist r1 = shape mlist r2 ->
      shape mlist (l1 ++ r1) = shape mlist (l2 ++ r2) <->
      shape mlist l1 = shape mlist l2.
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split.
    - intros. unfold mlist in l1, l2, r1, r2.
      eapply List.app_inv_tail. eassumption.
    - intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_inv_app_l : forall A (l1 l2 r1 r2: mlist A),
      shape mlist l1 = shape mlist l2 ->
      shape mlist (l1 ++ r1) = shape mlist (l2 ++ r2) <->
      shape mlist r1 = shape mlist r2.
  Proof.
    introv heq. rewrite 2(shape_app). rewrite heq.
    split.
    - intros; eapply List.app_inv_head; eassumption.
    - intros hyp; now rewrite hyp.
  Qed.

  Theorem shape_inv_cons_iff : forall A (l1 l2 : mlist A) (k1 k2 : K) (a1 a2 : A),
      shape mlist ((k1, a1) :: l1) = shape mlist ((k2, a2) :: l2) <->
      k1 = k2 /\ shape mlist l1 = shape mlist l2.
  Proof.
    introv. rewrite 2(shape_cons).
    split; [introv hyp | introv [hyp1 hyp2]]. now inverts hyp.
    now rewrite hyp1, hyp2.
  Qed.

  Corollary shape_inv_cons_iff_eq : forall A (l1 l2 : mlist A) (k : K) (a1 a2 : A),
      shape mlist ((k, a1) :: l1) = shape mlist ((k, a2) :: l2) <->
      shape mlist l1 = shape mlist l2.
  Proof.
    introv. rewrite shape_inv_cons_iff. intuition.
  Qed.

  Corollary shape_inv_cons_tail : forall A (l1 l2 : mlist A) (k1 k2 : K) (a1 a2 : A),
      shape mlist ((k1, a1) :: l1) = shape mlist ((k2, a2) :: l2) ->
      shape mlist l1 = shape mlist l2.
  Proof.
    introv. rewrite shape_inv_cons_iff. intuition.
  Qed.
  Theorem mlist_inv_app_ll : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist l1 = shape mlist l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| (k1, a1) ? IHl1 ];
                induction l2 as [| (k2, a2) ? IHl2 ].
    - reflexivity.
    - introv shape_eq hyp. now inverts shape_eq.
    - introv shape_eq hyp. now inverts shape_eq.
    - introv shape_eq heq.
      rewrite shape_inv_cons_iff in shape_eq;
        destruct shape_eq as [? ?].
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem mlist_inv_app_rl : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist r1 = shape mlist r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      l1 = l2.
  Proof.
    intros A. induction l1 as [| (?, ?) ? IHl1 ];
                induction l2 as [| (?, ?) ? IHl2 ].
    - reflexivity.
    - introv shape_eq heq. apply (mlist_inv_app_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- shape_inv_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq. apply (mlist_inv_app_ll) with (r1 := r1) (r2 := r2).
      + rewrite <- shape_inv_app_r. now rewrite heq. auto.
      + assumption.
    - introv shape_eq heq.
      rewrite <- 2(List.app_comm_cons) in heq.
      inverts heq. fequal. eauto.
  Qed.

  Theorem mlist_inv_app_lr : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist l1 = shape mlist l2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eapply List.app_inv_head; eassumption. }
    { eauto using mlist_inv_app_ll. }
  Qed.

  Theorem mlist_inv_app_rr : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist r1 = shape mlist r2 ->
      (l1 ++ r1 = l2 ++ r2) ->
      r1 = r2.
  Proof.
    introv hyp1 hyp2. enough (l1 = l2).
    { subst. eapply List.app_inv_head; eassumption. }
    { eauto using mlist_inv_app_rl. }
  Qed.

  Theorem inv_app_eq : forall A (l1 l2 r1 r2 : mlist A),
      shape mlist l1 = shape mlist l2 \/ shape mlist r1 = shape mlist r2 ->
      l1 ++ r1 = l2 ++ r2 <-> l1 = l2 /\ r1 = r2.
  Proof.
    introv [hyp | hyp]; split.
    - introv heq. split. eapply mlist_inv_app_ll; eauto.
      eapply mlist_inv_app_lr; eauto.
    - introv [? ?]. now subst.
    - introv heq. split. eapply mlist_inv_app_rl; eauto.
      eapply mlist_inv_app_rr; eauto.
    - introv [? ?]. now subst.
  Qed.

  Context
    `{! MFunctor F fmap_F } `{! Tomlist F} `{! Natural (@tomlist _ F _)}.

  Theorem shape_eq_impl_tomlist : forall A (t s : F A),
      shape F t = shape F s ->
      shape mlist (tomlist F t) = shape mlist (tomlist F s).
  Proof.
    introv heq. compose near t on left; compose near s on right.
    unfold shape in *. rewrite naturality.
    unfold compose. now rewrite heq.
  Qed.

  Corollary shape_l : forall A (l1 l2 : F A) (x y : mlist A),
      shape F l1 = shape F l2 ->
      tomlist F l1 ++ x = tomlist F l2 ++ y ->
      tomlist F l1 = tomlist F l2.
  Proof.
    introv shape_eq heq.
    eauto using mlist_inv_app_ll, shape_eq_impl_tomlist.
  Qed.

  Corollary shape_r : forall A (l1 l2 : F A) (x y : mlist A),
      shape F l1 = shape F l2 ->
      x ++ tomlist F l1 = y ++ tomlist F l2 ->
      tomlist F l1 = tomlist F l2.
  Proof.
    introv shape_eq heq.
    eauto using mlist_inv_app_rr, shape_eq_impl_tomlist.
  Qed.

  Corollary shape_l_mfmap : forall A B (l1 l2 : F A) (f g : A -k-> B) (x y : mlist B),
      shape F l1 = shape F l2 ->
      mfmap mlist f (tomlist F l1) ++ x = mfmap mlist g (tomlist F l2) ++ y ->
      mfmap mlist f (tomlist F l1) = mfmap mlist g (tomlist F l2).
  Proof.
    introv shape_eq. compose near l1. compose near l2.
    rewrite 2(naturality). unfold compose; intro heq.
    eapply shape_l. compose near l1; compose near l2.
    rewrite 2(shape_mfmap_). assumption. eassumption.
  Qed.

  Corollary shape_r_mfmap : forall A B (l1 l2 : F A) (f g : A -k-> B) (x y : mlist B),
      shape F l1 = shape F l2 ->
      x ++ mfmap mlist f (tomlist F l1) = y ++ mfmap mlist g (tomlist F l2) ->
      mfmap mlist f (tomlist F l1) = mfmap mlist g (tomlist F l2).
  Proof.
    introv shape_eq. compose near l1. compose near l2.
    rewrite 2(naturality). unfold compose; intro heq.
    eapply shape_r. compose near l1; compose near l2.
    rewrite 2(shape_mfmap_). assumption. eassumption.
  Qed.

End shape_lemmas.

(** * [mlist] is a listable monad *)
(** For good measure, we prove here that [mlist] is indeed a listable monad. We
do not expose this instance globally because it is probably not useful and may
be annoying when one infers quantifiable instances from generic listable
instances. *)
(******************************************************************************)
Section mlist_is_listable.

  Context
    `{ix : Index}.

  #[global] Instance tomlist_mlist `{Index} : Tomlist mlist :=
    fun A => @id (mlist A).

  Theorem lmmon_mret_mlist : forall {A k},
      tomlist (const mlist k) ∘ mret (const mlist) k (A:=A) = mret (const mlist) k.
  Proof.
    reflexivity.
  Qed.

  Theorem lmmon_mbind_mlist : forall {A B} (f : forall k, A -> const mlist k B),
      tomlist mlist ∘ mbind mlist f =
      mbind mlist (fun k => tomlist (const mlist k) ∘ f k) ∘ tomlist mlist.
  Proof.
    reflexivity.
  Qed.

End mlist_is_listable.

(** * Listable instances form quantifiable instances *)
(******************************************************************************)
#[global] Instance tomset_Listable `{Index} `{Tomlist F} : Tomset F :=
  fun A => tomset mlist ∘ tomlist F.

(*(** We add an extra typeclass instance that will be used to infer
    families of [Tomset] instances from families of [Tomlist]
    instances. This is more convenient during unification when
    rewriting with theorems like [in_ret_iff], because the [tomset]
    instance in that theorem is a family applied to some <<k>>. *)
#[global] Instance tomset_Listable_family `{Index} {T : K -> Type -> Type}
 `{forall k, Tomlist (T k)} : `{forall k, Tomset (T k)} :=
  fun k A => tomset mlist ∘ tomlist (T k).
*)

(** A value <<a>> occurs in <<t>> if and only if <<a>> occurs in <<t>>'s
      contents. *)
Lemma in_iff_in_mlist `{Index} `{Tomlist F} : forall A (t : F A) (k : K) (a : A),
    (k, a) ∈m t <-> (k, a) ∈m tomlist F t.
Proof.
  reflexivity.
Qed.

(** ** Listable functors are quantifiable *)
Section quantifiable_of_listable_functor.

  Context
    `{ListableMFunctor F}.

  (** The derived [tomset] operation on <<F>> is natural. *)
  Instance Natural_tomset_Listable : Natural (@tomset ix F tomset_Listable).
  Proof.
    intros A B f. unfold tomset, tomset_Listable.
    reassociate <- on left. rewrite (naturality (η := @tomset _ mlist _) f).
    reassociate -> on left. rewrite (naturality (η := @tomlist _ F _) f).
    reflexivity.
  Qed.

  #[global] Instance Quantifiable_Listable_MFunctor :
    QuantifiableMFunctor F := {}.

End quantifiable_of_listable_functor.

(** ** Listable monads are quantifiable *)
Section quantifiable_of_listable_monad.

  Context
    `{ListableMMonad T}.

  Theorem qmmon_mret_Listable : forall A k,
      tomset (T k) ∘ mret T k (A:=A) = mret (const mset) k.
  Proof.
    introv. unfold tomset, tomset_Listable, compose. ext a.
    compose near a on left. rewrite (lmmon_mret T).
    compose near a on left. rewrite (qmmon_mret_mlist).
    reflexivity.
  Qed.

  Theorem qmmon_mbind_Listable : forall A B k (f : A ~k~> T B),
      tomset (T k) ∘ mbind (T k) f =
      mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset (T k).
  Proof.
    intros. unfold tomset, tomset_Listable, compose. ext t.
    compose near t on left. rewrite (lmmon_mbind T). unfold compose.
    compose near (tomlist (T k) t). rewrite (qmmon_mbind_mlist). unfold compose.
    reflexivity.
  Qed.

  #[global] Instance Quantifiable_Listable_Monad : QuantifiableMMonad T :=
    {| qmmon_mret := qmmon_mret_Listable;
       qmmon_mbind := qmmon_mbind_Listable; |}.

End quantifiable_of_listable_monad.

(** ** Listable modules are quantifiable *)
Section quantifiable_of_listable_module.

  Context
    `{ListableRightModule F T}.

  Theorem qrmod_mbind_Listable : forall A B (f : A ~k~> T B),
      tomset F ∘ mbind F f = mbind mset (fun k => tomset (T k) ∘ f k) ∘ tomset F.
  Proof.
    intros. unfold tomset, tomset_Listable, compose. ext t.
    compose near t on left. rewrite (lrmod_mbind F T). unfold compose.
    compose near (tomlist F t). rewrite (qmmon_mbind_mlist). unfold compose.
    reflexivity.
  Qed.

  #[global] Instance Quantifiable_Listable_Module : QuantifiableRightModule F T :=
    {| qrmod_mbind := qrmod_mbind_Listable;
    |}.

End quantifiable_of_listable_module.

(** * Derived operation [tolistk] *)
(******************************************************************************)
Definition tolistk F `{Tomlist F} {A} k : F A -> list A :=
  filterk k ∘ tomlist F.

Theorem in_tolistk_iff `{Tomlist F} : forall A (k : K) (t : F A) (a : A),
    a ∈ tolistk F k t <-> (k, a) ∈m tomlist F t.
Proof with tauto.
  intros. unfold tolistk, compose.
  induction (tomlist F t) as [| [k' a'] ? IH ].
  - cbv...
  - compare values k and k'; autorewrite* with tea_list.
    + rewrite filterk_cons_eq; autorewrite* with tea_list.
      rewrite IH...
    + rewrite filterk_cons_neq; auto. rewrite IH...
Qed.

(** * Properties of [mfmap] over listable functors *)
(******************************************************************************)
Section listable_functor_global.

  Context
    (F : Type -> Type)
    `{ListableMFunctor F}.

  Theorem tomlist_mfmap {A B} : forall (f : K -> A -> B),
      tomlist F ∘ mfmap F f = mfmap mlist f ∘ tomlist F.
  Proof.
    introv. now rewrite <- (naturality f).
  Qed.

  Theorem tolistk_mfmap {A B} : forall k (f : K -> A -> B),
      tolistk F k ∘ mfmap F f = fmap list (f k) ∘ tolistk F k.
  Proof.
    introv. unfold tolistk.
    reassociate -> on left. rewrite <- (naturality f).
    reassociate <- on left. now rewrite filterk_natural.
  Qed.

End listable_functor_global.

(** * Properties of [fmapk] over listable functors *)
(******************************************************************************)
Section listable_functor_local.

  Context
    (F : Type -> Type)
    `{ListableMFunctor F}.

  (** ** Interaction between [tomlist] and [fmapk] *)
  (******************************************************************************)
  Theorem tomlist_fmapk {A} k : forall (f : A -> A),
      tomlist F ∘ fmapk F k f = fmapk mlist k f ∘ tomlist F.
  Proof.
    introv. unfold fmapk.
    now rewrite <- (naturality (tgt k f)).
  Qed.

  (** ** Interaction between [tolistk] and [fmapk] *)
  (******************************************************************************)
  Theorem tolistk_fmapk_eq {A} k : forall (f : A -> A),
      tolistk F k ∘ fmapk F k f =  fmap list f ∘ tolistk F k.
  Proof.
    introv. unfold fmapk, tolistk.
    reassociate -> on left. rewrite <- (naturality (tgt k f)).
    reassociate <- on left. rewrite filterk_natural.
    now rewrite tgt_eq.
  Qed.

  Theorem tolistk_fmapk_neq {A} k j : forall (f : A -> A),
      k <> j ->
      tolistk F j ∘ fmapk F k f = tolistk F j.
  Proof.
    introv neq. unfold fmapk, tolistk.
    reassociate -> on left. rewrite <- (naturality (tgt k f)).
    reassociate <- on left. rewrite filterk_natural.
    rewrite tgt_neq; auto. now rewrite (fun_fmap_id list).
  Qed.

End listable_functor_local.

(** * Properties of global [mbind] over listable functors *)
(******************************************************************************)
Section listable_module_global.

  Context
    `{ix : Index}
    (F : Type -> Type)
    (T : K -> Type -> Type)
    `{ListableRightModule (ix:=ix) F T}.

  Theorem tomlist_mbind {A B} : forall (f : A ~k~> T B),
      tomlist F ∘ mbind F f = mbind mlist (fun k => tomlist (T k) ∘ f k) ∘ tomlist F.
  Proof.
    introv. now rewrite <- (lrmod_mbind F T).
  Qed.

  Existing Instance lrmod_monad.

  (** Interaction between [tomlist] and [bindk] *)
  Theorem tomlist_bindk {A} k : forall (f : A -> T k A),
      tomlist F ∘ bindk F k f = bindk mlist k (tomlist (T k) ∘ f) ∘ tomlist F.
  Proof.
    introv. unfold bindk. rewrite (lrmod_mbind F T).
    fequal. fequal. ext k'. destruct_eq_args k k'.
    - now do 2 rewrite btg_eq.
    - do 2 (rewrite btg_neq; auto).
      now rewrite (lmmon_mret T).
  Qed.

  Theorem tolistk_bindk_eq {A} k : forall (f : A -> T k A),
      tolistk F k ∘ bindk F k f =
      bind list (tolistk (T k) k ∘ f) ∘ tolistk F k.
  Proof.
    introv. unfold tolistk.
    reassociate -> on left. rewrite tomlist_bindk.
    reassociate <- on left. rewrite (filterk_bindk_eq).
    reflexivity.
  Qed.

  Theorem tolistk_bindk_neq {A} k j : forall (f : A -> T k A),
      k <> j ->
      tolistk F j ∘ bindk F k f =
      filterk j ∘ bindk mlist k (tomlist (T k) ∘ f) ∘ tomlist F.
  Proof.
    introv neq. unfold tolistk.
    reassociate -> on left. now rewrite tomlist_bindk.
  Qed.

End listable_module_global.

(** * Miscellaneous inversion lemmas for equality between [mlist] *)
(******************************************************************************)
Section mlist_inversion_principles.

  Context
    `{Index}.

  Lemma mlist_inv_cons : forall A (k1 k2 : K) (a1 a2 : A) (l1 l2 : mlist A),
      (k1, a1) :: l1 = (k2, a2) :: l2 -> k1 = k2 /\ a1 = a2 /\ l1 = l2.
  Proof.
    introv heq. inversion heq. subst. auto.
  Qed.

  Lemma mfmap_inv_cons : forall  {A B} {f g : A -k-> B} (k1 k2 : K) (a1 a2 : A) (l1 l2 : mlist A),
      mfmap mlist f ((k1, a1) :: l1) = mfmap mlist g ((k2, a2) :: l2) ->
      f k1 a1 = g k2 a2 /\ mfmap mlist f l1 = mfmap mlist g l2.
  Proof.
    introv hyp. rewrite mfmap_mlist_cons in hyp.
    cbn in hyp. apply mlist_inv_cons in hyp.
    intuition.
  Qed.

  Lemma mfmap_inv_cons_hd : forall  {A B} {f g : A -k-> B} (k1 k2 : K) (a1 a2 : A) (l1 l2 : mlist A),
      mfmap mlist f ((k1, a1) :: l1) = mfmap mlist g ((k2, a2) :: l2) ->
      f k1 a1 = g k2 a2.
  Proof.
    introv hyp. now apply mfmap_inv_cons in hyp.
  Qed.

  Lemma mfmap_inv_cons_tl : forall  {A B} {f g : A -k-> B} (k1 k2 : K) (a1 a2 : A) (l1 l2 : mlist A),
      mfmap mlist f ((k1, a1) :: l1) = mfmap mlist g ((k2, a2) :: l2) ->
      mfmap mlist f l1 = mfmap mlist g l2.
  Proof.
    introv hyp. now apply mfmap_inv_cons in hyp.
  Qed.

  Lemma mfmap_app_inv_l : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l1 = mfmap mlist g l1.
  Proof.
    introv hyp. rewrite 2(mfmap_mlist_app) in hyp.
    eapply mlist_inv_app_rl. 2: eauto.
    now rewrite 2(shape_mfmap).
  Qed.

  Lemma mfmap_app_inv_r : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l2 = mfmap mlist g l2.
  Proof.
    introv hyp. rewrite 2(mfmap_mlist_app) in hyp.
    eapply mlist_inv_app_lr. 2: eauto.
    now rewrite 2(shape_mfmap).
  Qed.

  Lemma map_app_inv : forall {A B} {f g : A -k-> B} (l1 l2 : mlist A),
      mfmap mlist f (l1 ++ l2) = mfmap mlist g (l1 ++ l2) ->
      mfmap mlist f l1 = mfmap mlist g l1 /\
      mfmap mlist f l2 = mfmap mlist g l2.
  Proof.
    intros; split; eauto using mfmap_app_inv_l, mfmap_app_inv_r.
  Qed.

End mlist_inversion_principles.
