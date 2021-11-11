(** * Characterizations of listable monad compatibility conditions *)
(******************************************************************************)
Section listable_monad_compatibility_conditions.

  Context
    `{Monad T} `{Tolist T} `{! ListableFunctor T}.

  (** The left-hand condition states that the natural transformation [ret T]
      commutes with taking [tolist], i.e. that [ret T] is a list-preserving
      natural transformation. The right-hand condition is one half of the
      statement that [tolist] forms a monad homomorphism. *)
  Lemma tolist_ret_iff {A} :
    (tolist T ∘ ret T = tolist (fun x => x) (A:=A)) <->
    (tolist T ∘ ret T = ret list (A:=A)).
  Proof with auto.
    split...
  Qed.

  (** The left-hand condition states that the natural transformation [join T] is
      [tolist]-preserving. The right-hand condition is one half of the statement
      that [tolist] forms a monad homomorphism. *)
  Lemma tolist_join_iff {A} :
    `(tolist T ∘ join T (A:=A) = tolist (T ∘ T)) <->
    `(tolist T ∘ join T (A:=A) = join list ∘ tolist T ∘ fmap T (tolist T)).
  Proof with auto.
    split...
  Qed.

  Theorem listable_monad_compatibility_spec :
    Monad_Hom T list (@tolist T _) <->
    ListPreservingTransformation (@ret T _) /\
    ListPreservingTransformation (@join T _).
  Proof with auto.
    split.
    - introv mhom. inverts mhom. inverts mhom_domain. split.
      + constructor...
        introv. symmetry. rewrite tolist_ret_iff...
      + constructor...
        introv. symmetry. apply tolist_join_iff...
    - intros [h1 h2]. inverts h1. inverts h2.
      constructor; try typeclasses eauto.
      + introv. rewrite <- tolist_ret_iff...
      + introv. rewrite <- tolist_join_iff...
  Qed.

End listable_monad_compatibility_conditions.

(* Proof that lists lack the strongly faithful [bind] property *)
Example f1 : nat -> list nat :=
  fun n => match n with
        | 0 => [4 ; 5]
        | 1 => [ 6 ]
        | _ => [ 42 ]
        end.

Example f2 : nat -> list nat :=
  fun n => match n with
        | 0 => [ 4 ]
        | 1 => [ 5 ; 6 ]
        | _ => [ 42 ]
        end.

Definition l := [ 0 ; 1 ].

Goal bind list f1 l = bind list f2 l.
  reflexivity.
Qed.

Goal not (forall x, x ∈ l -> f1 x = f2 x).
Proof.
  intro hyp.
  assert (0 ∈ l) by (cbn; now left).
  specialize (hyp 0 ltac:(auto)).
  cbv in hyp.
  now inverts hyp.
Qed.





(*
Section TolisterableRightModule.

  Context
    `{module : TolisterableRightModule F T}.

  Lemma tolistm_ret_mhom : forall A (a : A), tolist (ret a) = ret a.
  Proof.
    inversion module.
    inversion tolistrmod_monad0.
    rewrite tolisterable_monad_compatibility_spec in tolistm_mhom0.
    destructs_all.
    rewrite <- tolisterable_ret_iff.
    rewrite <- tolisterable_ret_unpack.
    auto.
  Qed.

  Lemma tolistm_join_mhom : forall A (t : T (T A)), tolist (join t) = join (tolist (fmap (F := T) tolist t)).
  Proof.
    inversion module.
    inversion tolistrmod_monad0.
    rewrite tolisterable_monad_compatibility_spec in tolistm_mhom0.
    destructs_all.
    rewrite <- tolisterable_join_iff.
    rewrite <- tolisterable_join_unpack.
    auto.
  Qed.

  Lemma tolisterable_action_12 :
    TolisterableTransformation (fun A (x : F (T A)) => right_action x) ->
    (forall A (x : F (T A)), tolist (right_action x) = join (tolist (fmap tolist x))).
  Proof.
    introv hyp A x.
    rewrite tolistrmod_action.
    reflexivity.
  Qed.

  Lemma tolisterable_action_23 :
    (forall A (x : F (T A)), tolist (right_action x) = join (tolist (fmap tolist x))) ->
    (forall A (x : F (T A)), tolist (right_action x) = tolist x).
  Proof.
    introv hyp A x.
    rewrite tolistrmod_action.
    reflexivity.
  Qed.

  Lemma tolisterable_action_31 :
    (forall A (x : F (T A)), tolist (right_action x) = tolist x) ->
    TolisterableTransformation (fun A (x : F (T A)) => right_action x).
  Proof.
    intros hyp. constructor.
    - intros; eauto.
    - inversion module.
      inversion tolistrmod_module0.
      auto.
  Qed.

  Lemma tolistrmod_action_alt : forall A (x : F (T A)), enum (right_action x) = join (enum (fmap (F := F) enum x)).
  Proof.
    inversion module.
    intros. rewrite enumrmod_action0.
    reflexivity.
  Qed.

End EnumerableRightModule.
*)
