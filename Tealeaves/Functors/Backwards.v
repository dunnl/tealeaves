From Tealeaves Require Export
  Classes.Categorical.Applicative
  Classes.Kleisli.TraversableFunctor
  Functors.List.

Import Applicative.Notations.

#[local] Generalizable Variables F.

(** * The <<Backwards>> idiom *)
(******************************************************************************)
Section Backwards.

  Record Backwards (F : Type -> Type) A :=
    mkBackwards { forwards : F A }.

  #[global] Arguments mkBackwards {F}%function_scope {A}%type_scope forwards.
  #[global] Arguments forwards {F}%function_scope {A}%type_scope b.

  (** ** Functor instance *)
  (******************************************************************************)
  Section functor.

    Context `{Functor F}.

    #[export] Instance Map_Backwards: Map (Backwards F) :=
      fun A B f b => mkBackwards (map f (forwards b)).

    #[export] Instance Functor_Backwards: Functor (Backwards F).
    Proof.
      constructor.
      - intros. ext [x].
        unfold_ops Map_Backwards.
        rewrite fun_map_id.
        reflexivity.
      - intros. ext [x].
        unfold_ops Map_Backwards.
        rewrite <- fun_map_map.
        reflexivity.
    Qed.

  End functor.

  (** ** Applicative instance *)
  (******************************************************************************)
  Section applicative.

    Context
      `{Applicative F}.

    #[export] Instance Pure_Backwards : Pure (Backwards F) :=
      fun A a => mkBackwards (pure a).

    Definition swap {A B} : B * A -> A * B :=
      fun '(b, a) => (a, b).

    Definition mult_Backwards {A B} :
      Backwards F A -> Backwards F B -> Backwards F (A * B) :=
      fun ba bb => mkBackwards (map swap (forwards bb ⊗ forwards ba)).

    #[export] Instance Mult_Backwards : Mult (Backwards F) :=
      fun A B '(x, y) => mult_Backwards x y.

    #[export] Instance Applicative_Backwards : Applicative (Backwards F).
    Proof.
      constructor;
        intros;
        unfold_ops Pure_Backwards;
        unfold_ops @Map_Backwards;
        unfold_ops @Mult_Backwards;
        unfold mult_Backwards;
        cbn.
      - typeclasses eauto.
      - now rewrite app_pure_natural.
      - fequal.
        rewrite app_mult_natural.
        compose near (forwards y ⊗ forwards x).
        do 2 rewrite fun_map_map.
        fequal.
        now ext [p q].
      - fequal.
        rewrite (app_mult_natural_r F).
        rewrite (app_mult_natural_l F).
        rewrite <- (app_assoc).
        compose near (forwards z ⊗ forwards y ⊗ forwards x) on left.
        compose near (forwards z ⊗ forwards y ⊗ forwards x) on left.
        compose near (forwards z ⊗ forwards y ⊗ forwards x) on left.
        compose near (forwards z ⊗ forwards y ⊗ forwards x) on right.
        repeat rewrite (fun_map_map).
        fequal.
        ext [[c b] a].
        reflexivity.
      - destruct x as [forward].
        cbn.
        fequal.
        compose near (forward ⊗ pure tt).
        rewrite (fun_map_map).
        replace (left_unitor ∘ swap) with (@right_unitor A).
        now rewrite app_unital_r.
        now ext [a tt].
      - destruct x as [forward].
        cbn.
        fequal.
        compose near (pure tt ⊗ forward).
        rewrite (fun_map_map).
        replace (right_unitor ∘ swap) with (@left_unitor A).
        now rewrite app_unital_l.
        now ext [a tt].
      - fequal.
        rewrite app_mult_pure.
        rewrite app_pure_natural.
        reflexivity.
    Qed.

  End applicative.

  (** ** Involutive properties *)
  (******************************************************************************)
  Section involution.

    Context
      {T G : Type -> Type}
        `{TraversableFunctor T}
        `{Applicative G}.

    Instance double_forwards:
      ApplicativeMorphism (Backwards (Backwards G)) G
                          (fun A => forwards ∘ forwards).
    Proof.
      constructor;
        try typeclasses eauto;
        intros;
        repeat (match goal with
                | x : Backwards (Backwards G) ?A
                  |- _ =>
                    destruct x as [[x]]
                end);
        try easy; cbn.
      compose near (x ⊗ y).
      rewrite fun_map_map.
      replace (swap ∘ swap) with (@id (A * B)).
      now rewrite fun_map_id.
      now ext [a b].
    Qed.

    Instance double_backwards:
      ApplicativeMorphism G (Backwards (Backwards G))
                          (fun A => mkBackwards ∘ mkBackwards).
    Proof.
      constructor;
        try typeclasses eauto;
        intros;
        repeat (match goal with
                | x : Backwards (Backwards G) ?A
                  |- _ =>
                    destruct x as [[x]]
                end);
        try easy; cbn.
      unfold compose.
      unfold_ops @Mult_Backwards.
      unfold mult_Backwards.
      cbn.
      fequal.
      unfold_ops @Map_Backwards.
      cbn.
      do 2 fequal.
      compose near (x ⊗ y).
      rewrite fun_map_map.
      replace (swap ∘ swap) with (@id (A * B)).
      now rewrite fun_map_id.
      now ext [a b].
    Qed.

    Context
      {A B: Type}
        {f: A -> G B}
        (t: T A).

    Lemma traverse_double_backwards:
      forwards (forwards
                  (traverse (G := Backwards (Backwards G))
                            (mkBackwards ∘ (mkBackwards ∘ f)) t)) =
        traverse f t.
    Proof.
      intros.
      compose near t on left.
      change_left (((forwards ∘ forwards)
                      ∘ traverse (T := T)
                      (G := Backwards (Backwards G))
                      (mkBackwards ∘ (mkBackwards ∘ f))) t).
      rewrite (trf_traverse_morphism (morphism := double_forwards)).
      reflexivity.
    Qed.

  End involution.

  (** ** Misc *)
  (******************************************************************************)
  Lemma forwards_ap {G} `{Applicative G}:
    forall {A B: Type} (f: (Backwards G) (A -> B)) (a : (Backwards G) A),
      forwards (f <⋆> a) =
        map evalAt (forwards a) <⋆> forwards f.
  Proof.
    intros.
    cbn.
    unfold ap.
    rewrite (app_mult_natural_l G).
    compose near (forwards a ⊗ forwards  f).
    do 2 rewrite (fun_map_map).
    fequal.
    now ext [p q].
  Qed.

   Lemma traverse_backwards_list1 {G} `{Applicative G}:
     forall {A B: Type} (f: A -> G B) (l: list A),
       traverse f l =
         map (@List.rev B)
           (forwards
              (traverse (G := Backwards G)
                 (mkBackwards ∘ f)
                 (List.rev l))).
   Proof.
     intros.
     induction l.
     - cbn.
       rewrite app_pure_natural.
       reflexivity.
     - cbn.
       (* left *)
       rewrite IHl.
       rewrite map_to_ap.
       repeat rewrite <- ap4;
         repeat rewrite ap2.
       rewrite ap3;
         repeat rewrite <- ap4;
         repeat rewrite ap2.
       unfold compose.
       assert (cut: (fun (b:B) => cons b ○ List.rev (A := B)) =
                 (compose (List.rev (A := B)) ∘ Basics.flip (@snoc B))).
       { ext x y. unfold compose, Basics.flip, snoc.
         rewrite List.rev_unit.
         reflexivity. }
       rewrite cut.
       (* right *)
       rewrite traverse_list_snoc; [|typeclasses eauto].
       change (map ?f (forwards ?x)) with
         (forwards (map f x)).
       rewrite map_to_ap.
       repeat rewrite <- ap4;
         repeat rewrite ap2.
       rewrite forwards_ap.
       rewrite forwards_ap.
       rewrite map_to_ap;
       repeat rewrite <- ap4;
         repeat rewrite ap2.
       cbn.
       rewrite map_to_ap;
       repeat rewrite <- ap4;
         repeat rewrite ap2.
       rewrite ap3;
       repeat rewrite <- ap4;
         repeat rewrite ap2.
       rewrite ap3;
       repeat rewrite <- ap4;
         repeat rewrite ap2.
       reflexivity.
   Qed.

   Lemma traverse_backwards_list2 {G} `{Applicative G}:
     forall {A B: Type} (f: A -> G B) (l: list A),
       traverse f (List.rev l) =
           forwards (map (List.rev (A:=B))
                       (traverse (G := Backwards G)
                          (mkBackwards ∘ f) l)).
   Proof.
     intros.
     rewrite traverse_backwards_list1.
     change (map ?f (forwards ?x)) with
       (forwards (map f x)).
     rewrite List.rev_involutive.
     reflexivity.
   Qed.

End Backwards.

