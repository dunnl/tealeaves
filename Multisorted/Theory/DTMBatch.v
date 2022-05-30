(** * DTMs as (particular) <<Batch>> coalgebras *)
(******************************************************************************)
Section traversals_coalgebras.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Definition batch {A : Type} (B : Type) : K -> A -> @Batch (Tag A) B B :=
    fun k a => Go (@id B) ⧆ (k, a).
  Definition iterate {A : Type} (B : Type) : S A -> @Batch (Tag A) B (S B) :=
    mfmapt S (@Batch (Tag A) B) (batch B).

  Definition batchd {A : Type} (B : Type) : K -> W * A -> @Batch (W * Tag A) B B :=
    fun k '(w, a) => Go (@id B) ⧆ (w, (k, a)).
  Definition iterated {A : Type} (B : Type) : S A -> @Batch (W * Tag A) B (S B) :=
    mfmapdt S (@Batch (W * Tag A) B) (batchd B).

End traversals_coalgebras.

(** ** Decomposing traversals in terms of <<iterate>> *)
(******************************************************************************)
Section traversal_iterate.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma iterate_to_iterated `{Applicative F} `(f : K -> A -> F B) (t : S A) :
    runBatch (uncurry f) (iterate B t) = runBatch (fun '(w, (k, a)) => f k a) (iterated B t).
  Proof.
    unfold iterated. unfold iterate. unfold mfmapt. unfold mfmapdt. unfold mbindt.
    compose near t.
    rewrite (dtp_mbinddt_morphism W S T _ _ (ϕ := @runBatch (W * Tag A) F B _ _ _ _)).
    rewrite (dtp_mbinddt_morphism W S T _ _ (ϕ := @runBatch (Tag A) F B _ _ _ _)).
    fequal. now ext k [w a].
  Qed.

  Lemma iterate_to_iterated2 `(f : K -> A -> B) (t : S A) :
    runBatch (uncurry f) (iterate B t) = runBatch (fun '(w, (k, a)) => f k a) (iterated B t).
  Proof.
    apply (iterate_to_iterated (F := fun x => x)).
  Qed.

  (** ** Identities for <<mfmapdt>>, <<mfmapd>> *)
  (******************************************************************************)
  Lemma mfmapdt_to_runBatch `{Applicative F} `(f : K -> W * A -> F B) (t : S A) :
    mfmapdt S F f t = runBatch (fun '(w, (k, a)) => f k (w, a)) (iterated B t).
  Proof.
    unfold iterated, mfmapdt.
    compose near t on right.
    rewrite (dtp_mbinddt_morphism W S T _ _ (ϕ := @runBatch (W * Tag A) F B _ _ _ _)).
    fequal. ext k [w a]. unfold compose; cbn. now rewrite <- fmap_to_ap.
  Qed.

  Lemma mfmapd_to_runBatch `(f : K -> W * A -> B) (t : S A) :
    mfmapd S f t = runBatch (fun '(w, (k, a)) => f k (w, a)) (iterated B t).
  Proof.
    unfold mfmapd.
    now rewrite mfmapdt_to_runBatch.
  Qed.

  (** ** Identities for <<mfmapt>>, <<mfmap>> *)
  (******************************************************************************)
  Lemma mfmapt_to_runBatch `{Applicative F} `(f : K -> A -> F B) (t : S A) :
    mfmapt S F f t = runBatch (uncurry f) (iterate B t).
  Proof.
    unfold iterate, mfmapt, mbindt.
    compose near t on right.
    rewrite (dtp_mbinddt_morphism W S T _ _ (ϕ := @runBatch (Tag A) F B (uncurry f) _ _ _)).
    fequal. ext k [w a]. unfold compose; cbn. now rewrite <- fmap_to_ap.
  Qed.

  Lemma mfmap_to_runBatch `(f : K -> A -> B) (t : S A) :
    mfmap S f t = runBatch (uncurry f) (iterate B t).
  Proof.
    unfold mfmap, mfmapd.
    rewrite mfmapdt_to_runBatch.
    rewrite (iterate_to_iterated (F := fun x => x)).
    easy.
  Qed.

  (** ** Identities for <<tolist>> and <<foldMap>> *)
  (******************************************************************************)
  Lemma tomlistd_gen_to_runBatch `{Applicative F} `(t : S A) (fake : Type) :
    tomlistd_gen S fake t = runBatch (ret list : _ -> const (list (W * Tag A)) _) (iterated fake t).
  Proof.
    unfold tomlistd_gen. rewrite mfmapdt_to_runBatch.
    fequal. now ext [w [k a]].
  Qed.

  Lemma tomlistd_to_runBatch `{Applicative F} `(t : S A) :
    tomlistd S t = runBatch (ret list : _ -> const (list (W * Tag A)) _) (iterated (W * Tag A) t).
  Proof.
    unfold iterate. unfold tomlistd, tomlistd_gen.
    rewrite mfmapdt_to_runBatch. unfold iterated.
    admit.
  Admitted.
bbbbbbbbbb
  Lemma tomlist_to_runBatch `{Applicative F} `(t : S A) :
    tomlist S t = runBatch (ret list : Tag A -> const (list (Tag A)) (Tag A)) (iterate (Tag A) t).
  Proof.
    unfold iterate. unfold tomlist.
  Admitted.

  (** ** Other identities *)
  (******************************************************************************)
  Lemma id_to_runBatch `{Applicative F} `(t : S A) (fake : Type) :
    t = runBatch (F := fun x => x) (fun '(w, (k, a)) => a)
                 (iterated A t : @Batch (W * Tag A) A (S A)).
  Proof.
    change t with (id t).
    rewrite <- (dtp_mbinddt_mret W S T).
    unfold iterated.
  Admitted.

End traversal_iterate.

(** * Shapeliness *)
(******************************************************************************)
Section DTM_shapeliness.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Theorem shapeliness : forall A (t1 t2 : S A),
      shape S t1 = shape S t2 /\
      tomlistd S t1 = tomlistd S t2 ->
      t1 = t2.
  Proof.
    introv [hyp1 hyp2].
    unfold shape in hyp1.
    do 2 rewrite mfmap_to_runBatch in hyp1.
    do 2 rewrite (iterate_to_iterated (F := fun x => x)) in hyp1.
    unfold tomlistd in hyp2.
    rewrite (tomlistd_equiv S False unit) in hyp2.
    rewrite (tomlistd_gen_to_runBatch t1 unit) in hyp2.
    rewrite (tomlistd_gen_to_runBatch t2 unit) in hyp2.
    rewrite (id_to_runBatch t1 unit).
    rewrite (id_to_runBatch t2 unit).
  Admitted.

End DTM_shapeliness.

(** ** <<ret>> is always injective *)
(******************************************************************************)
Section DTM_unit_injective.

  Context
    {S : Type -> Type}
    `{DTPreModule W S T}
    `{! DTM W T}.

  Lemma DTM_unit_injective : forall (A : Type) (a1 a2 : A) (k : K),
      mret T k a1 = mret T k a2 -> a1 = a2.
  Proof.
    introv heq.
    cut (tomlist (T k) (mret T k a1) = tomlist (T k) (mret T k a2)).
    { do 2 rewrite tomlist_mret. now inversion 1. }
    now rewrite heq.
  Qed.

End DTM_unit_injective.
