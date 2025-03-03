From Tealeaves Require Export
  Examples.LambdaNominal.Syntax
  Functors.Subset
  Backends.LN.AtomSet
  Backends.Named.Names.

Require Coq.funind.Recdef.  (* Needed for Function *)


Import Early.Subset.Notations.

Fixpoint fv (t: term name name): subset name :=
  match t with
  | tvar v => {{ v }}
  | tap t1 t2 => fv t1 ∪ fv t2
  | lam b t => fun v => (fv t v) /\  (v <> b)
  end.

Fixpoint remove (x: name) (l: list name) : list name :=
  match l with
  | nil => nil
  | cons y rest =>
      if x == y then remove x rest else cons y (remove x rest)
  end.

Fixpoint remove_all (xs: list name) (l: list name) : list name :=
  match xs with
  | nil => l
  | cons y rest =>
      remove_all rest (remove y l)
  end.

Fixpoint fvL (t: term name name): list name :=
  match t with
  | tvar v => [ v ]
  | tap t1 t2 => fvL t1 ++ fvL t2
  | lam b t => remove b (fvL t)
  end.

Section rw.

  Context {l: list name} {x: name} {u: term name name}.

  Lemma fvL_rw1: forall v,
      fvL (tvar v) = [v].
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma fvL_rw2: forall b t,
      fvL (lam b t) =
        remove b (fvL t).
  Proof.
    reflexivity.
  Qed.

  Lemma fvL_rw3: forall t1 t2,
      fvL (tap t1 t2) = (fvL t1) ++ (fvL t2).
  Proof.
    intros.
    reflexivity.
  Qed.

End rw.

(* Depth function for well-founded recursion *)
Fixpoint depth (t : term name name) : nat :=
  match t with
  | tvar _ => 0
  | lam b t => S (depth t)
  | tap t1 t2 => S (max (depth t1) (depth t2))
  end.

About Acc_inv.

(* Well-founded measure for lexicographic ordering *)

Definition term_lt (t1 t2: term name name) : Prop := depth t1 < depth t2.

Lemma term_lt_wf : well_founded term_lt.
Proof.
  unfold well_founded. intro t.
  induction t; intros.
  - constructor; intros.
    inversion H.
  - constructor.
    intro u.
    introv H_u_lt.
    assert (depth u <= depth t).
    { unfold term_lt in *.
      cbn in H_u_lt.
      lia. }
    constructor.
    introv Hlt.
    inversion IHt.
    apply H0.
    unfold term_lt in *.
    lia.
  - constructor.
    introv Hlt.
    inversion IHt1.
    inversion IHt2.
    unfold term_lt in Hlt.
    constructor.
    introv Hlt'.
    unfold term_lt in Hlt'.
    cbn in Hlt.
    assert (depth y0 < depth t1 \/ depth y0 < depth t2).
    lia.
    destruct H1.
    apply H; auto.
    apply H0; auto.
Qed.


Definition tap_Acc1: forall t1 t2,
    Acc term_lt (tap t1 t2) -> Acc term_lt t1.
Proof.
  intros.
  inversion H.
  apply H0.
  unfold term_lt.
  cbn. lia.
Defined.

Definition tap_Acc2: forall t1 t2,
    Acc term_lt (tap t1 t2) -> Acc term_lt t2.
Proof.
  intros.
  inversion H.
  apply H0.
  unfold term_lt.
  cbn. lia.
Defined.

Definition tap_depth1: forall t1 t2,
    term_lt t1 (tap t1 t2).
Proof.
  intros.
  unfold term_lt.
  cbn. lia.
Defined.

Definition tap_depth2: forall t1 t2,
    term_lt t2 (tap t1 t2).
Proof.
  intros.
  unfold term_lt.
  cbn. lia.
Defined.

Check ex.
Print ex.
Search sig.
Search sig.
Print sig.
Definition rename':
  forall (l: list name) (x y: name) (t: term name name),
    Acc term_lt t -> {u : term name name | depth u = depth t}.
Proof.
  refine (fix rename l x y t (Ht: Acc term_lt t) {struct Ht} :=
    (match t as t' return ((forall x, term_lt x t' -> term_lt x t) -> {u : term name name | depth u = depth t'}) with
    | tvar v =>
        fun phi =>
          if x == v
          then (@exist _ _ (tvar y) _)
          else (@exist _ _ (tvar v) _)
    | tap t1 t2 =>
        fun phi =>
        match (rename l x y t1 (Acc_inv Ht t1 (phi t1 (tap_depth1 t1 t2)))) with
        | exist _ t1' pf1' =>
            match (rename l x y t2 (Acc_inv Ht t2 (phi t2 (tap_depth2 t1 t2)))) with
            | exist _ t2' pf2' =>
                (@exist _ _ (tap t1' t2') (_ pf1' pf2'))
            end
        end
    | lam b t' =>
        fun phi =>
        if b == x then (@exist _ _ (lam b t') _)
        else if b == y then
               let z := fresh ([x] ++ l ++ [b]) in
               match (rename l b z t' (Acc_inv Ht t' _)) with
               | exist _ tm pf =>
                   match (rename l x y tm (Acc_inv Ht _)) with
                   | exist _ tm' pf' =>
                       @exist _ _ (lam z tm') _
                   end
               end
        else  match (rename l x y t' ((Acc_inv Ht t' _))) with
                   | exist _ tm pf =>
                       (@exist _ _ (lam b tm) _)
              end
    end) (fun x y => y) ).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply phi.
    unfold term_lt.
    cbn. lia.
  - apply phi.
    unfold term_lt.
    cbn.
    subst. lia.
  - cbn.
    rewrite pf'.
    rewrite pf.
    reflexivity.
  - apply phi.
    unfold term_lt.
    cbn.
    lia.
  - cbn.
    rewrite pf.
    reflexivity.
  - cbn.
    rewrite pf1'.
    rewrite pf2'.
    reflexivity.
Defined.


Lemma wf: forall (t: term name name), Acc term_lt t.
Admitted.

Definition rename :
  forall (l: list name) (x y: name) (t: term name name), term name name.
Proof.
  intros.
  pose (rename' l x y t (wf t)).
  destruct s as [me you].
  exact me.
Defined.


Definition rename_iter:
  forall (l: list name) (x y: name) (t: term name name), term name name :=
  fun l x y t =>
    match t with
    | tvar v =>
        if x == v
        then tvar y
        else tvar v
    | tap t1 t2 =>
        tap (rename l x y t1) (rename l x y t2)
    | lam b t' =>
        if b == x then lam b t'
        else if b == y
             then let z := fresh ([x] ++ l ++ [b])
                  in lam z (rename l x y (rename (l ++ [b]) b z t'))
             else lam b (rename l x y t')
    end.

(*
Program Fixpoint rename (l: list name) (x: name) (y: name) (t: term name name)
  {wf term_lt t}
  : term name name :=
  match t with
  | tvar v => if x == v then tvar y else tvar v
  | tap t1 t2 => tap (rename l x y t1) (rename l x y t2)
  | lam b t =>
      if b == x then lam b t
      else if b == y
           then let z := (fresh ([x] ++ l ++ [b]): name) in
                lam z (rename l x y (rename l b y t))
      else lam b (rename l x y t)
  end.
Next Obligation.
  unfold term_lt.
  cbn.
  lia.
Qed.

Next Obligation.
  unfold term_lt, term_measure.
  cbn.
  lia.
Qed.

Next Obligation.
  unfold term_lt, term_measure.
  cbn.
  lia.
Defined.

Next Obligation.
  unfold term_lt.
  unfold term_measure.

  cbn.
Admitted.

Next Obligation.
  unfold term_lt, term_measure.
  cbn.
  lia.
Qed.

Next Obligation.
  unfold term_lt, term_measure.
Abort.
*)


Section rw.

  Context {l: list name} {x: name} {y: name}.

  Lemma test: forall (A: Type) (P: A -> Prop) (x: {a: A | P a}) (y: {a: A | P a}),
      proj1_sig x = proj1_sig y ->
      x = y.
  Proof.
    intros.
    destruct x0.
    destruct y0.
    cbn in *.
    subst.
    fequal.
    apply proof_irrelevance.
  Qed.

  Lemma rename_eq_iter': forall t Hacc,
      proj1_sig (rename' l x y t Hacc) = (rename_iter l x y t).
  Proof.
    intro t.
    induction t; intro HAcc.
    - cbn.
      destruct HAcc.
      destruct_eq_args x v.
      + cbn.
        destruct_eq_args v v.
      + cbn.
        destruct_eq_args v v.
        destruct_eq_args x v.
    - destruct HAcc.
      cbn.
      destruct_eq_args b x.
      destruct_eq_args b y.
      Search sig "eta".
      rewrite sig_eta.
      + eauto.
      + destruct_eq_args b y.


  Lemma rename_eq_iter': forall t Hacc,
      exists pf, rename' l x y t Hacc = @exist _ _ (rename_iter l x y t) pf.
  Proof.
    intro t.
    induction t; intro HAcc.
    - cbn.
      destruct HAcc.
      destruct_eq_args x v.
      + cbn.
        destruct_eq_args v v.
        eauto.
      + cbn.
        destruct_eq_args v v.
        destruct_eq_args x v.
        eauto.
    - destruct HAcc.
      cbn.
      destruct_eq_args b x.
      + eauto.
      + destruct_eq_args b y.

    - destruct (HAcc).
      cbn.
      destruct (IHt1 (a t1 (tap_depth1 t1 t2))) as [Step1Depth Step1Eq].
      rewrite Step1Eq.
      destruct (IHt2 (a t2 (tap_depth2 t1 t2))) as [Step2Depth Step2Eq].
      rewrite Step2Eq.
      eexists.
      unfold rename.
      destruct (IHt1 (wf t1)) as [Step1Depth' Step1Eq'].
      destruct (IHt2 (wf t2)) as [Step2Depth' Step2Eq'].
      apply test. cbn.
      rewrite Step1Eq'.
      rewrite Step2Eq'.
      reflexivity.
      Unshelve.

      destruct (IHt1 (wf t1)) as [Step1Depth' Step1Eq'].
      destruct (IHt2 (wf t2)) as [Step2Depth' Step2Eq'].
      rewrite Step1
      reflexivity.
  Qed.

      exists (ltac:(reflexivity)).
      destruct (rename' l v
      fequal.

  Lemma rename_eq_iter: forall t,
      rename l x y t = rename_iter l x y t.
  Proof.
    intros.
    unfold rename.
    generalize dependent (wf t).
    induction t; intro HAcc.
    - destruct HAcc.
      cbn.
      destruct_eq_args x v.
    - destruct HAcc.
      cbn.
      destruct_eq_args x b.
      destruct_eq_args b y.
      + admit.
      + admit.
    - destruct HAcc.
      cbn.
      assert (
      assert (t1' = rename l x y t1).
      unfold rename at 1.
      unfold rename at 1.
      rewrite IHt1.
      rewrite IHt2.

      rewrite
      destruct (rename' l x y t1 (a t1 (tap_depth1 t1 t2))).
      destruct (rename' l x y t2 (a t2 (tap_depth2 t1 t2))).
      fequal.

        .
    i



  Lemma rename_rw1: forall v,
      rename l x y (tvar v) = tvar (if v == x then y else v).
  Proof.
    intros.
    unfold rename.
    destruct (wf (tvar v)).
    unfold rename'.
    destruct_eq_args x v.
  Qed.

  Lemma rename_rw2_eq: forall b t,
      b = x ->
      rename l x y (lam b t) =
        lam b t.
  Proof.
    intros.
    unfold rename.
    destruct (wf (λ b t)).
    unfold rename'.
    destruct_eq_args b x.
  Qed.

  Lemma rename_rw2_neq: forall b t,
      b <> x ->
      b = y ->
      rename l x y (lam b t) =
        (λ) (fresh ([x] ++ l ++ [b])) (rename l x y
                                         (rename (l ++ [fresh ([x] ++ l ++ [b])]) b (fresh ([x] ++ l ++ [b])) t)).
  Proof.
    intros.
    unfold rename.
    destruct (wf (λ b t)).
    remember (rename' ([x] ++ l ++ [fresh ([x] ++ l ++ [b])]) b (fresh ([x] ++ l ++ [b])) t (wf t)) as Rem.
    remember (let (x0, _) := Rem in x0) as Rem'.
    destruct (wf Rem').
    unfold rename'.
    subst.
    destruct_eq_args x y.
    destruct_eq_args y y.
    reflexivity.
    intros.
    cbn.
    destruct_eq_args b x.
  Qed.

  Lemma rename_rw3: forall t1 t2,
      rename x y (tap t1 t2) = tap (rename x y t1) (rename x y t2).
  Proof.
    intros.
    reflexivity.
  Qed.

End rw.
*)



(* Capture-avoiding substitution with well-founded recursion *)
Function substRaw (l: list name) (* l is the avoid set *)
  (x : name) (u : term name name)
  (t : term name name)
  {measure term_measure t}
  : term name name :=
  match t with
  | tvar y => if y == x then u else tvar y
  | tap t1 t2 =>
      tap (substRaw l x u t1) (substRaw l x u t2)
  | lam b t =>
      if b == x then lam b t
      else if SmartAtom.name_inb b (fvL u)
           then let z := (fresh ([x] ++ l ++ [b]): name) in
                lam z (substRaw (l ++ [z]) x u (substRaw l b (tvar z) t))
           else lam b (substRaw (l ++ [b]) x u t)
  end.
Proof.
  all: unfold term_measure.
  - intros.
    rewrite depth_rename_eq.
    cbn. lia.
  - intros.
    cbn.
    lia.
  - intros.
    cbn.
    lia.
  - intros.
    cbn.
    lia.
Qed.


(* Capture-avoiding substitution with well-founded recursion *)
Function substF (l: list name) (* l is the avoid set *)
  (x : name) (u : term name name)
  (t : term name name)
  {measure term_measure t}
  : term name name :=
  match t with
  | tvar y => if y == x then u else tvar y
  | tap t1 t2 =>
      tap (substF l x u t1) (substF l x u t2)
  | lam b t =>
      if b == x then lam b t
      else if SmartAtom.name_inb b (fvL u)
           then let z := (fresh ([x] ++ l ++ [b]): name) in
                lam z (substF (l ++ [z]) x u (rename b z t))
           else lam b (substF (l ++ [b]) x u t)
  end.
Proof.
  all: unfold term_measure.
  - intros.
    rewrite depth_rename_eq.
    cbn. lia.
  - intros.
    cbn.
    lia.
  - intros.
    cbn.
    lia.
  - intros.
    cbn.
    lia.
Qed.

Section rw.

  Context {l: list name} {x: name} {u: term name name}.

  Lemma substF_rw1: forall v,
      substF l x u (tvar v) = (if v == x then u else tvar v).
  Proof.
    intros.
    rewrite substF_equation.
    reflexivity.
  Qed.

  Lemma substF_rw2: forall b t,
      substF l x u (lam b t) =
        (if b == x
   then (λ) b t
   else
    if SmartAtom.name_inb b (fvL u)
    then
     (λ) (fresh ([x] ++ l ++ [b]))
       (substF (l ++ [fresh ([x] ++ l ++ [b])]) x u (rename b (fresh ([x] ++ l ++ [b])) t))
    else (λ) b (substF (l ++ [b]) x u t)).
  Proof.
    intros.
    rewrite substF_equation.
    reflexivity.
  Qed.

  Lemma substF_rw3: forall t1 t2,
      substF l x u (tap t1 t2) = tap (substF l x u t1) (substF l x u t2).
  Proof.
    intros.
    rewrite substF_equation.
    reflexivity.
  Qed.

End rw.

Definition subst (x : name) (u : term name name) (t : term name name) :=
  substF (fvL t ++ fvL u) x u t.
