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

Fixpoint rename (x: name) (y: name) (t: term name name): term name name :=
  match t with
  | tvar v => if x == v then tvar y else tvar v
  | tap t1 t2 => tap (rename x y t1) (rename x y t2)
  | lam b t => if b == x then lam b t
              else lam b (rename x y t)
  end.

Section rw.

  Context {l: list name} {x: name} {y: name}.

  Lemma rename_rw1: forall v,
      rename x y (tvar v) = tvar (if v == x then y else v).
  Proof.
    intros.
    cbn.
    destruct_eq_args x v.
  Qed.

  Lemma rename_rw2_eq: forall b t,
      b = x ->
      rename x y (lam b t) =
        lam b t.
  Proof.
    intros.
    cbn.
    destruct_eq_args b x.
  Qed.

  Lemma rename_rw2_neq: forall b t,
      b <> x ->
      rename x y (lam b t) =
        (λ) b (rename x y t).
  Proof.
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


(* Depth function for well-founded recursion *)
Fixpoint depth (t : term name name) : nat :=
  match t with
  | tvar _ => 0
  | lam b t => S (depth t)
  | tap t1 t2 => S (max (depth t1) (depth t2))
  end.

(* Well-founded measure for lexicographic ordering *)
Definition term_measure (t : term name name) : nat := depth t.

Lemma depth_rename_eq:
  forall (x y : name) (t : term name name),
    depth (rename x y t) = depth t.
Proof.
  intros.
  induction t.
  - cbn. destruct_eq_args x v.
  - cbn. destruct_eq_args x b.
    cbn.
    rewrite IHt.
    reflexivity.
  - cbn. lia.
Qed.


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
