(** ** Writable instance *)
(*
Fixpoint write_ {A} (l : list typ) (t : term A) : term A :=
  match l with
  | nil => t
  | cons τ rest => Lam τ (write_ rest t)
  end.

Definition write {A} (p : list typ * term A) : term A :=
  match p with | (l, t) => write_ l t end.

Theorem write_nat : forall `(f : A -> B) (w : list typ) (x : term A),
    fmap f (write (w, x)) = write (w, fmap f x).
Proof.
  intros. symmetry. cbn.
  induction x.
  - cbn. induction w.
    + reflexivity.
    + cbn. f_equal. apply IHw.
  - cbn. induction w.
    + reflexivity.
    + cbn. inversion IHx. rewrite IHw; auto.
  - cbn. induction w.
    + reflexivity.
    + cbn. inversion IHx1.
      inversion IHx2. rewrite IHw; auto.
Qed.

Theorem write_unit {A} : forall (x : term A),
    write (List.nil, x) = x.
Proof.
  reflexivity.
Qed.

Theorem write_write : forall (w1 w2 : list typ) `(x : term A),
    write (w1, write (w2, x)) = write (w1 ● w2, x).
Proof.
  intros. induction w1; induction w2.
  - reflexivity.
  - cbn. f_equal; auto.
  - cbn. f_equal. auto.
  - cbn. f_equal. auto.
Qed.

Theorem write_tolist : forall (w : list typ) `(x : term A),
    tolist (write (w, x)) = tolist x.
Proof.
  induction x; cbn; induction w; auto.
Qed.

Theorem write_join : forall A (w : list typ) (t : term (term A)),
    write (w, join t) = join (write (w, t)).
Proof.
  intros. induction w.
  - reflexivity.
  - cbn. f_equal; auto.
Qed.

Theorem dec_write : forall (w : nat) `(x : term A),
        dec (write (w, x)) = write (w, shift w (dec x)).
Proof.
  intros. induction w.
  - cbn. rewrite shift_zero.
    reflexivity.
  - cbn. f_equal. unfold write in *. rewrite IHw.
Admitted.
 *)
