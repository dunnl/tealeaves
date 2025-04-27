From Tealeaves Require Import
  Backends.Nominal.Common.Freshening
  Backends.Nominal.Common.Binding
  Backends.Nominal.FV
  Kleisli.DecoratedMonadPoly.

Section ops.

  Context
    {T: Type -> Type -> Type}
    `{forall W, Return (T W)}
    `{Mapdt (list name) (T name)}
    `{BinddP T}.

  Section rename_local.

    Context
      (Γ: list name)
      (x: name)
      (u: T name name).

    Definition subst_loc:
      list name * name -> T name name :=
      fun '(ctx, v) =>
        match get_binding ctx v with
        | Unbound _ _ =>
            if v == x
            then u
            else ret v
        | Bound prefix _ post =>
            ret (renb_ctx Γ (prefix, v))
        end.

  End rename_local.

  Definition subst_top
    (Γ: list name)
    (x: name) (u: T name name)
    (t: T name name): T name name :=
    binddp (T := T)
      (renb_ctx Γ)
      (subst_loc Γ x u) t.

  Definition subst
    (x: name) (u: T name name)
    (t: T name name): T name name :=
    subst_top (FV t ++ FV u) x u t.

End ops.
