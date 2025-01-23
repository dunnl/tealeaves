(** ** Some things to think about *)

(** ** <<Join>> in terms of Kleisli Composition *)
(******************************************************************************)
Check (@kc T Return_inst (@Bind_Binddt W T T Bindd_T_inst)
         (T (T A)) (T A) A (@id (T A)) (@id (T (T A)))).

Many interesting properties have the forms like
  join = id ⋆ id
           cojoin = (id ⋆1 id)
                       or some such












  (** * Traversable Monads *)





























(** Dec Tra Monads *)

