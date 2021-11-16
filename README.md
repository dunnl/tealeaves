# Tealeaves

Tealeaves is a Coq library for proving theorems about syntax
abstractly. More specifically, for any concrete choice about how to
represent variables and binders (e.g. as names like with
paper-and-pencil proofs, or as de Bruijn indices like with many
computer-formalized proofs), you can use Tealeaves to define the
operations of this representation, such as capture-avoiding
substitution or a well-formedness predicate and prove theorems about
these operations abstractly. By "abstractly" we mean that these
theorems and definitions are polymorphic over syntax. It is then
possible to use these polymorphic operations and theorems with any
concrete syntax by providing a certain typeclass instance for the syntax, that of a
decorated traversable monad.

[![Generalized Kleisli composition](https://raw.githubusercontent.com/dunnl/tealeaves/master/docs/tealeaves_kleisli_composition.png)](http://comono.id/tealeaves/Tealeaves.Singlesorted.Classes.DecoratedTraversableMonad.html#kcomposedtm)

## Technical publications
Tealeaves is a work-in-progress and has no associated publications
yet. At the moment it would be a bad idea to rely on anything in this
repo!
