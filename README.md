# Tealeaves

Tealeaves is a Coq framework for proving theorems about syntax abstractly, i.e. independently of a concrete grammar. This independence makes syntactical theory reusable between developments, and is achieved by separating a choice of grammar from a choice of variable representation. To formalize generic syntactical reasoning in Coq, it is enough to fix the choice of variable representation and find an appropriate substitute for structural recursion on the grammar of terms. This sort of abstract recursion principle, for purposes of defining operations and reasoning about them, is subsumed by the assumption that the grammar forms a "structured" kind of monad that we call *decorated-traversable.* Tealeaves "core" is a Coq implementation of the equational theory of such monads, as well as higher-level principles built on top of this theory.


## Tealeaves workflow
Typically one formalizes a formal system (e.g. a lambda calculus or a logic) by first defining an inductive type `T : Type` of expressions, where the structure of the inductive type essentially corresponds to a context-free grammar. In Tealeaves  we view `T` as parameterized by the concrete representation of variables. To a first approximation, this means `T` is a *functor* of type `T : Type -> Type`.

Any method of representing variables (e.g. as names like with paper-and-pencil proofs, or as de Bruijn indices like with many formalized implementations) is realized by a concrete type `leaf` to represent variables, accompanied by operations on type `T leaf` as well as theorems about these operations. Tealeaves *backends* formalize the theory of a given variable representation in Coq *abstractly* over `T` (but concretely in `leaf`). To remain abstract over `T`, clearly we must have a mechanism taking the place of recursion on the structure of `T`, as well as mechanisms replacing the need for proofs by induction on `T`. To achieve this, a backend must stipulate that `T` is a *decorated traversable monad*, whose central operation `binddt` can be seen as a kind of combinator that lifts operations on `leaf` to operations over `T leaf`. (`binddt` is a high-level generalization of Haskell's `fold`, as well as `bind`, among other higher-order operations). The equational theory of `binddt` is used in lieu of induction on `T`, permitting a style of reasoning about syntax that we find very natural.

The role of Tealeaves "core" is to provide high-level reasoning principles for decorated-traversable monads, to be used by backends. This theory includes the raw equational theory of `binddt`, as well as convenient reasoning principles that can be used, e.g., to prove that two operations defined with `binddt` are equivalent when applied to some subset of expressions (which could be all expressions, or just well-formed or locally-closed expressions, etc.) To role of a Tealeaves "backend" (each of which corresponds to a choice of variable representation) is to define `leaf` and theorize about `T leaf` where `T` is a parameter. A backend uses the reasoning principles provided by Tealeaves to reason about operations defined on `T leaf`.

To use Tealeaves in your own development, you must provide a concrete definition of `T` and an accompanying instance for the `DecoratedTraversableMonad` typeclass (actually we replace `Monad` with `RightModule`, but that's just a detail). Then one can merely import any backend to have access to the operations and theorems of a variable representation. Coq's typeclass mechanism will specialize the backend definitions and theorems to one's instance automatically.

## How to build

Run `make` here in the top-level directory. On multicore systems you may want to use the `-j` flag to use several build threads. We have sometimes observed that `-j` leads to cryptic build errors. The solution to these is simply to re-run the build command again.

## File layout

TODO

## Decorated and traversable monads

The most fundamental idea in Tealeaves is that a decorated-traversable monad has a generalized Kleisli operation `binddt` whose composition law is expressed by the following string diagram. Click the image to see the accompanying theorem formalized in Coq.

[![Generalized Kleisli composition](https://raw.githubusercontent.com/dunnl/tealeaves/master/docs/tealeaves_kleisli_composition.png)](http://comono.id/tealeaves/Tealeaves.Classes.DecoratedTraversableMonad.html#binddt_binddt)

## Technical publications
Tealeaves is a work-in-progress and has no associated publications
yet. Catch our presentation at [CoqPL 2022](https://popl22.sigplan.org/home/CoqPL-2022) in January, which will be streamed and recorded online.
