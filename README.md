# Tealeaves

Tealeaves is a Coq framework for proving theorems about syntax abstractly, i.e. independently of a concrete grammar. This independence makes syntactical theory reusable between developments, and is achieved by separating a choice of grammar from a choice of variable representation. Our central abstraction is a "structured" kind of monad that we call *decorated traversable,* which is an abstract of abstract syntax trees. Tealeaves "core" is a Coq implementation of the equational theory of such monads, as well as higher-level principles built on top of this theory.

## How to build Tealeaves
System requirements:
- `make` (see [GNU Make](https://www.gnu.org/software/make/))
- An installation of Coq >= 8.13 (see the Coq [downloads page](https://coq.inria.fr/download))

Compilation instructions:
- Run `make` in the top-level directory
- Run `make clean` to remove all build artifacts (including compiled files) and start over
 
On multicore systems you may want to use the `-j` flag to use several build threads. We have sometimes observed that `-j` leads to cryptic build errors. The solution to these is simply to re-run the build command again.
 
Tealeaves is built with the [coq_makefile](https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile), which is distributed with Coq itself. This utility generates a customized Makefile to build a Coq project. For simplicity, we provide a top-level `Makefile` which will call `coq_makefile` for you, and then recursively call `make` on the generated Makefile, so that you should not have to do anything except call `make` once in the top-level directory.

## Axioms used in Tealeaves
To be completely clear, Tealeaves currently admits three modest propositions without proof. Two are commonly taken for convenience in Coq, and one is an non-trivial `Admitted` proposition from the literature on traversable functors. Accordingly, none of them threaten the soundness of Coq. The admitted propositions are the following:
- [Propositional extensionality](https://coq.github.io/doc/v8.12/stdlib/Coq.Logic.PropExtensionality.html#propositional_extensionality), which says that equivalent propositions (`P <-> Q`) are computationally equal (`P = Q`)
- [Functional extensionality](https://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html#functional_extensionality), which is the statement `forall x, f x = g x -> f = g`.
- The shapeliness of traversable functors: `t = u <-> tolist t = tolist u /\ shape t = shape u` for all `t, u : T A` and `T` a traversable functor ([admitted here](https://github.com/dunnl/tealeaves/blob/1e69a99b9376506c5c28c243112e74c9282535aa/Tealeaves/Classes/TraversableFunctor.v#L524))

The first two axioms, both assumed [here](https://github.com/dunnl/tealeaves/blob/1e69a99b9376506c5c28c243112e74c9282535aa/Tealeaves/Util/Prelude.v#L6), are a convenience to use Coq's rewriting features. In principle one can eliminate these at the cost of ``setoid hell'' (see [this question](https://stackoverflow.com/questions/65493694/why-do-calculus-of-construction-based-languages-use-setoids-so-much) on StackOverflow). These axioms have been proved on paper to be equi-consistent with Coq itself and are commonly assumed for convenience' sake.

The shapeliness of traversable functors is a non-trivial (but non-surprising) theorem from the literature ([see this paper](https://arxiv.org/abs/1402.1699)). It is generally proved as a corollary of the representation theorem for traversable functors, which roughly states that traversing over a general data structure is equivalent to traversing over its contents as a list, then re-assembling the structure. For a standalone formalization of the representation theorem in Coq, see [here](https://r6.ca/blog/20121209T182914Z.html). To avoid formalizing our own version of this theorem while we develop Tealeaves, we currently admit the shapeliness property without proof. In the future we intend to formalize a generalization of representation theorem for DTMs.

## Basic layout

### Typeclasses
Classes of "structured" functors (like monads, decorated monads, traversable functors, etc.) are found in under `Tealeaves/Classes`. The internal implementation of Tealeaves uses an *algebraic* rather than *Kleisli-style* implementation of our typeclasses, so that operations like `bind` are derived rather than taken as primitive. For example, decorated monads are defined [here](https://github.com/dunnl/tealeaves/blob/master/Tealeaves/Classes/DecoratedMonad.v) as monads equipped with a "decoration" operation. Their equivalent Kleisli presentation is derived [here](https://github.com/dunnl/tealeaves/blob/master/Tealeaves/Classes/DecoratedMonad.v#L200) in the same file. A characterization of decorated functors as comodules of the reader/writer bimonad is found [here](https://github.com/dunnl/tealeaves/blob/master/Tealeaves/Theory/Decorated.v).

### The locally nameless backend 
Our locally nameless backend library is formalized under the `LN/` directory. The operations (opening, closing, local closure, etc) are defined [here](https://github.com/dunnl/tealeaves/blob/master/LN/Operations.v). Various lemmas about these operations, proved polymorphically over a decorated traversable monad `T`, are proved [here](https://github.com/dunnl/tealeaves/blob/master/LN/Theory.v).

### Simply typed lambda calculus
Our formalization of STLC is under the `STLC/` directory. A formalization of STLC's syntax as a DTM is found [here](https://github.com/dunnl/tealeaves/blob/master/STLC/Language.v). Basic metatheory such as a progress theorem are proved [here](https://github.com/dunnl/tealeaves/blob/master/STLC/Theory.v).

## Decorated and traversable monads

The most fundamental idea in Tealeaves is that a decorated-traversable monad has a generalized Kleisli operation `binddt` whose composition law is expressed by the following string diagram. Click the image to see the accompanying theorem formalized in Coq.

[![Generalized Kleisli composition](https://raw.githubusercontent.com/dunnl/tealeaves/master/docs/tealeaves_kleisli_composition.png)](http://comono.id/tealeaves/Tealeaves.Classes.DecoratedTraversableMonad.html#binddt_binddt)

## Technical publications
Tealeaves is a work-in-progress and has no associated publications
yet. Catch our presentation at [CoqPL 2022](https://popl22.sigplan.org/home/CoqPL-2022) in January, which will be streamed and recorded online.
