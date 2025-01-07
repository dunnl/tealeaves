# Tealeaves

Tealeaves is a Coq framework for proving theorems about syntax abstractly, i.e. independently of a concrete grammar. This independence makes syntactical theory reusable between developments, and is achieved by separating a choice of grammar from a choice of variable representation. Our central abstraction is a "structured" kind of monad that we call *decorated traversable,* which is an abstraction of abstract syntax trees. Tealeaves "core" is a Coq implementation of the equational theory of such monads, as well as higher-level principles built on top of this theory.

![Abstract syntax tree](/images/tree.svg)

## How to build Tealeaves
System requirements:
- `make` (see [GNU Make](https://www.gnu.org/software/make/))
- [Autosubst](https://github.com/coq-community/autosubst/tree/master)
- An installation of [Coq](https://coq.inria.fr/download). This branch has been tested with Coq 8.16.

Compilation instructions:
- Run `make` in the top-level directory
- Run `make clean` to remove all build artifacts (including compiled files) and start over
- By default `make` generates Coqdocs under `html`
- Run `make alectryon` (if Alectryon is installed) to generate documents under `html-alectryon/`

## Documentation

Coqdocs are found under [/docs/html/toc.html](/docs/html/toc.html)

Alectryon files are found under [/docs/html-alectryon/](/docs/html-alectryon/)

## Organization

### Navigating the Typeclass Hierarchy

The theory of decorated traversable monads (DTMs) is formlized in three equivalent ways:

- Classically: "a DTM is a monoid in the category of decorated-traversable endofunctors"
- In the style of Kleisli: "a DTM is a type constructor with a generalized `bind` operation subject to equations"
- In terms of parameterized coalgebras: "a DTM is a container of elements, paired with a context, which can be replaced with subtrees"

These different views are respetively formalized under these directories:

- [Tealeaves/Classes/Categorical](/Tealeaves/Classes/Categorical)
- [Tealeaves/Classes/Kleisli](/Tealeaves/Classes/Coalgebraic)
- [Tealeaves/Classes/Coalgebraic](/Tealeaves/Classes/Coalgebraic)

Here is a convenient table for navigating the typeclass hierarchy:

| **Tealeaves Typeclasses** | Functor                                                                                                                                                                                                                         | Monad                                                                                                                                                                                                                     |
|---------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Plain                     | [Classes/Functor.v](/Tealeaves/Classes/Functor.v)                                                                                                                                                                               | [Categorical](/Tealeaves/Classes/Categorical/Monad.v) / [Kleisli](/Tealeaves/Classes/Kleisli/Monad.v)                                                                                                                     |
| Decorated                 | [Categorical](/Tealeaves/Classes/Categorical/DecoratedFunctor.v) / [Kleisli](/Tealeaves/Classes/Kleisli/DecoratedFunctor.v)                                                                                                     | [Categorical](/Tealeaves/Classes/Categorical/DecoratedMonad.v) / [Kleisli](/Tealeaves/Classes/Kleisli/DecoratedMonad.v)                                                                                                   |
| Traversable               | [Categorical](/Tealeaves/Classes/Categorical/TraversableFunctor.v) / [Kleisli](/Tealeaves/Classes/Kleisli/TraversableFunctor.v) / [Coalgebraic](/Tealeaves/Classes/Coalgebraic/TraversableFunctor.v)                            | [Categorical](/Tealeaves/Classes/Categorical/TraversableMonad.v) / [Kleisli](/Tealeaves/Classes/Kleisli/TraversableMonad.v) / [Coalgebraic](/Tealeaves/Classes/Coalgebraic/TraversableMonad.v)                            |
| Decorated+Traversable     | [Categorical](/Tealeaves/Classes/Categorical/DecoratedTraversableFunctor.v) / [Kleisli](/Tealeaves/Classes/Kleisli/DecoratedTraversableFunctor.v) / [Coalgebraic](/Tealeaves/Classes/Coalgebraic/DecoratedTraversableFunctor.v) | [Categorical](/Tealeaves/Classes/Categorical/DecoratedTraversableMonad.v) / [Kleisli](/Tealeaves/Classes/Kleisli/DecoratedTraversableMonad.v) / [Coalgebraic](/Tealeaves/Classes/Coalgebraic/DecoratedTraversableMonad.v) |

### Equivalence of the Presentations

For each concept (e.g. decorated functor, traversable monad, etc.) adapters are provided which, given a typeclass instance for one view, derive a typeclass instance for another view. For example, the typeclass instance that converts a Kleisli-presented decorated-traversable functor into a coalgebraic one is found in [Tealeaves/Adapters/KleisliToCoalgebraic/DecoratedTraversableFunctor.v](Tealeaves/Adapters/KleisliToCoalgebraic/DecoratedTraversableFunctor.v). Adapters that convert directly between categorical and coalgebraic instances are not given, but can be obtained by composition via converting to/from the Kleisli instances.

| Adapter                   | Directory                                                                          |
|---------------------------|------------------------------------------------------------------------------------|
| Categorical ⇝ Kleisli     | [Tealeaves/Adapters/CategoricalToKleisli](/Tealeaves/Adapters/CategoricalToKleisli) |
| Categorical ⇝ Coalgebraic | Not formalized directly                                                            |
| Kleisli ⇝ Categorical     | [Tealeaves/Adapters/KleisliToCategorical](/Tealeaves/Adapters/KleisliToCategorical) |
| Kleisli ⇝ Coalgebraic     | [Tealeaves/Adapters/KleisliToCoalgebraic](/Tealeaves/Adapters/KleisliToCoalgebraic) |
| Coalgebraic ⇝ Kleisli     | [Tealeaves/Adapters/CoalgebraicToKleisli](/Tealeaves/Adapters/CoalgebraicToKleisli) |
| Coalgebraic ⇝ Categorical | Not formalized directly                                                            |


The correctness of the adapters states that (up to functional extensionality), performing a two-way roundtrip with any of the adapters results in the original structure. These proofs are found in [Tealeaves/Adapters/Roundtrips](Tealeaves/Adapters/Roundtrips)

### Backends

Tealeaves backends are formalized under [Tealeaves/Backends](/Tealeaves/Backends). Tealeaves users should import backends directly from the top-level files in this directory. For instance, to import the single-sorted locally nameless backend, import [Tealeaves/Backends/LN.v](/Tealeaves/Backends/LN.v).

### Adapters

Adapters that convert between locally nameless and de Bruijn representations of variable binding are found under [Tealeaves/Backends/Adapters](/Tealeaves/Backends/Adapters).

### Examples

Examples of using Tealeaves to formalize various calculi are found in [Tealeaves/Examples](/Tealeaves/Examples)

### Multisorted Tealeaves

A multisorted definition of DTMs is contained in [Tealeaves/Classes/Multisorted](/Tealeaves/Classes/Multisorted). A multisorted locally nameless backend is contained in [Tealeaves/Backends/Multisorted/LN.v](/Tealeaves/Backends/Multisorted/LN.v).

### Other Directories

| Directory                                                         | Contents                                                                              |
|-------------------------------------------------------------------|---------------------------------------------------------------------------------------|
| [Tealeaves/Categories](/Tealeaves/Categories)                     | Instances of the `Category` typeclass                                                 |
| [Tealeaves/Functors](/Tealeaves/Functors)                         | Common endofunctors (`Type -> Type`) and instances of DTM concepts (Kleisli style)    |
| [Tealeaves/Functors/Categorical](/Tealeaves/Functors/Categorical) | A few endofunctors (`Type -> Type`) and instances of DTM concepts (Categorical style) |
| [Tealeaves/Tactics](/Tealeaves/Tactics)                           | Tactics for internal use                                                              |
| [Tealeaves/Simplification](/Tealeaves/Simplification)             | Simplication tactics for backends for downstream use                                  |

Additionally, subdirectories named `Theory/` are scattered in various places. Mostly these contain definitions and lemmas regarding various DTM concepts which, for whatever reason (e.g. to avoid cyclic dependencies), are formalized in files separately from those defining the relevant concepts.

## Naming Conventions

### Kleisli Composition

| Decorated | Traversable | Monad | Composition operation             |
|-----------|-------------|-------|-----------------------------------|
| 0         | 0           | 0     | compose (kc0)                     |
| 1         | 0           | 0     | kc1 (now kc4, oops!)              |
| 0         | 1           | 0     | kc2                               |
| 1         | 1           | 0     | kc3 (now kc6, oops!)              |
| 0         | 0           | 1     | kc (would be kc4, now kc1, oops!) |
| 1         | 0           | 1     | kc5                               |
| 0         | 1           | 1     | kc6 (now kc3, oops!)              |
| 1         | 1           | 1     | kc7                               |


### Typeclasses Field Names

| Decorated | Traversable | Monad | Class prefix    | Categorical prefix |
|-----------|-------------|-------|-----------------|--------------------|
| 0         | 0           | 0     | fun             |                    |
| 1         | 0           | 0     | dfun            |                    |
| 0         | 1           | 0     | trf             |                    |
| 1         | 1           | 0     | kdtfun / kdtfci |                    |
| 0         | 0           | 1     | kmon            |                    |
| 1         | 0           | 1     | kmond           |                    |
| 0         | 1           | 1     | ktm             |                    |
| 1         | 1           | 1     | kdtm            |                    |
