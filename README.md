# Bidirectional Type Checking for Languages with Refinement Kinds

A checker-only Haskell implementation of the language studied in *Refinement
Kinds: Type-safe Programming with Practical Type-level Computation*.

## Build and test

Requires GHC 9.4 or later, Cabal, Alex, Happy, and CVC5.

The local build and test environment uses these versions:

| Software | Version |
| --- | --- |
| GHC | 9.4.8 |
| cabal-install | 3.12.1.0 |
| Alex | 3.5.4.2 |
| Happy | 2.2 |
| CVC5 | 1.1.2 |

Alex and Happy are the versions selected by Cabal's build plan.

```sh
cabal build all --offline
cabal test --offline --test-show-details=direct
```

## Code and tests

- `src/Types.hs`: surface and core syntax, kinds, and predicates.
- `src/Desugar.hs`: named surface syntax to locally nameless core syntax.
- `src/ANF.hs`: administrative normal form conversion before checking.
- `src/Check.hs`, `src/Constraint.hs`, and `src/EvalTy.hs`: kind and term checking, constraint validation, and type evaluation.
- `test/Suites/`: parser, syntax, ANF, kind, term-checker, equality, solver-boundary, and paper-example suites.
- `test/Support/`: shared test helpers and representation-invariant checks.
- `examples/`: small checker inputs used for CLI examples.

The surface language has named binders. Core bound variables use de Bruijn
indices, and free term, type, and refinement variables use separate namespaces.
Term and type lambdas are checking-only. The checker accepts expressions,
types, kinds, and predicates; it has no top-level declaration language or term
evaluator. Types and terms are converted to ANF before checking.
