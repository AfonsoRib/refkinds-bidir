# Repository instructions

## Mission

Build an independent Haskell implementation of the language in the Refinement
Kinds paper as a checker-only core. The refinement constraint generator follows the bidirectional
structure of Chapters 3 and 4 of the bundled refinement-types tutorial.

Read `GUARDRAILS.md` before implementing checker or language changes. It records
non-negotiable prohibitions, not a positive language specification. The bundled
papers, design notes, implementation behavior, and tests are evidence rather
than automatic authority. Resolve material semantic choices with the user.

## External-reference boundary

- External projects may be inspected read-only for design and semantic
  comparison.  Do not modify them.
- Do not copy or adapt external source, tests, or prose.  All implementation
  code and tests in this repository must be independently authored.
- When external inspection materially affects semantics or architecture,
  record a concise design note in this repository identifying the provenance
  and the resulting decision.  Only files under `resources/` may be imported
  as repository evidence.
- Files below `resources/fixtures/original/` are immutable test evidence.
- Compatibility behavior is recorded without importing the old Haskell tests.
- Implement generic paper examples; closed specializations are not substitutes.

## Semantic invariants

- Surface binders are named. Core bound variables are de Bruijn indices and
  free variables retain names in separate term, type, and refinement namespaces.
- Term and type lambdas contain no binder classifier and are checking-only.
- Both terms and types are converted to ANF before checking.
- This branch currently has no term evaluator or top-level declaration
  language. Callers supply trusted kind and term assumptions through `Context`;
  transparent definitions remain lexical `TLet`/`TRec` syntax. A future branch
  may add a separate definition environment through an explicit design revision.
- Hidden type evaluation is deterministic, left-to-right, and call by value.
- Type and term recursion need not structurally decrease. Recursive definitions
  must still check against their declared classifiers. Type equality validates,
  evaluates, and alpha-compares its operands; evaluation may diverge.
- Constraints are not simplified, split, or deduplicated by the checker or SMT
  encoder. Except for the solver-free `CTrue` case, each constraint reaches one
  CVC5 process as a complete query.
- Open obligations are sent to CVC5 deliberately and are expected to fail there;
  no ambient-context closure or free-variable preflight is performed. `unknown`
  is never success.

## Workflow

- Add positive and negative tests with each semantic rule.
- Run the complete test suite after each milestone.
- Generate the Happy parser with `%expect 0`; any shift/reduce or reduce/reduce
  conflict is a release-blocking failure.
