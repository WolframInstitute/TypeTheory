# AGENTS.md

Guidance for any AI agent or automated contributor working in this repository. It is plain Markdown,
not specific to one tool.

## What this repo is

`WolframInstitute/TypeTheory` is a Wolfram Language paclet: a proof engine for the Calculus of
Inductive Constructions in pure Wolfram Language. Kernel code lives in `TypeTheory/Kernel/<Area>/<File>.wl`,
tests in `TypeTheory/Tests/<Area>/<File>.wlt` (the same layout), design notes in `docs/notes/`, the
design document in `docs/research/`, and the documentation pages in `docs/paclet/en/`.
[README.md](README.md) is the overview.

The paclet has one context, `` WolframInstitute`TypeTheory` ``, through StructuredPackageFormat: the
umbrella file `TypeTheory/Kernel/TypeTheory.wl` calls `PackageInitialize`, and each feature file declares
`PackageExported` and `PackageScoped` symbols. Scoped symbols live in
`` WolframInstitute`TypeTheory`PackageScope` ``; tests refer to them by their full names.

## Rules

- Follow [GUIDE.md](GUIDE.md), the Wolfram Language style guide shared with PureMath: complete English
  words in names, tabs, no trailing `;` on definitions, `Failure` objects instead of messages, no
  `Return`, no `Part`, usage messages for every function.
- **The kernel is the trust boundary.** `Terms/CoreTerms.wl`, `Checking/TypeChecking.wl`,
  `Checking/InductiveTypes.wl`, `Checking/NaturalNumbers.wl`, `Checking/Environment.wl` and the core
  declaration functions in `Checking/Declarations.wl` decide what is a theorem. A change there needs a
  test that a forged proof or declaration is still rejected. Elaboration and tactics are untrusted:
  everything they produce is checked again by the kernel.
- **Terms must stay held.** Surface terms are built from built-in symbols that evaluate (`ForAll`,
  `Equal`, `Plus`); never let one evaluate. Functions that take surface terms have `Hold*` attributes,
  and names are kept as `HoldComplete[name]`. A pattern such as `TypeTheoryProof[_Association]` must not
  start a proof; `statementQ` in `Proofs/ProofStates.wl` guards against it.
- Kernel functions report failure with `kernelFailure`, a tagged `Throw` that `catchKernelFailure` turns
  into a `Failure` at each exported function.
- An environment is a handle to a store, a symbol whose DownValues hold the constants. Stores are never
  mutated after they are built; code that builds environments in steps runs inside `withStoreCleanup`,
  which removes the stores of the steps in between.
- This paclet does not depend on Lean or LeanLink, and no symbol here is named after Lean. A Lean bridge
  belongs in LeanLink.

## Documentation

Every exported symbol has a page in `docs/paclet/en/Symbols/`, written to
[docs/paclet/en/DOC_GUIDE.md](docs/paclet/en/DOC_GUIDE.md). A new exported symbol gets its page, and a
change in behavior updates the examples it touches. `wl -f build_docs.wls` evaluates every page; read the
outputs back and compare them with the `<!-- => ... -->` hints, which nothing checks automatically.
`release.wls` publishes the site and the paclet resource as wolframinstitute.

## Testing

```bash
wolframscript -f scripts/run_tests.wls                                   # every file
wolframscript -f scripts/run_tests.wls TypeTheory/Tests/Proofs/ProofStates.wlt
```

Run from the repository root: each `.wlt` file starts with `PacletDirectoryLoad[Directory[]]`. There is
no global environment: a test builds the environments it needs, usually from `TypeTheoryEnvironment["Prelude"]`,
and environments never change, so files do not depend on one another.

### Writing Wolfram context names in Markdown

A context name ends in a backtick, which closes a single-backtick code span early. Any code span whose
content contains a backtick uses double-backtick delimiters with a space inside each end:
``` `` WolframInstitute`TypeTheory` `` ```. This applies to every Markdown an agent writes, including
commit messages and prompts.
