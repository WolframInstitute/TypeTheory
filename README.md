# TypeTheory

A proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Coq, written
in the Wolfram Language. Terms are ordinary Wolfram Language expressions built from built-in symbols
(`Function`, `Typed`, `ForAll`, `Implies`, `Equal`, `Plus`, ...). A small trusted kernel checks them,
and tactics build proofs step by step in a notebook.

> Status: **prototype.** The kernel, inductive families with generated recursors, structures with
> projections, elaboration, a prelude of logic, equality and natural numbers, and six tactics work and
> are tested. It is pure Wolfram Language, with no native library underneath, and it does not depend
> on Lean. LeanLink has a bridge that translates declarations in both directions.

## Loading

From a checkout:

```wolfram
PacletDirectoryLoad["path/to/TypeTheory/TypeTheory"]
Needs["WolframInstitute`TypeTheory`"]
```

Loading takes about a second, and most of that is building the prelude through the kernel.

## A first session

There is no global environment. An environment is a value, and a term carries the environment its
constants come from:

```wolfram
prelude = TypeTheoryEnvironment["Prelude"];

TypeOf[TypeTheoryTerm[2 + 3, prelude]]
(* TypeTheoryTerm[NonNegativeIntegers, prelude] *)

WeakHeadNormalForm[TypeTheoryTerm[2 + 3, prelude]]
(* TypeTheoryTerm[5, prelude] *)
```

Declarations are inert constructors until they are added to an environment, which gives a new
environment and leaves the old one as it was:

```wolfram
arithmetic = Append[prelude, TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]];
arithmetic[TwoPlusTwo]
(* TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]] *)

Append[prelude, TypeTheoryTheorem[Wrong, 2 + 2 == 5, EqualityReflexivity[4]]]
(* Failure["TypeMismatch", ...]: EqualityReflexivity[4] has type 4 == 4, but the expected type is 2 + 2 == 5 *)
```

A proof by induction, one tactic at a time:

```wolfram
proof = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n], prelude];
proof = TypeTheoryTactic["Introduce", n][proof];
proof = TypeTheoryTactic["Induction", n][proof];        (* two goals: zero and successor *)
proof = TypeTheoryTactic["Reflexivity"][proof];         (* 0 + 0 == 0 by computation *)
proof = TypeTheoryTactic["Introduce", k, ih][proof];    (* ih : 0 + k == k *)
proof = TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]][proof];

proved = Append[prelude, TypeTheoryTheorem[AdditionZeroLeft, proof]];
TypeTheoryCheck[TypeTheoryTerm[AdditionZeroLeft[7], proved], TypeTheoryTerm[0 + 7 == 7]]
(* True *)
```

In a notebook a proof shows its open goals, each as a list of hypotheses over the goal. A term shows
in mathematical notation, and a declaration as its keyword, its name and its type.

## The language

| Surface term | Meaning |
| --- | --- |
| `Function[{Typed[x, A], ...}, b]` | a function |
| `ForAll[{Typed[x, A], ...}, B]` | a dependent function type, or a universal statement |
| `Implies[A, B]`, `TypeSpecifier[{A, ...} -> B]`, `A -> B` | a function type whose result does not depend on the argument |
| `Annotation[Typed[x, A], "Implicit"]` | an implicit binder, filled in by elaboration (also `"StrictImplicit"`, `"InstanceImplicit"`) |
| `Exists[{Typed[x, A]}, p]` | an existential statement |
| `Typed[e, A]` | `e`, checked against `A` |
| `With[{x = v}, b]` | `b` with `x` standing for `v` |
| `TypeUniverse[level]` | a universe: `TypeUniverse[0]` is Prop, `TypeUniverse[1]` is Type, `TypeUniverse[u + 1]` |
| `f[a, b]` | application, curried, with implicit arguments filled in |
| `Construct[f, a, b]` | application with every argument given, implicit ones included |
| `Subscript[c, level, ...]` | the constant `c` at explicit universe levels |
| `t[[i]]` | field `i` of `t`, whose type is a structure |
| `0`, `1`, `2`, ... | natural number literals |
| `RightTee[{Typed[x, A], ...}, B]` | a goal, read as `ForAll` |

Any other symbol or string is a bound variable or a declared constant. A symbol whose value is a
`TypeTheoryTerm` stands for that term, and one whose value is a finished `TypeTheoryProof` stands for
its proof.

`TypeTheoryTerm` has the `HoldFirst` attribute. It has to: `ForAll[Typed[x, A], B]` on its own evaluates
to `B`, and `n + 0 == n` to `True`. The declaration constructors and `TypeTheoryProof` hold their terms
for the same reason. Names are kept in `HoldComplete` throughout, so a symbol with a value never
evaluates inside a term.

## Environments

| Constructor | Declares |
| --- | --- |
| `TypeTheoryAxiom[name, type]` | an axiom |
| `TypeTheoryDefinition[name, value]` | a definition; `value` may be `Typed[v, type]` |
| `TypeTheoryTheorem[name, statement, proof]` | a theorem; `TypeTheoryTheorem[name, proof]` takes the statement of a finished proof |
| `TypeTheoryInductiveType[name, type, {c -> type, ...}]` | an inductive type with its constructors and its recursor `InductiveRecursor[name]` |
| `TypeTheoryNaturalNumbers[type, zero, successor, addition]` | the natural numbers that literals belong to |

`TypeTheoryEnvironment[]` is empty, `TypeTheoryEnvironment["Prelude"]` is the prelude,
`TypeTheoryEnvironment[env, {declaration, ...}]` adds declarations in turn, and `Append[env, declaration]`
adds one. An environment behaves like an association of its constants: `env[name]` gives the declaration
that introduced `name`, and `Keys`, `Length`, `KeyExistsQ`, `Normal` and `Information` work as expected.
`Normal[env]` gives the declarations, written out exactly, so `TypeTheoryEnvironment[Normal[env]]`
rebuilds it.

An environment is a handle to a store: a symbol of its own whose DownValues hold the constants, the
Wolfram Language's own way of storing definitions. The handle is small, so terms and proofs carry it. A
store is never changed once built, and it lasts for the session.

## The prelude

- **Logic:** `True` (`TrueIntroduction`), `False`, `Not`, `And` (`AndIntroduction`) and `Or` (`OrIntroductionLeft`, `OrIntroductionRight`).
- **Equality:** `Equal` (`EqualityReflexivity`), and `Exists` (`ExistsIntroduction`).
- **Natural numbers:** `NonNegativeIntegers`, with `NaturalNumberZero` and `NaturalNumberSuccessor`, registered so that literals are natural numbers.
- **Addition:** `Plus`, defined by recursion on its second argument.
- **Theorems:** `FalseElimination`, `AndEliminationLeft`, `AndEliminationRight`, `EqualitySymmetry`, `EqualityTransitivity`, `EqualityCongruence` and `EqualitySubstitution`, proved with the recursors.

## Tactics

`TypeTheoryTactic[name, arguments...][proof]` works on the first goal of a `TypeTheoryProof`:

| Tactic | Effect |
| --- | --- |
| `"Introduce", x, ...` | moves the variables or hypotheses of a universal statement, implication or `Not` into the context |
| `"Exact", term` | solves the goal with a term |
| `"Apply", term` | solves the goal with a term applied to new goals, as many as its conclusion needs |
| `"Reflexivity"` | solves `a == b` when the two sides are equal by computation |
| `"Induction", x` | one goal per constructor of the type of `x`, with induction hypotheses |
| `"Assumption"` | solves the goal with a hypothesis |

`TypeTheoryProof[statement, env, {tactic1, tactic2, ...}]` runs a list of tactics. Nothing a tactic does
is trusted: the finished term is checked by the kernel when the theorem is added to an environment.

## How it works

```
TypeTheory/Kernel/
  Terms/CoreTerms.wl           core terms (locally nameless) and universe levels
  Terms/SurfaceSyntax.wl       held syntax trees; reading core terms back, for display or exactly
  Terms/Formatting.wl          notebook display of terms, declarations and proofs
  Checking/TypeChecking.wl     the kernel: inference, reduction, definitional equality, projections
  Checking/InductiveTypes.wl   checking inductive families and generating recursors
  Checking/NaturalNumbers.wl   registering the natural numbers for literals
  Checking/Environment.wl      environments as stores of definitions, and kernel failures
  Checking/Declarations.wl     the declaration constructors and environments built from them
  Checking/Queries.wl          TypeOf, TypeTheoryCheck, DefinitionallyEqualQ, WeakHeadNormalForm, environments as associations
  Elaboration/Elaboration.wl   implicit arguments, universe levels, unification
  Proofs/ProofStates.wl        proof states and tactics
  Library/Prelude.wl           the prelude
```

The trusted part is `CoreTerms.wl`, `TypeChecking.wl`, `InductiveTypes.wl`, `NaturalNumbers.wl`,
`Environment.wl` and the core declaration functions: about 1,400 lines with their comments and usage
messages. Elaboration and tactics produce terms that the kernel checks again with no metavariables
left, so a mistake outside the kernel can make a proof fail but cannot make a false statement a theorem.
Kernel answers are `Failure` objects, never messages.

A store can be changed by hand. `TypeTheoryCheck[environment]` replays every declaration from scratch
and compares each stored record with the record that checking it produces, so a forged theorem or
recursor is caught. See [docs/notes/Kernel.md](docs/notes/Kernel.md) for the design decisions, and
[docs/research/TypeTheoryEngine.html](docs/research/TypeTheoryEngine.html) for the full design.

## Tests

```bash
wolframscript -f scripts/run_tests.wls
```

The suite has 106 tests in `TypeTheory/Tests/`, mirroring the kernel layout. They include rejecting
forged declarations: a wrong proof, a negative occurrence, an oversized universe, large elimination
from `Or`, data projected out of a proof, `Type : Type`, and tampered environment records.

## Not yet

- Mutual and nested inductive types; quotients; induction on indexed families in the tactic.
- Higher-order unification beyond patterns; no type classes.
- A compiled kernel (`FunctionCompile` over an array encoding of terms).
