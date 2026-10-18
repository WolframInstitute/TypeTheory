# TypeTheory

A proof engine for the Calculus of Inductive Constructions, the type theory of Lean and Rocq, written
in the Wolfram Language. Terms are ordinary Wolfram Language expressions built from built-in symbols
(`Function`, `Typed`, `ForAll`, `Implies`, `Equal`, `Plus`, ...). A small trusted kernel checks them,
and tactics build proofs step by step in a notebook.

> Status: **prototype.** The kernel, inductive families with generated recursors, structures with
> projections, elaboration, a prelude of logic, equality and natural numbers, and six tactics work and
> are tested. It is pure Wolfram Language, with no native library underneath, and it does not depend
> on Lean. LeanLink's `LeanToTypeTheory` and `TypeTheoryToLean` translate declarations between Lean
> and TypeTheory.

## Loading

Install the published paclet:

```wolfram
PacletInstall[ResourceObject["https://www.wolframcloud.com/obj/wolframinstitute/DeployedResources/Paclet/WolframInstitute/TypeTheory"]]
Needs["WolframInstitute`TypeTheory`"]
```

Or from a checkout:

```wolfram
PacletDirectoryLoad["path/to/TypeTheory/TypeTheory"]
Needs["WolframInstitute`TypeTheory`"]
```

Loading takes about a second, and most of that is building the prelude through the kernel.

## Documentation

The [documentation site](https://www.wolframcloud.com/obj/wolframinstitute/TypeTheory) has a reference
page for every symbol, a guide, and the tutorial *Getting Started with TypeTheory*. The pages are
literate Markdown in [docs/paclet/en](docs/paclet/en), written to
[docs/paclet/en/DOC_GUIDE.md](docs/paclet/en/DOC_GUIDE.md), and
[PacletPage](https://www.wolframcloud.com/obj/wolframinstitute/PacletPage) builds and publishes them:

```bash
wl -f build_docs.wls             # evaluate the pages into notebooks under TypeTheory/Documentation
wl -f release.wls --dry-run      # build and check the site and the paclet archive, deploying nothing
wl -f release.wls                # publish the site and the paclet, as wolframinstitute
```

## A first session

A term carries the environment its constants come from. Without one, it is in the prelude, an
environment of logic, equality and the natural numbers:

```wolfram
TypeOf[TypeTheoryTerm[2 + 3]]
(* ℕ, that is TypeTheoryTerm[NonNegativeIntegers, prelude] *)

WeakHeadNormalForm[TypeTheoryTerm[2 + 3]]
(* 5 *)
```

Declarations are inert constructors until an environment checks them. `TypeTheoryEnvironment[{...}]`
gives the prelude extended with them, and `Append` extends any environment; neither changes the old one:

```wolfram
arithmetic = TypeTheoryEnvironment[{TypeTheoryTheorem[TwoPlusTwo, 2 + 2 == 4, EqualityReflexivity[4]]}];
arithmetic[TwoPlusTwo]
(* theorem TwoPlusTwo : 2 + 2 == 4 *)

TypeTheoryEnvironment[{TypeTheoryTheorem[Wrong, 2 + 2 == 5, EqualityReflexivity[4]]}]
(* Failure["TypeMismatch", ...]: EqualityReflexivity[4] has type 4 == 4, but the expected type is 2 + 2 == 5 *)
```

A proof by induction, one tactic at a time:

```wolfram
proof = TypeTheoryProof[ForAll[{Typed[n, NonNegativeIntegers]}, 0 + n == n]];
proof = TypeTheoryTactic["Introduce", n][proof];
proof = TypeTheoryTactic["Induction", n][proof];        (* goals 0 + 0 == 0 and 0 + n == n ⇒ 0 + (n + 1) == n + 1 *)
proof = TypeTheoryTactic["Reflexivity"][proof];         (* 0 + 0 == 0 by computation *)
proof = TypeTheoryTactic["Introduce", k, ih][proof];    (* ih : 0 + k == k *)
proof = TypeTheoryTactic["Exact", EqualityCongruence[NaturalNumberSuccessor, ih]][proof];

proved = TypeTheoryEnvironment[{TypeTheoryTheorem[ZeroLeftIdentity, proof]}];
TypeTheoryCheck[TypeTheoryTerm[ZeroLeftIdentity[7], proved], TypeTheoryTerm[0 + 7 == 7]]
(* True *)
```

In a notebook a proof shows its open goals, each as a list of hypotheses over the goal. A term shows
in mathematical notation, with `∧`, `∨`, `¬`, and the natural numbers as `0` and `n + 1` as Lean shows
them; a declaration shows as its keyword, its name and its type.

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

`TypeTheoryEnvironment[{declaration, ...}]` adds declarations in turn to the prelude, which is also the
environment of any term or proof that names none. `TypeTheoryEnvironment[env, {declaration, ...}]` adds
them to `env`, `Append[env, declaration]` adds one, `TypeTheoryEnvironment[]` is empty,
`TypeTheoryEnvironment["Prelude"]` is the prelude itself, and `TypeTheoryEnvironment["Constructive"]` is
the prelude without its axioms. An environment behaves like an association of
its constants: `env[name]` gives the declaration that introduced `name`, and `Keys`, `Length`,
`KeyExistsQ`, `Normal` and `Information` work as expected. `Normal[env]` gives the declarations, the
prelude's included, written out exactly, so `TypeTheoryEnvironment[TypeTheoryEnvironment[], Normal[env]]`
rebuilds it.

An environment is a handle to a store: a symbol of its own whose DownValues hold the constants, the
Wolfram Language's own way of storing definitions. The handle is small, so terms and proofs carry it. A
store is never changed once built, and it lasts for the session.

## The prelude

The prelude is the environment of every term, proof and declaration list that names none. Each of its
109 constants is checked by the kernel when the paclet loads. It is classical, as Lean's library is:
three constants are axioms, propositional extensionality, function extensionality and choice, and the
excluded middle is proved from them. `TypeTheoryEnvironment["Constructive"]` is the prelude without the
axioms and what is proved from them, to prove theorems without axioms or to assume others. The tutorial
*The TypeTheory Prelude* on the documentation site goes through all of it.

- **Logic:** `True` (`TrueIntroduction`), `False` (`FalseElimination`), `Not`, `And` (`AndIntroduction`,
  `AndEliminationLeft`, `AndEliminationRight`), `Or` (`OrIntroductionLeft`, `OrIntroductionRight`),
  `Equivalent` (`EquivalentIntroduction`, `EquivalentForward`, `EquivalentBackward`, with reflexivity,
  symmetry and transitivity) and `Exists` (`ExistsIntroduction`).
- **Equality:** `Equal` (`EqualityReflexivity`, `EqualitySymmetry`, `EqualityTransitivity`,
  `EqualityCongruence`, `EqualitySubstitution`) and `Unequal`, `x != y`.
- **Functions:** `Identity` and `Composition`.
- **Natural numbers:** `NonNegativeIntegers`, with `NaturalNumberZero`, `NaturalNumberSuccessor` and
  `NaturalNumberPredecessor`, registered so that literals are natural numbers; `Plus`, `Times`, `Power`
  and `Subtract` (which stops at 0), each by recursion on its second argument as in Lean; `LessEqual`,
  inductive as Lean's `Nat.le` (`LessEqualReflexivity`, `LessEqualStep`), with `Less`, `GreaterEqual`
  and `Greater`.
- **Theorems about them:** commutativity, associativity and distributivity of addition and
  multiplication, the zero, one and successor laws, cancellation of subtraction, the laws of powers,
  injectivity of the successor, and the order's transitivity, antisymmetry and irreflexivity.
- **Booleans:** `Booleans`, with `BooleanFalse` and `BooleanTrue`, and `BooleanNot`, `BooleanAnd` and
  `BooleanOr`, by cases on the first argument as Lean's `Bool`. They show as `true`, `false`, `!`, `&&` and
  `||`.
- **Classical logic:** `Nonempty` (`NonemptyIntroduction`) and `Subtype` (`SubtypeIntroduction`); the
  axioms `PropositionalExtensionality`, `FunctionExtensionality` (which Lean proves from quotients) and
  `Choice`; `ChosenWitness` with `ChosenWitnessProperty`; and the theorems `ExcludedMiddle`, proved by
  Diaconescu's argument, and `DoubleNegationElimination`.

The elaborator reads `a - b` as `Subtract[a, b]` and `a && b && c` as `a && (b && c)` for propositions
and `(a && b) && c` for Booleans. `True`, `False`, `Not`, `And` and `Or` are propositions or Booleans, as
the type decides: propositions where a type or `Prop` is expected, Booleans where `Booleans` is, and
otherwise whatever the arguments or the term's use allow. A term nothing decides, such as
`True == False`, is ambiguous and gives a `Failure`, and `Typed[True, Booleans]` says which it is.

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

The suite has 133 tests in `TypeTheory/Tests/`, mirroring the kernel layout. They include rejecting
forged declarations: a wrong proof, a negative occurrence, an oversized universe, large elimination
from `Or`, data projected out of a proof, `Type : Type`, and tampered environment records.

## Not yet

- Decidability, pairs, sums, options and lists, and the theory around them.
- Mutual and nested inductive types; quotients; induction on indexed families in the tactic.
- Higher-order unification beyond patterns; no type classes.
- A compiled kernel (`FunctionCompile` over an array encoding of terms), and computing products and
  powers of literals with integers, as sums already are.
