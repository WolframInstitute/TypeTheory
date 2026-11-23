---
Template: Symbol
Name: TypeTheoryDetermine
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryDetermine
Keywords: [determine, decision, theorem proving, proof, refutation, counterexample, independence, finite models, undetermined, automatic, LLM, LLMFunction, verification]
SeeAlso: [TypeTheoryProof, TypeTheoryAssumptions, TypeTheoryConsequences, TypeTheoryTermination, TypeTheoryTactic, TypeTheoryTheorem, Decide, LLMFunction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [AutomatedAnalysisAndDiscovery, TypeTheoryIntroduction, ProgramsAndProofs]
---

## Usage

<code>[TypeTheoryDetermine]()[*proposition*]</code> determines whether *proposition* is `"Proved"`, `"Refuted"`, `"Independent"` or `"Undetermined"` in the default environment, [$TypeTheoryEnvironment](), returning an [Association]() with kernel-checked certificates.

<code>[TypeTheoryDetermine]()[*proposition*, *env*]</code> determines *proposition* in the [TypeTheoryEnvironment]() *env*, or in the library environment named by *env*, such as `"Integers"` or `"Constructive"`.

<code>[TypeTheoryDetermine]()[[TypeTheoryTerm]()[*proposition*, *env*]]</code> determines the [TypeTheoryTerm]() *proposition* in its own environment *env*.

## Details & Options

- [TypeTheoryDetermine]() has the [HoldFirst]() attribute: *proposition* is held, so built-in symbols such as [ForAll](), [Equal]() and [Plus]() never evaluate before elaboration. Patterns such as <code>[TypeTheoryDetermine]()[_[Association]()]</code> stay unevaluated, and expressions that are not propositions in <code>[TypeUniverse]()[0]</code> give a [Failure]() tagged `"NotAProposition"`.
- Every proof returned is untrusted until checked by the kernel against the proposition's core type: a `"Proved"` result carries a finished [TypeTheoryProof]() of *proposition*, a `"Refuted"` result carries a finished [TypeTheoryProof]() of <code>[Not]()[*proposition*]</code> (with `"Counterexample"` when found), and an `"Independent"` result carries two finished [TypeTheoryProof]() certificates under `"Models"`, one instantiating the opaque axioms so *proposition* holds (`"TrueModel"`) and one so <code>[Not]()[*proposition*]</code> holds (`"FalseModel"`).
- `"Status"` is one of `"Proved"`, `"Refuted"`, `"Independent"` or `"Undetermined"`.
- `"ComputationallyDecidable"` is an orthogonal [True]()/[False]() field recording whether a [Decidable]() instance synthesizes for *proposition* in the environment, separate from whether a proof was found.
- When `"Status"` is `"Undetermined"` in an environment without classical axioms (such as `"Constructive"`), `"Details"` reports `"ClassicallyProvable"` and `"RequiredAxioms"` if the proposition is provable in the prelude.
- The following options can be given:

| Option | Default | Description |
| --- | --- | --- |
| [Method]() | [Automatic]() | `"Heuristic"` (the offline default), `"LLM"`, or `{"Heuristic", "LLM"}` to fall back to [LLMFunction]() when heuristics return `"Undetermined"` |
| [TimeConstraint]() | `15` | time budget in seconds for search and LLM calls |
| `"MaxModelSize"` | `3` | maximum finite carrier size tried when constructing certified independence models |
| `"LLMEvaluator"` | [Automatic]() | [Automatic]() for Wolfram AI's default model, an [LLMConfiguration](), or a prompt guidance string wrapped in [LLMConfiguration]() |
| [ProgressReporting]() | [Automatic]() | whether to display live stage progress (`True`, `False`, or [Automatic]() following [$ProgressReporting]()) |

- With `Method -> Automatic`, [TypeTheoryDetermine]() runs strictly offline using its symbolic and tactic heuristics and makes no network calls.
- When [Method]() includes `"LLM"`, candidate tactic lists proposed by [LLMFunction]() are executed in [TypeTheoryProof]() and verified by the trusted kernel before `"Status" -> "Proved"` is ever returned.

## Basic Examples

Decide a closed true proposition by computation in the prelude:

```wl
result = TypeTheoryDetermine[2 + 2 == 4]
```

<!-- => <|"Status" -> "Proved", "Statement" -> 2 + 2 == 4, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> True, "Method" -> "Decide", "Details" -> <||>|> -->

The proof it returns is accepted as a theorem by [TypeTheoryTheorem]():

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[TwoPlusTwo, result["Proof"]]][TwoPlusTwo]
```

<!-- => theorem TwoPlusTwo : 2 + 2 == 4 -->

---

Refute a false universal conjecture with an explicit counterexample and a kernel-checked proof of its negation:

```wl
TypeTheoryDetermine[ForAll[{n}, n^2 <= 2^n]]
```

<!-- => <|"Status" -> "Refuted", "Statement" -> ∀_n∶ℕ n^2 <= 2^n, "Proof" -> Proof complete, "Counterexample" -> <|"n" -> 3|>, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Counterexample", "Details" -> <||>|> -->

---

Prove a universal arithmetic identity by induction:

```wl
TypeTheoryDetermine[ForAll[{n}, 0 + n == n]]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_n∶ℕ 0 + n == n, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

## Scope

### Environments and Terms

Prove a linear inequality over the integers by naming the `"Integers"` environment:

```wl
TypeTheoryDetermine[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[x <= y, x <= y + 1]], "Integers"]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_x∶ℤ ∀_y∶ℤ x <= y ⇒ x <= y + 1, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

---

A [TypeTheoryTerm]() carries its own environment:

```wl
term = TypeTheoryTerm[ForAll[{Typed[x, Integers]}, x - x == 0], "Integers"]
```

<!-- => ∀_x∶ℤ x - x == 0 -->

[TypeTheoryDetermine]() checks it in the term's environment:

```wl
TypeTheoryDetermine[term]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_x∶ℤ x - x == 0, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "Portfolio", "Details" -> <||>|> -->

### Certified Independence

Declare an opaque unary function on the natural numbers:

```wl
env = TypeTheoryEnvironment[{TypeTheoryAxiom[opaqueInv, Naturals -> Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 276 constants -->

[TypeTheoryDetermine]() finds two concrete instantiations, one where `opaqueInv` is an involution and one where it is not, certifying independence in the kernel:

```wl
TypeTheoryDetermine[ForAll[{x}, opaqueInv[opaqueInv[x]] == x], env]
```

<!-- => <|"Status" -> "Independent", "Statement" -> ∀_x∶ℕ opaqueInv[opaqueInv[x]] == x, "Proof" -> None, "Counterexample" -> None, "Witness" -> None, "Models" -> <|"TrueModel" -> <|"Assignment" -> ..., "Proof" -> Proof complete|>, "FalseModel" -> <|"Assignment" -> ..., "Proof" -> Proof complete|>|>, "ComputationallyDecidable" -> False, "Method" -> "CertifiedModelIndependence", "Details" -> <||>|> -->

---

Declare an opaque carrier and binary operation:

```wl
magma = TypeTheoryEnvironment[{
    TypeTheoryAxiom[magmaCarrier, TypeUniverse[1]],
    TypeTheoryAxiom[magmaOp, magmaCarrier -> magmaCarrier -> magmaCarrier]
}]
```

<!-- => TypeTheoryEnvironment summary box: 277 constants -->

Commutativity is certified independent by a 1-element commutative model and a 2-element non-commutative model:

```wl
TypeTheoryDetermine[ForAll[{Typed[x, magmaCarrier], Typed[y, magmaCarrier]}, magmaOp[x, y] == magmaOp[y, x]], magma]
```

<!-- => <|"Status" -> "Independent", "Statement" -> ∀_x∶magmaCarrier ∀_y∶magmaCarrier magmaOp[x, y] == magmaOp[y, x], ..., "Method" -> "CertifiedModelIndependence", "Details" -> <||>|> -->

### Constructive vs. Classical Gaps

Double-negation elimination is not provable in `"Constructive"`; [TypeTheoryDetermine]() reports `"Undetermined"` and records the classical axiom gap in `"Details"`:

```wl
TypeTheoryDetermine[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]], "Constructive"]
```

<!-- => <|"Status" -> "Undetermined", "Statement" -> ∀_p∶Prop ¬¬p ⇒ p, "Proof" -> None, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "SearchExhausted", "Details" -> <|"ClassicallyProvable" -> True, "RequiredAxioms" -> <|"choice" -> "Signature", "quotientSoundness" -> "Proposition", "propositionalExtensionality" -> "Proposition"|>, "ClassicalProof" -> Proof complete|>|> -->

## Options

### Method

Formalize Gauss's triangular numbers as a recursive definition:

```wl
triangular[0] = 0;
triangular[n_Integer] := n + triangular[n - 1];
programs = TypeTheoryEnvironment[TypeTheoryFormalize[triangular]]
```

<!-- => TypeTheoryEnvironment summary box: 276 constants -->

The offline `"Heuristic"` method does not unfold the user definition and returns `"Undetermined"`:

```wl
TypeTheoryDetermine[ForAll[{n}, 2 triangular[n] == n (n + 1)], programs]
```

<!-- => <|"Status" -> "Undetermined", "Statement" -> ∀_n∶ℕ 2 triangular[n] == n (n + 1), "Proof" -> None, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> False, "Method" -> "SearchExhausted", "Details" -> <||>|> -->

Enabling `"LLM"` queries [LLMFunction]() with Wolfram AI's default model to propose candidate tactic scripts, runs them in [TypeTheoryProof](), and checks the resulting proof term in the trusted kernel:

```wl
gauss = TypeTheoryDetermine[
    ForAll[{n}, 2 triangular[n] == n (n + 1)],
    programs,
    Method -> {"Heuristic", "LLM"},
    TimeConstraint -> 45
]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_n∶ℕ 2 triangular[n] == n (n + 1), "Proof" -> Proof complete, ..., "Method" -> "LLMVerified", "Details" -> <|"Tactics" -> ...|>|> -->

The kernel accepts the LLM-assisted proof as a theorem:

```wl
TypeTheoryEnvironment[programs, {TypeTheoryTheorem[GaussFormula, gauss["Proof"]]}][GaussFormula]
```

<!-- => theorem GaussFormula : ∀_n∶ℕ 2 triangular[n] == n (n + 1) -->

### LLMEvaluator

Formalize list summation by structural recursion:

```wl
total[{}] = 0;
total[{x_, rest___}] := x + total[{rest}];
programs = TypeTheoryEnvironment[TypeTheoryFormalize[total]]
```

<!-- => TypeTheoryEnvironment summary box: 276 constants -->

Offline heuristics return `"Undetermined"` on its additivity over [Join]():

```wl
TypeTheoryDetermine[ForAll[{a, b}, total[Join[a, b]] == total[a] + total[b]], programs]
```

<!-- => <|"Status" -> "Undetermined", "Statement" -> ∀_a∶{ℕ} ∀_b∶{ℕ} total[Join[a, b]] == total[a] + total[b], "Proof" -> None, ..., "Method" -> "SearchExhausted", "Details" -> <||>|> -->

Passing prompt guidance in [LLMConfiguration]() while still using Wolfram AI's default model lets [LLMFunction]() propose the exact structural-induction and rewriting script, which the kernel verifies:

```wl
TypeTheoryDetermine[
    ForAll[{a, b}, total[Join[a, b]] == total[a] + total[b]],
    programs,
    Method -> {"Heuristic", "LLM"},
    "LLMEvaluator" -> LLMConfiguration[<|"Prompts" -> "To prove statements about total[Join[a, b]], introduce a and b, do Induction on a, use RewriteRepeated[total, Join] then Ring on the base case, then Introduce[x, rest, ih], RewriteRepeated[total, Join, ih], and Ring."|>],
    TimeConstraint -> 45
]
```

<!-- => <|"Status" -> "Proved", "Statement" -> ∀_a∶{ℕ} ∀_b∶{ℕ} total[Join[a, b]] == total[a] + total[b], "Proof" -> Proof complete, ..., "Method" -> "LLMVerified", "Details" -> <|"Tactics" -> ...|>|> -->

## Properties and Relations

A closed decidable false statement has `"ComputationallyDecidable" -> True` and `"Status" -> "Refuted"`:

```wl
refuted = TypeTheoryDetermine[2 + 2 == 5]
```

<!-- => <|"Status" -> "Refuted", "Statement" -> 2 + 2 == 5, "Proof" -> Proof complete, "Counterexample" -> None, "Witness" -> None, "Models" -> None, "ComputationallyDecidable" -> True, "Method" -> "Decide", "Details" -> <||>|> -->

Its proof checks against the negation of the statement:

```wl
TypeTheoryCheck[refuted["Proof"]["Term"], TypeTheoryTerm[Not[2 + 2 == 5]]]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

A non-proposition such as a type fails with `"NotAProposition"`:

```wl
TypeTheoryDetermine[NonNegativeIntegers]
```

<!-- => Failure["NotAProposition", ...] -->

---

Patterns stay unevaluated so they cannot accidentally launch a search:

```wl
TypeTheoryDetermine[_Association]
```

<!-- => TypeTheoryDetermine[_Association] -->
