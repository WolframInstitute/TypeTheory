---
Template: Symbol
Name: TypeTheoryConsequences
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryConsequences
Keywords: [consequences, deduction, forward chaining, implications, relevance, inconsistency, projection, involution, classical logic, LLM, LLMFunction]
SeeAlso: [TypeTheoryDetermine, TypeTheoryAssumptions, TypeTheoryTermination, TypeTheoryProof, TypeTheoryTheorem, LLMFunction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [AutomatedAnalysisAndDiscovery, TypeTheoryIntroduction, ProgramsAndProofs]
---

## Usage

<code>[TypeTheoryConsequences]()[*proposition*]</code> discovers ranked, sensible, non-trivial consequences *C* following from *proposition* assumed true in the default environment, [$TypeTheoryEnvironment]().

<code>[TypeTheoryConsequences]()[*proposition*, *env*]</code> searches in the [TypeTheoryEnvironment]() *env*, or in the library environment named by *env*, such as `"Constructive"` or `"Integers"`.

<code>[TypeTheoryConsequences]()[[TypeTheoryTerm]()[*proposition*, *env*]]</code> searches in the term's own environment *env*.

## Details & Options

- [TypeTheoryConsequences]() has the [HoldFirst]() attribute: *proposition* stays held, patterns such as <code>[TypeTheoryConsequences]()[_[Association]()]</code> stay unevaluated, and non-propositions give a [Failure]() tagged `"NotAProposition"`.
- If <code>[Not]()[*proposition*]</code> is provable, [TypeTheoryConsequences]() short-circuits and returns a single entry whose `"Consequence"` is [False](), tagged `"Inconsistent" -> True`, with a kernel-checked refutation proof.
- Each entry is an [Association]() with `"Consequence"` (a [TypeTheoryTerm]()), `"Statement"` (the implication <code>*proposition* ⇒ *consequence*</code>), `"Proof"` (a finished, kernel-checked [TypeTheoryProof]() of `"Statement"`), `"Method"`, `"Inconsistent"`, and `"Verified" -> True`.
- Every candidate passes four quality gates before being returned:
  1. a kernel-checked proof of <code>*proposition* ⇒ *consequence*</code>;
  2. an exact proof-term relevance check verifying that the hypothesis variable for *proposition* occurs free in the normalized proof term;
  3. a non-background novelty check rejecting consequences already provable without *proposition*;
  4. a non-triviality filter rejecting [True](), *proposition* itself, trivial weakenings, and equivalents (unless `"IncludeEquivalents" -> True`).
- Redundant weaker consequences implied by stronger discovered consequences are pruned before ranking.
- The offline heuristic portfolio combines structural elimination, forward-chaining through environment lemmas (such as antisymmetry), symbolic projection via [Reduce](), and equational/algebraic property discovery (such as injectivity, surjectivity, and classical principles).
- The following options can be given:

| Option | Default | Description |
| --- | --- | --- |
| [Method]() | [Automatic]() | `"Heuristic"` (offline default), `"LLM"`, or `{"Heuristic", "LLM"}` |
| [TimeConstraint]() | `15` | time budget in seconds |
| [MaxItems]() | `8` | maximum number of ranked consequences to return |
| `"IncludeEquivalents"` | [False]() | whether to keep consequences logically equivalent to *proposition* |
| `"LLMEvaluator"` | [Automatic]() | [Automatic]() for Wolfram AI's default model, an [LLMConfiguration](), or a prompt guidance string |

## Basic Examples

Declare an opaque unary function on the natural numbers:

```wl
env = TypeTheoryEnvironment[{TypeTheoryAxiom[involFn, Naturals -> Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 276 constants -->

From the involution hypothesis `involFn[involFn[x]] == x`, [TypeTheoryConsequences]() derives canonical instances, surjectivity, injectivity, and the third-iterate identity, each with a kernel-checked proof:

```wl
consequences = TypeTheoryConsequences[ForAll[{x}, involFn[involFn[x]] == x], env]
```

<!-- => {<|"Consequence" -> involFn[involFn[0]] == 0, "Statement" -> (∀_x∶ℕ involFn[involFn[x]] == x) ⇒ involFn[involFn[0]] == 0, "Proof" -> Proof complete, "Method" -> "CanonicalSpecialization", "Inconsistent" -> False, "Verified" -> True|>, ...} -->

Every returned proof can be declared as a theorem in the environment:

```wl
TypeTheoryEnvironment[env, {TypeTheoryTheorem[InvolutionConsequence, First[consequences]["Proof"]]}][InvolutionConsequence]
```

<!-- => theorem InvolutionConsequence : (∀_x∶ℕ involFn[involFn[x]] == x) ⇒ involFn[involFn[0]] == 0 -->

---

Declare two natural-number constants:

```wl
circle = TypeTheoryEnvironment[{TypeTheoryAxiom[xCircle, Naturals], TypeTheoryAxiom[yCircle, Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 277 constants -->

From a polynomial equation, symbolic projection derives tight coordinate bounds:

```wl
TypeTheoryConsequences[xCircle^2 + yCircle^2 == 25, circle]
```

<!-- => {<|"Consequence" -> xCircle <= 5, "Statement" -> xCircle^2 + yCircle^2 == 25 ⇒ xCircle <= 5, "Proof" -> Proof complete, "Method" -> "SymbolicProjection", "Inconsistent" -> False, "Verified" -> True|>, <|"Consequence" -> yCircle <= 5, "Statement" -> xCircle^2 + yCircle^2 == 25 ⇒ yCircle <= 5, "Proof" -> Proof complete, "Method" -> "SymbolicProjection", "Inconsistent" -> False, "Verified" -> True|>} -->

---

Declare two natural-number constants:

```wl
ordered = TypeTheoryEnvironment[{TypeTheoryAxiom[aOrd, Naturals], TypeTheoryAxiom[bOrd, Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 277 constants -->

From a conjunction of inequalities, forward chaining applies antisymmetry to derive equality:

```wl
TypeTheoryConsequences[And[aOrd <= bOrd, bOrd <= aOrd], ordered]
```

<!-- => {<|"Consequence" -> aOrd == bOrd, "Statement" -> aOrd <= bOrd ∧ bOrd <= aOrd ⇒ aOrd == bOrd, "Proof" -> Proof complete, "Method" -> "ForwardChaining", "Inconsistent" -> False, "Verified" -> True|>} -->

## Scope

### Classical Principles in `"Constructive"`

Assuming the law of excluded middle in `"Constructive"` yields double-negation elimination, Peirce's law, and contraposition:

```wl
TypeTheoryConsequences[ForAll[{Typed[p, TypeUniverse[0]]}, Or[p, Not[p]]], "Constructive"]
```

<!-- => {<|"Consequence" -> ∀_p∶Prop ¬¬p ⇒ p, ..., "Verified" -> True|>, <|"Consequence" -> ∀_p∶Prop ∀_q∶Prop ((p ⇒ q) ⇒ p) ⇒ p, ..., "Verified" -> True|>, <|"Consequence" -> ∀_p∶Prop ∀_q∶Prop (¬q ⇒ ¬p) ⇒ p ⇒ q, ..., "Verified" -> True|>} -->

### Inconsistency Short-Circuit

If the assumed proposition is refutable, [TypeTheoryConsequences]() short-circuits to [False]() rather than emitting arbitrary ex-falso consequences:

```wl
TypeTheoryConsequences[ForAll[{n}, n^2 <= 2^n]]
```

<!-- => {<|"Consequence" -> False, "Statement" -> (∀_n∶ℕ n^2 <= 2^n) ⇒ False, "Proof" -> Proof complete, "Method" -> "InconsistencyShortCircuit", "Inconsistent" -> True, "Verified" -> True|>} -->

## Options

### Method

Declare an opaque unary function on the natural numbers:

```wl
env = TypeTheoryEnvironment[{TypeTheoryAxiom[additiveF, Naturals -> Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 276 constants -->

For an additive function `additiveF[x + y] == additiveF[x] + additiveF[y]`, enabling `Method -> "LLM"` uses [LLMFunction]() with Wolfram AI's default model to propose candidate consequences such as `additiveF[x + x] == additiveF[x] + additiveF[x]`, which are then kernel-checked and verified to genuinely depend on the hypothesis:

```wl
TypeTheoryConsequences[
    ForAll[{x, y}, additiveF[x + y] == additiveF[x] + additiveF[y]],
    env,
    Method -> "LLM",
    TimeConstraint -> 45
]
```

<!-- => {<|"Consequence" -> ∀_x∶ℕ additiveF[x + x] == additiveF[x] + additiveF[x], "Statement" -> (∀_x∶ℕ ∀_y∶ℕ additiveF[x + y] == additiveF[x] + additiveF[y]) ⇒ ∀_x∶ℕ additiveF[x + x] == additiveF[x] + additiveF[x], "Proof" -> Proof complete, "Method" -> "LLM", "Inconsistent" -> False, "Verified" -> True|>} -->

## Properties and Relations

Declare two natural-number constants and derive their consequences:

```wl
ordered = TypeTheoryEnvironment[{TypeTheoryAxiom[aOrd, Naturals], TypeTheoryAxiom[bOrd, Naturals]}]
```

<!-- => TypeTheoryEnvironment summary box: 277 constants -->

```wl
consequences = TypeTheoryConsequences[And[aOrd <= bOrd, bOrd <= aOrd], ordered]
```

<!-- => {<|"Consequence" -> aOrd == bOrd, "Statement" -> aOrd <= bOrd ∧ bOrd <= aOrd ⇒ aOrd == bOrd, "Proof" -> Proof complete, "Method" -> "ForwardChaining", "Inconsistent" -> False, "Verified" -> True|>} -->

Every consequence's proof passes [TypeTheoryCheck]() against its `"Statement"`:

```wl
TypeTheoryCheck[First[consequences]["Proof"]["Term"], First[consequences]["Statement"]]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

A pattern stays unevaluated:

```wl
TypeTheoryConsequences[_Association]
```

<!-- => TypeTheoryConsequences[_Association] -->
