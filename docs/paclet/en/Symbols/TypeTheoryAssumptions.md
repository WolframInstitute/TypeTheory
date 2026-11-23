---
Template: Symbol
Name: TypeTheoryAssumptions
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryAssumptions
Keywords: [assumptions, abduction, hypotheses, missing assumptions, preconditions, guards, excluded middle, algebraic properties, holes, LLM, LLMFunction]
SeeAlso: [TypeTheoryDetermine, TypeTheoryConsequences, TypeTheoryTermination, TypeTheoryProof, TypeTheoryTheorem, LLMFunction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [AutomatedAnalysisAndDiscovery, TypeTheoryIntroduction, ProgramsAndProofs]
---

## Usage

<code>[TypeTheoryAssumptions]()[*proposition*]</code> finds ranked, sensible, non-vacuous and non-trivial assumptions *A* that turn an unprovable *proposition* into a kernel-checked theorem <code>*A* ⇒ *proposition*</code> in the default environment, [$TypeTheoryEnvironment]().

<code>[TypeTheoryAssumptions]()[*proposition*, *env*]</code> searches for assumptions in the [TypeTheoryEnvironment]() *env*, or in the library environment named by *env*, such as `"Constructive"` or `"Integers"`.

<code>[TypeTheoryAssumptions]()[[TypeTheoryTerm]()[*proposition*, *env*]]</code> searches in the term's own environment *env*.

<code>[TypeTheoryAssumptions]()[*openProof*]</code> extracts and packages the assumptions needed to close the open goals of an unfinished [TypeTheoryProof]().

## Details & Options

- [TypeTheoryAssumptions]() has the [HoldFirst]() attribute: *proposition* stays held, patterns such as <code>[TypeTheoryAssumptions]()[_[Association]()]</code> stay unevaluated, and non-propositions give a [Failure]() tagged `"NotAProposition"`.
- If *proposition* is already provable, [TypeTheoryAssumptions]() returns `{}`.
- Each result is an [Association]() with `"Assumption"` (the discovered guard or global hypothesis as a [TypeTheoryTerm]()), `"Statement"` (the full guarded theorem), `"Proof"` (a finished, kernel-checked [TypeTheoryProof]() of `"Statement"`), `"Scope"` (`"Local"`, `"Global"` or `"GoalHole"`), `"Method"`, `"Witness"` (a non-vacuity witness when found), and `"Verified" -> True`.
- Every candidate passes three quality gates before being returned: a kernel-checked proof of the guarded statement, a non-vacuity check rejecting contradictory assumptions such as [False](), and a non-triviality check rejecting assumptions identical to the conclusion (or proving the consequent while ignoring existing premises). Redundant stronger assumptions implied by simpler ones are pruned.
- The offline heuristic portfolio combines symbolic domain abduction ([Reduce]()), tactic-residual lemma abduction, axiom-diff discovery (for example, excluded middle in `"Constructive"`), counterexample-guided refinement, and an algebraic property catalog for opaque operations.
- The following options can be given:

| Option | Default | Description |
| --- | --- | --- |
| [Method]() | [Automatic]() | `"Heuristic"` (offline default), `"LLM"`, or `{"Heuristic", "LLM"}` |
| [TimeConstraint]() | `15` | time budget in seconds |
| [MaxItems]() | `5` | maximum number of ranked assumptions to return |
| `"EquivalentConditions"` | [True]() | whether to allow logically equivalent reformulations that are strictly simpler than the target |
| `"IncludeOpen"` | [False]() | whether to include unverified candidates when no proof was found |
| `"LLMEvaluator"` | [Automatic]() | [Automatic]() for Wolfram AI's default model, an [LLMConfiguration](), or a prompt guidance string |

## Basic Examples

Find the missing guards for `n^2 <= 2^n` on natural numbers (which fails only at `n == 3`):

```wl
assumptions = TypeTheoryAssumptions[ForAll[{n}, n^2 <= 2^n]]
```

<!-- => {<|"Assumption" -> 4 <= n, "Statement" -> ∀_n∶ℕ 4 <= n ⇒ n^2 <= 2^n, "Proof" -> Proof complete, "Scope" -> "Local", "Method" -> "SymbolicDomain", "Witness" -> <|"n" -> 4|>, "Verified" -> True|>, <|"Assumption" -> n != 3, "Statement" -> ∀_n∶ℕ n != 3 ⇒ n^2 <= 2^n, "Proof" -> Proof complete, "Scope" -> "Local", "Method" -> "CounterexampleRefinement", "Witness" -> <|"n" -> 0|>, "Verified" -> True|>} -->

Each returned proof is accepted as a theorem by the kernel:

```wl
TypeTheoryEnvironment[TypeTheoryTheorem[TailBound, First[assumptions]["Proof"]]][TailBound]
```

<!-- => theorem TailBound : ∀_n∶ℕ 4 <= n ⇒ n^2 <= 2^n -->

---

Discover the guard `b <= a` needed for natural-number subtraction cancellation:

```wl
TypeTheoryAssumptions[ForAll[{a, b}, Subtract[a, b] + b == a]]
```

<!-- => {<|"Assumption" -> b <= a, "Statement" -> ∀_a∶ℕ ∀_b∶ℕ b <= a ⇒ (a - b) + b == a, "Proof" -> Proof complete, "Scope" -> "Local", "Method" -> "SymbolicDomain", "Witness" -> <|"a" -> 0, "b" -> 0|>, "Verified" -> True|>} -->

---

For multiplicative cancellation `a * c == b * c => a == b`, [TypeTheoryAssumptions]() finds `1 <= c` (or `c != 0`) and filters out the trivial assumption `a == b`:

```wl
TypeTheoryAssumptions[ForAll[{a, b, c}, Implies[a c == b c, a == b]]]
```

<!-- => {<|"Assumption" -> 1 <= c, "Statement" -> ∀_a∶ℕ ∀_b∶ℕ ∀_c∶ℕ 1 <= c ⇒ a c == b c ⇒ a == b, "Proof" -> Proof complete, "Scope" -> "Local", ...|>} -->

## Scope

### Missing Axioms

In `"Constructive"`, double-negation elimination lacks the law of excluded middle; [TypeTheoryAssumptions]() discovers it via `"AxiomDiff"`:

```wl
TypeTheoryAssumptions[ForAll[{Typed[p, TypeUniverse[0]]}, Implies[Not[Not[p]], p]], "Constructive"]
```

<!-- => {<|"Assumption" -> ∀_p∶Prop p ∨ ¬p, "Statement" -> (∀_p∶Prop p ∨ ¬p) ⇒ ∀_p∶Prop ¬¬p ⇒ p, "Proof" -> Proof complete, "Scope" -> "Global", "Method" -> "AxiomDiff", "Witness" -> None, "Verified" -> True, "AxiomName" -> "excludedMiddle"|>} -->

### Algebraic Properties

Declare an opaque carrier and binary operation:

```wl
algebra = TypeTheoryEnvironment[{
    TypeTheoryAxiom[algCarrier, TypeUniverse[1]],
    TypeTheoryAxiom[algOp, algCarrier -> algCarrier -> algCarrier]
}]
```

<!-- => TypeTheoryEnvironment summary box: 277 constants -->

[TypeTheoryAssumptions]() discovers that commutativity and associativity make `algOp[algOp[x, y], z] == algOp[x, algOp[z, y]]` provable:

```wl
TypeTheoryAssumptions[ForAll[{Typed[x, algCarrier], Typed[y, algCarrier], Typed[z, algCarrier]}, algOp[algOp[x, y], z] == algOp[x, algOp[z, y]]], algebra]
```

<!-- => {<|"Assumption" -> (∀_x∶algCarrier ∀_y∶algCarrier algOp[x, y] == algOp[y, x]) ∧ (∀_x∶algCarrier ∀_y∶algCarrier ∀_z∶algCarrier algOp[algOp[x, y], z] == algOp[x, algOp[y, z]]), ..., "Method" -> "AlgebraicCatalog", "Verified" -> True|>} -->

### Open Proofs

Start a proof and leave one goal open:

```wl
openProof = TypeTheoryProof[ForAll[{n}, n == 0], {"Introduce"[n]}]
```

<!-- => Proof, 1 goal: n ∶ ℕ ⊢ n == 0 -->

[TypeTheoryAssumptions]() extracts the minimal quantified assumption needed to close the remaining goal:

```wl
TypeTheoryAssumptions[openProof]
```

<!-- => {<|"Assumption" -> ∀_n∶ℕ n == 0, "Statement" -> (∀_n∶ℕ n == 0) ⇒ ∀_n∶ℕ n == 0, "Proof" -> Proof complete, "Scope" -> "GoalHole", "Witness" -> None, "Method" -> "OpenGoalAbstraction", "Verified" -> True|>} -->

## Options

### Method and LLMEvaluator

Declare two opaque functions on the natural numbers:

```wl
env = TypeTheoryEnvironment[{
    TypeTheoryAxiom[leftInverse, Naturals -> Naturals],
    TypeTheoryAxiom[fnG, Naturals -> Naturals]
}]
```

<!-- => TypeTheoryEnvironment summary box: 277 constants -->

Offline heuristics know single-function algebraic properties (`fnG[x] == x`, `fnG[fnG[x]] == x`) but do not synthesize cross-function hypotheses relating two separate axioms. With `Method -> "LLM"` and prompt guidance in [LLMConfiguration](), [LLMFunction]() proposes the left-inverse assumption and the kernel verifies that it implies injectivity:

```wl
TypeTheoryAssumptions[
    ForAll[{x, y}, Implies[fnG[x] == fnG[y], x == y]],
    env,
    Method -> "LLM",
    "LLMEvaluator" -> LLMConfiguration[<|"Prompts" -> "Suggest an assumption relating leftInverse and fnG (such as leftInverse being a left inverse of fnG) that implies fnG is injective."|>],
    TimeConstraint -> 45
]
```

<!-- => {<|"Assumption" -> ∀_n∶ℕ leftInverse[fnG[n]] == n, "Statement" -> (∀_n∶ℕ leftInverse[fnG[n]] == n) ⇒ ∀_x∶ℕ ∀_y∶ℕ fnG[x] == fnG[y] ⇒ x == y, "Proof" -> Proof complete, "Scope" -> "Global", "Method" -> "LLM", "Witness" -> None, "Verified" -> True|>} -->

## Properties and Relations

An already provable theorem needs no additional assumptions and returns `{}`:

```wl
TypeTheoryAssumptions[ForAll[{n}, n + 0 == n]]
```

<!-- => {} -->

## Possible Issues

A pattern stays unevaluated:

```wl
TypeTheoryAssumptions[_Association]
```

<!-- => TypeTheoryAssumptions[_Association] -->
