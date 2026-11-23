---
Template: Symbol
Name: TypeTheoryTermination
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/TypeTheoryTermination
Keywords: [termination, non-termination, well-foundedness, ranking function, Farkas, polynomial interpretation, rewrite rules, DownValues, lasso, divergence, conditional termination, TypeTheoryFormalize]
SeeAlso: [TypeTheoryFormalize, TypeTheoryDetermine, TypeTheoryAssumptions, TypeTheoryConsequences, TypeTheoryProof, TypeTheoryTheorem, Expressions]
RelatedGuides: [TypeTheory]
RelatedTutorials: [AutomatedAnalysisAndDiscovery, TheWolframLanguage, PatternsAndRewriting, ProgramsAndProofs]
---

## Usage

<code>[TypeTheoryTermination]()[*symbol*]</code> analyzes termination of a Wolfram Language function or rewrite symbol formalized via [TypeTheoryFormalize](), returning an [Association]() with `"Status"` (`"Terminating"`, `"NonTerminating"`, `"ConditionallyTerminating"` or `"Undetermined"`) and kernel-checked certificates.

<code>[TypeTheoryTermination]()[*symbol*, *env*]</code> analyzes *symbol* in the [TypeTheoryEnvironment]() *env*, or in the library environment named by *env*.

<code>[TypeTheoryTermination]()[*expression*, *rules*]</code> checks pointwise termination or non-termination (lasso cycle) of *expression* under the list of rewrite rules *rules*.

<code>[TypeTheoryTermination]()[*rules*]</code> checks global termination of a list of rewrite rules via polynomial weight interpretations or divergence witnesses.

## Details & Options

- [TypeTheoryTermination]() has the [HoldAll]() attribute so symbols, expressions and rewrite rules are inspected without evaluating.
- Every `"Terminating"`, `"NonTerminating"` and `"ConditionallyTerminating"` verdict with `"Verified" -> True` is backed by a kernel-checked [TypeTheoryProof]():
  - **Pointwise rewrite termination**: a kernel proof that `iterateReplaceAll[k, expr]` reaches a fixed point in `k` steps (`"Steps" -> k`).
  - **Global rewrite termination**: a synthesized polynomial weight interpretation `expressionWeight : Expressions -> ℕ` together with kernel-checked strict decrease proofs `expressionWeight[rhs] < expressionWeight[lhs]` for every rule (`"Method" -> "PolynomialWeightInterpretation"`).
  - **Pointwise lasso non-termination**: a kernel proof by induction on the step count that `iterateDownValues[n, expr]` stays on a finite cycle and never equals `"none"` (`"Method" -> "LassoCycleInduction"`).
  - **Unbounded divergence**: a kernel proof by induction of a self-embedding invariant showing every step produces another matching call (`"Method" -> "SelfEmbeddingDivergenceInvariant"`).
  - **Integer loops and recursive functions**: Farkas-synthesized affine ranking functions proved in `"Integers"` (`"Method" -> "FarkasAffineRankingFunction"`), or conditional termination with both a `"Precondition"`, a kernel-checked `"TerminationProof"`, a `"NonTerminationWitness"`, and a kernel-checked `"NonTerminationProof"`.
  - **Structural recursion**: functions that [TypeTheoryFormalize]() translates directly into a total [TypeTheoryDefinition]() over an inductive recursor are total by construction (`"Method" -> "StructuralRecursor"`).
- The following options can be given:

| Option | Default | Description |
| --- | --- | --- |
| [Method]() | [Automatic]() | `"Heuristic"` (offline default), `"LLM"`, or `{"Heuristic", "LLM"}` |
| `"Meaning"` | [Automatic]() | `"Function"`, `"Rules"`, or `"Compiled"` (or [Automatic]() to select based on the symbol's definitions) |
| `"MaxSteps"` | `100` | maximum rewrite or simulation steps for pointwise probes |
| [TimeConstraint]() | `15` | time budget in seconds |
| `"LLMEvaluator"` | [Automatic]() | [Automatic]() for Wolfram AI's default model, an [LLMConfiguration](), or a prompt guidance string |

## Basic Examples

Certify pointwise termination of an expression under a rewrite rule:

```wl
TypeTheoryTermination[rwA[rwB[0]], {rwA[rwB[x_]] :> rwB[rwA[x]]}]
```

<!-- => <|"Status" -> "Terminating", "Target" -> rwA[rwB[0]], "Steps" -> 1, "NormalForm" -> rwB[rwA[0]], "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "ConcreteExecution", "Verified" -> True|> -->

---

Certify global termination of a rewrite rule system by synthesizing a polynomial weight interpretation and verifying strict decrease in the kernel:

```wl
TypeTheoryTermination[{rwA[rwB[x_]] :> rwB[rwA[x]]}]
```

<!-- => <|"Status" -> "Terminating", "Target" -> {rwA[rwB[x_]] :> rwB[rwA[x]]}, "Measure" -> ..., "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "PolynomialWeightInterpretation", "Verified" -> True|> -->

---

Certify termination of an integer [While]() loop via a Farkas affine ranking function proved in `"Integers"`:

```wl
sumLoop[n_Integer] := Module[{i = n, s = 0}, While[i > 0, s += i; i--]; s];
loopRes = TypeTheoryTermination[sumLoop]
```

<!-- => <|"Status" -> "Terminating", "Target" -> sumLoop, "Measure" -> "i", "FuelBound" -> Max[0, n] + 1, "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "FarkasAffineRankingFunction", "Verified" -> True|> -->

The descent proof is accepted as a theorem in `"Integers"`:

```wl
TypeTheoryEnvironment["Integers", {TypeTheoryTheorem[SumLoopTerminates, loopRes["Proof"]]}][SumLoopTerminates]
```

<!-- => theorem SumLoopTerminates : ℤ → ∀_i∶ℤ 0 < i ⇒ 0 <= i ∧ i - 1 < i -->

## Scope

### Conditional Termination and Divergence Witnesses

For an integer factorial written with `n == 0` as the base case, [TypeTheoryTermination]() certifies `"ConditionallyTerminating"` under `"0 <= n"` and also proves divergence at `n == -1`:

```wl
factFn[n_Integer] := If[n == 0, 1, n * factFn[n - 1]];
TypeTheoryTermination[factFn]
```

<!-- => <|"Status" -> "ConditionallyTerminating", "Target" -> factFn, "Precondition" -> "0 <= n", "Measure" -> "n", "TerminationProof" -> Proof complete, "NonTerminationWitness" -> <|"n" -> -1|>, "NonTerminationProof" -> Proof complete, "Method" -> "ConditionalFarkasAndDivergence", "Verified" -> True|> -->

### Non-Termination Certificates

A cyclic rewrite definition is certified `"NonTerminating"` by lasso cycle induction:

```wl
lassoFn[x_] := lassoFn[x];
TypeTheoryTermination[lassoFn[0]]
```

<!-- => <|"Status" -> "NonTerminating", "Target" -> lassoFn[0], "Cycle" -> <|"PrefixLength" -> 0, "Period" -> 1, "States" -> {lassoFn[0]}|>, "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "LassoCycleInduction", "Verified" -> True|> -->

---

An unbounded self-embedding rewrite `growFn[x_] := growFn[x + 1]` is certified `"NonTerminating"` by a kernel-checked divergence invariant:

```wl
growFn[x_] := growFn[x + 1];
TypeTheoryTermination[growFn, "Meaning" -> "Rules"]
```

<!-- => <|"Status" -> "NonTerminating", "Target" -> growFn, "Statement" -> ..., "Proof" -> Proof complete, "Method" -> "SelfEmbeddingDivergenceInvariant", "Verified" -> True|> -->

## Options

### Meaning

With `"Meaning" -> "Function"`, a function that [TypeTheoryFormalize]() translates directly into a total definition is certified by structural recursion:

```wl
doubleInt[n_Integer] := 2 n;
TypeTheoryTermination[doubleInt, "Meaning" -> "Function"]
```

<!-- => <|"Status" -> "Terminating", "Target" -> doubleInt, "Method" -> "StructuralRecursor", "Verified" -> True, ...|> -->

## Properties and Relations

Certify termination of an integer [While]() loop:

```wl
sumLoop[n_Integer] := Module[{i = n, s = 0}, While[i > 0, s += i; i--]; s];
res = TypeTheoryTermination[sumLoop]
```

<!-- => <|"Status" -> "Terminating", "Target" -> sumLoop, "Measure" -> "i", ..., "Proof" -> Proof complete, "Method" -> "FarkasAffineRankingFunction", "Verified" -> True|> -->

Its proof checks directly with [TypeTheoryCheck]():

```wl
TypeTheoryCheck[res["Proof"]["Term"], res["Statement"]]
```

<!-- => Success["TypeChecked", ...] -->

## Possible Issues

A symbol with no [DownValues]() cannot be analyzed as a function or rewrite system and gives a [Failure]():

```wl
TypeTheoryTermination[undefinedSymbol]
```

<!-- => Failure["NoDefinitions", ...] -->
