---
Template: Symbol
Name: ExpressionEvaluate
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ExpressionEvaluate
Keywords: [Wolfram Language, expressions, evaluation, axiom, conditions, pattern tests, Condition, PatternTest, pattern matching, rules, prelude]
SeeAlso: [Expressions, TypeTheoryFormalize, TypeTheoryAxiomClosure, Condition, MatchFirst]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[ExpressionEvaluate]()[*e*]</code> is the expression that the Wolfram Language evaluates the expression *e* to.

## Details & Options

- [ExpressionEvaluate]() is an axiom of the prelude, of the type `Expressions -> Expressions`. The kernel never computes it, so a term reduces up to it and no further, and nothing in the type theory says what it gives.
- It stands for the evaluation of the Wolfram Language, which the type theory takes as given. It is one of the four axioms of the prelude, beside `"propositionalExtensionality"`, `"quotientSoundness"` and `"choice"`, and [TypeTheoryAxiomClosure]() lists it, as a `"Signature"`, for every term that rests on it.
- The rules of a symbol, from [TypeTheoryFormalize]() with `"Meaning" -> "Rules"`, test a condition `x_ /; test` or a pattern test `x_?test` as [SameQ]() of the [ExpressionEvaluate]() of the test and [True](), a Boolean, which is what the Wolfram Language tests. So do rules given to [Replace](), [ReplaceList](), [ReplaceAll]() and [ReplaceRepeated]() as terms: a rewriting by a rule with a condition computes in the kernel up to its test, so the kernel still decides every expression whose head or arguments the rule does not match.
- Its argument is an expression where one is expected: a declared constant in it computes, so `ExpressionEvaluate[1 + 2]` is `ExpressionEvaluate[3]`, and [Unevaluated]() quotes it as it is written.

## Basic Examples

[ExpressionEvaluate]() takes an expression to an expression:

```wl
TypeTheoryType[ExpressionEvaluate]
```

<!-- => Expressions → Expressions -->

---

It is an axiom:

```wl
TypeTheoryEnvironment["Prelude"][ExpressionEvaluate]
```

<!-- => axiom ExpressionEvaluate : Expressions → Expressions -->

---

The kernel does not evaluate an expression, so the value of `Sin[0]` stays as it is:

```wl
NormalForm[TypeTheoryTerm[ExpressionEvaluate[Sin[0]]]]
```

<!-- => ExpressionEvaluate[Sin[0]] -->

---

A condition in a rule tests the value of its test:

```wl
positive[x_ /; x > 0] := x;
Last[TypeTheoryFormalize[positive, "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[positive] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (x ∶ Expressions) ↦ (MatchValue[x] /; ExpressionEvaluate[x > 0] === True)] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 1]] -->

## Scope

The test of a condition is a Boolean, whether the value is [True]():

```wl
TypeTheoryType[SameQ[ExpressionEvaluate[1 > 0], True]]
```

<!-- => 𝔹 -->

---

A pattern test tests the value of the function applied:

```wl
halved[n_?EvenQ] := n/2;
Last[TypeTheoryFormalize[halved, "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[halved] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (n ∶ Expressions) ↦ (MatchValue[n/2] /; ExpressionEvaluate[EvenQ[n]] === True)] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 1]] -->

---

The rules of `positive` in an environment:

```wl
positive[x_ /; x > 0] := x;
positives = TypeTheoryEnvironment[TypeTheoryFormalize[positive, "Meaning" -> "Rules"]]
```

<!-- => TypeTheoryEnvironment summary box: 258 constants -->

They take an expression to the option of the expression it rewrites to:

```wl
TypeTheoryType["DownValues[positive]", positives]
```

<!-- => Expressions → Option[Expressions] -->

An expression with two arguments does not match the pattern, so the kernel computes that no rule applies without the test:

```wl
NormalForm[TypeTheoryTerm["DownValues[positive]"[positive[1, 2]], positives]]
```

<!-- => none -->

---

A rule with a condition rewrites in the kernel an expression whose head it does not match, leaving it as it is:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Replace[g[5], f[x_ /; x > 0] :> x]], TypeTheoryTerm[g[5]]]
```

<!-- => True -->

Where the head matches, the rewriting stops at the test, which the kernel cannot evaluate, so it is not 5 by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Replace[f[5], f[x_ /; x > 0] :> x]], TypeTheoryTerm[Typed[5, Expressions]]]
```

<!-- => False -->

The same rule without the condition rewrites `f[5]` to 5:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Replace[f[5], f[x_] :> x]], TypeTheoryTerm[Typed[5, Expressions]]]
```

<!-- => True -->

## Properties and Relations

[ExpressionEvaluate]() is one of the four axioms of the prelude:

```wl
Information[TypeTheoryEnvironment["Prelude"], "Axioms"]
```

<!-- => {"propositionalExtensionality", "quotientSoundness", "choice", ExpressionEvaluate} -->

---

A rewriting by a rule with a condition rests on [ExpressionEvaluate]():

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Replace[f[5], f[x_ /; x > 0] :> x]]]
```

<!-- => <|ExpressionEvaluate -> "Signature"|> -->

One without a condition rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[Replace[f[5], f[x_] :> x]]]
```

<!-- => <||> -->

---

The value of `Sin[0]` is not 0 by computation, since nothing in the type theory says what the Wolfram Language evaluates it to:

```wl
TypeTheoryProof[ExpressionEvaluate[Sin[0]] == 0, {"Reflexivity"}]
```

<!-- => Failure["NotReflexive", ...] -->

## Possible Issues

A declared constant in the argument computes first, so the sum is 3 before it is evaluated; [Unevaluated]() keeps it as it is written:

```wl
NormalForm[TypeTheoryTerm[ExpressionEvaluate[1 + 2]]]
```

<!-- => ExpressionEvaluate[3] -->

---

The value is an expression, not a natural number:

```wl
TypeTheoryType[Typed[ExpressionEvaluate[3], NonNegativeIntegers]]
```

<!-- => Failure["TypeMismatch", ...] -->
