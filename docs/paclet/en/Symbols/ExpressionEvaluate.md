---
Template: Symbol
Name: ExpressionEvaluate
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ExpressionEvaluate
Keywords: [Wolfram Language, expressions, evaluation, axiom, conditions, pattern tests, Condition, PatternTest, pattern matching, rules]
SeeAlso: [Expressions, TypeTheoryFormalize, TypeTheoryAxiomClosure, Condition, MatchFirst]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage, PatternsAndRewriting]
---

## Usage

<code>[ExpressionEvaluate]()[*e*]</code> is the expression that the Wolfram Language evaluates the expression *e* to.

## Details & Options

- [ExpressionEvaluate]() is an axiom of <code>[TypeTheoryEnvironment]()["WolframLanguage"]</code>, of the type `Expressions -> Expressions`. The kernel never computes it, so a term reduces up to it and no further, and nothing in the type theory says what it gives.
- It stands for the evaluation of the Wolfram Language, which the type theory takes as given. It is the one axiom the Wolfram Language environment adds to those of the prelude, and [TypeTheoryAxiomClosure]() lists it, as a `"Signature"`, for every term that rests on it.
- The rules of a symbol, from [TypeTheoryFormalize]() with `"Meaning" -> "Rules"`, test a condition `x_ /; test` or a pattern test `x_?test` as [SameQ]() of the [ExpressionEvaluate]() of the test and [True](), which is what the Wolfram Language tests. So do rules given to [Replace](), [ReplaceList](), [ReplaceAll]() and [ReplaceRepeated]() as terms: a rewriting by a rule with a condition computes in the kernel up to its test.
- Its argument is an expression where one is expected: a declared constant in it computes, so `ExpressionEvaluate[1 + 2]` is `ExpressionEvaluate[3]`, and [HoldForm]() quotes it as it is written.

## Basic Examples

The type of [ExpressionEvaluate]():

```wl
TypeTheoryType[ExpressionEvaluate, "WolframLanguage"]
```

<!-- => Expressions → Expressions -->

---

The value of an expression is an expression:

```wl
TypeTheoryType[ExpressionEvaluate[Construct[7, 1, 2]], "WolframLanguage"]
```

<!-- => Expressions -->

---

[ExpressionEvaluate]() is an axiom:

```wl
TypeTheoryEnvironment["WolframLanguage"][ExpressionEvaluate]
```

<!-- => axiom ExpressionEvaluate : Expressions → Expressions -->

---

The kernel does not compute it:

```wl
NormalForm[TypeTheoryTerm[ExpressionEvaluate[HoldForm[1 + 2]], "WolframLanguage"]]
```

<!-- => ExpressionEvaluate[1 + 2] -->

## Scope

The value of an expression with a symbol that names nothing:

```wl
NormalForm[TypeTheoryTerm[ExpressionEvaluate[f[x]], "WolframLanguage"]]
```

<!-- => ExpressionEvaluate[f[x]] -->

---

A natural number is an expression where one is expected:

```wl
TypeTheoryType[ExpressionEvaluate[3], "WolframLanguage"]
```

<!-- => Expressions -->

---

A condition tests the value of its test:

```wl
positive[x_ /; x > 0] := x;
Last[TypeTheoryFormalize[positive, TypeTheoryEnvironment["WolframLanguage"], "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[positive] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (x ∶ Expressions) ↦ (MatchValue[x] /; ExpressionEvaluate[x > 0] === True)] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 1]] -->

---

So does a pattern test:

```wl
positiveQ[x_?Positive] := x;
Last[TypeTheoryFormalize[positiveQ, TypeTheoryEnvironment["WolframLanguage"], "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[positiveQ] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (x ∶ Expressions) ↦ (MatchValue[x] /; ExpressionEvaluate[Positive[x]] === True)] /; ¬AtomQ[expression] ∧ Decide[Length[{Arguments[expression]}] == 1]] -->

## Properties and Relations

[ExpressionEvaluate]() is the one axiom the Wolfram Language environment adds to the three of the prelude:

```wl
Information[TypeTheoryEnvironment["WolframLanguage"], "Axioms"]
```

<!-- => {"propositionalExtensionality", "quotientSoundness", "choice", ExpressionEvaluate} -->

---

A term that uses it rests on it:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm[ExpressionEvaluate[HoldForm[x]], "WolframLanguage"]]
```

<!-- => <|ExpressionEvaluate -> "Signature"|> -->

---

The rules of a function with a condition:

```wl
positive[x_ /; x > 0] := x;
positives = TypeTheoryEnvironment["WolframLanguage", TypeTheoryFormalize[positive, "WolframLanguage", "Meaning" -> "Rules"]]
```

<!-- => TypeTheoryEnvironment summary box: 226 constants -->

They rest on [ExpressionEvaluate]():

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["DownValues[positive]", positives]]
```

<!-- => <|ExpressionEvaluate -> "Signature"|> -->

An expression the pattern does not match, with two arguments, computes to none before the condition is tested:

```wl
NormalForm[TypeTheoryTerm["DownValues[positive]"[positive[1, 2]], positives]]
```

<!-- => none -->

---

The value of `1 + 2` is not 3 by computation, since the kernel does not evaluate:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[ExpressionEvaluate[HoldForm[1 + 2]], "WolframLanguage"], TypeTheoryTerm[HoldForm[3], "WolframLanguage"]]
```

<!-- => False -->

## Possible Issues

A declared constant in the argument computes first, so the sum is 3 before it is evaluated; [HoldForm]() keeps it as it is written:

```wl
NormalForm[TypeTheoryTerm[ExpressionEvaluate[1 + 2], "WolframLanguage"]]
```

<!-- => ExpressionEvaluate[3] -->

---

A rule with a condition does not rewrite in the kernel, which cannot evaluate the test:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Replace[f[1], f[x_ /; x > 0] :> x], "WolframLanguage"], TypeTheoryTerm[Typed[1, Expressions], "WolframLanguage"]]
```

<!-- => False -->

The same rule without the condition does:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Replace[f[1], f[x_] :> x], "WolframLanguage"], TypeTheoryTerm[Typed[1, Expressions], "WolframLanguage"]]
```

<!-- => True -->

---

The value is an expression, not a natural number:

```wl
TypeTheoryType[Typed[ExpressionEvaluate[3], NonNegativeIntegers], "WolframLanguage"]
```

<!-- => Failure["TypeMismatch", ...] -->
