---
Template: Symbol
Name: ExpressionEvaluate
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ExpressionEvaluate
Keywords: [Wolfram Language, expressions, evaluation, conditions, pattern matching]
SeeAlso: [Expressions, TypeTheoryFormalize, Condition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[ExpressionEvaluate]()[*e*] is the expression that the Wolfram Language evaluates the expression *e* to.

## Details & Options

- [ExpressionEvaluate]() is an axiom of [TypeTheoryEnvironment]()["WolframLanguage"], of type `Expressions -> Expressions`. The kernel never computes it.
- The rules of a symbol, from [TypeTheoryFormalize]() with `"Meaning" -> "Rules"`, test a condition `x_ /; test` or `x_?test` as [SameQ]() of the [ExpressionEvaluate]() of the test and `True`, which is what the Wolfram Language tests.

## Basic Examples

The value of an expression is an expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeTheoryType[ExpressionEvaluate[Construct[7, 1, 2]], wolfram]
```

<!-- => Expressions -->

---

A condition tests the value:

```wl
positive[x_ /; x > 0] := x;
wolfram = TypeTheoryEnvironment["WolframLanguage"];
Last[TypeTheoryFormalize[positive, wolfram, "Meaning" -> "Rules"]]
```

<!-- => definition DownValues[positive] : Expressions → Option[Expressions] := (expression ∶ Expressions) ↦ MatchFirst[MatchPart[expression, 1, (x ∶ Expressions) ↦ (MatchValue[x] /; ExpressionEvaluate[x > 0] === True)] /; ¬AtomQ[expression] ∧ Decide[Length[Arguments[expression]] == 1]] -->
