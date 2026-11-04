---
Template: Symbol
Name: ExpressionNormal
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ExpressionNormal
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Expressions, ExpressionAtom, Arguments]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[ExpressionNormal]()[*h*, {*a*~1~, *a*~2~, ...}] is the expression *h*[*a*~1~, *a*~2~, ...], *h* applied to the list of its arguments.

## Details & Options

- [ExpressionNormal]() is a constructor of [Expressions](), in [TypeTheoryEnvironment]()["WolframLanguage"], of type `Expressions -> {Expressions} -> Expressions`.
- [Head]() gives *h*, and [Arguments]() gives the list of the arguments.
- An expression is written and shown as the Wolfram Language holds it, `HoldForm[h[a, b]]`, where its atoms are declared; [ExpressionNormal]() is what it stands for.
- The curried expression *h*[*a*][*b*] is [ExpressionNormal]()[[ExpressionNormal]()[*h*, {*a*}], {*b*}], another expression than *h*[*a*, *b*].

## Basic Examples

The head of an expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[Head[ExpressionNormal[7, {1, 2}]], wolfram], TypeTheoryTerm[Typed[7, Expressions], wolfram]]
```

<!-- => True -->

## Scope

The curried expression is another expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[ExpressionNormal[ExpressionNormal[7, {1}], {2}], wolfram], TypeTheoryTerm[ExpressionNormal[7, {1, 2}], wolfram]]
```

<!-- => False -->
