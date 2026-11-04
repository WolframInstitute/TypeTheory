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

[ExpressionNormal]()[*h*, *s*] is the expression *h* applied to the [Sequence]() *s* of its arguments, *h*[*s*~1~, ...].

## Details & Options

- [ExpressionNormal]() is a constructor of [Expressions](), in [TypeTheoryEnvironment]()["WolframLanguage"].
- [Head]() gives *h*, and [Arguments]() gives *s*.

## Basic Examples

The head of an expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[Head[ExpressionNormal[7, {1, 2}]], wolfram], TypeTheoryTerm[Typed[7, Expressions], wolfram]]
```

<!-- => True -->
