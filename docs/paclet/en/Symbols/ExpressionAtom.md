---
Template: Symbol
Name: ExpressionAtom
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/ExpressionAtom
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Expressions, Atoms, ExpressionNormal]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[ExpressionAtom]()[*a*] is the expression that is the atom *a*.

## Details & Options

- [ExpressionAtom]() is a constructor of [Expressions](), in [TypeTheoryEnvironment]()["WolframLanguage"].
- The head of [ExpressionAtom]()[*a*] is the atom that the Wolfram Language computes as the head of *a*, and its [Arguments]() are none.

## Basic Examples

An atom has no arguments:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[Arguments[ExpressionAtom["naturalAtom"[3]]], wolfram], TypeTheoryTerm[Typed[{}, Sequence], wolfram]]
```

<!-- => True -->
