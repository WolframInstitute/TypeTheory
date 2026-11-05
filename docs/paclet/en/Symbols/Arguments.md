---
Template: Symbol
Name: Arguments
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Arguments
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Expressions, MatchBind]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[Arguments]()[*e*] is the list of the arguments of the expression *e*, {} for an atom.

## Details & Options

- [Arguments]() is a definition of [TypeTheoryEnvironment]()["WolframLanguage"], by the recursor of [Expressions](), which the kernel computes.
- Its type is `Expressions -> {Expressions}`.

## Basic Examples

The arguments of an expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
DefinitionallyEqualQ[TypeTheoryTerm[Arguments["construct"[7, 1, 2]], wolfram], TypeTheoryTerm[Typed[{1, 2}, {Expressions}], wolfram]]
```

<!-- => True -->
