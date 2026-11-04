---
Template: Symbol
Name: Atoms
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Atoms
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Expressions, ExpressionAtom, TypeTheoryEnvironment]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[Atoms]() is the type of the expressions of the Wolfram Language that have no parts: symbols, numbers and strings.

## Details & Options

- [Atoms]() is a constant of [TypeTheoryEnvironment]()["WolframLanguage"], an axiom: the atoms are opaque to the kernel.
- [ExpressionAtom]() makes an expression of an atom, and a natural number is an expression where one is expected, by a coercion.
- The head of an atom is an axiom that the Wolfram Language computes, [Head]().

## Basic Examples

An atom is an expression:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeOf[TypeTheoryTerm[ExpressionAtom, wolfram]]
```

<!-- => Atoms → Expressions -->
