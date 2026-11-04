---
Template: Symbol
Name: Expressions
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Expressions
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Atoms, ExpressionAtom, ExpressionNormal, Arguments]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[Expressions]() is the type of the expressions of the Wolfram Language: an atom, [ExpressionAtom]()[*a*], or a head applied to the [Sequence]() of its arguments, [ExpressionNormal]()[*h*, *s*].

## Details & Options

- [Expressions]() is an inductive type of [TypeTheoryEnvironment]()["WolframLanguage"], nested: the arguments of an expression are a list of expressions, its [Sequence]().
- A natural number is an expression where one is expected, by a coercion.
- [TypeTheoryFormalize]() types a built-in it has no precise signature for over [Expressions]().

## Basic Examples

An expression with head 7 and arguments 1 and 2:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeOf[TypeTheoryTerm[ExpressionNormal[7, {1, 2}], wolfram]]
```

<!-- => Expressions -->
