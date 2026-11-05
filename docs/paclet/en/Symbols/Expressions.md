---
Template: Symbol
Name: Expressions
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Expressions
Keywords: [Wolfram Language, expressions, pattern matching, Match]
SeeAlso: [Atoms, Arguments]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheWolframLanguage]
---

## Usage

[Expressions]() is the type of the expressions of the Wolfram Language: an atom, `"atom"`[*a*], or a head applied to its arguments, `"construct"`[*h*, *a*, *b*, ...], as [Construct]() builds one.

## Details & Options

- [Expressions]() is an inductive type of [TypeTheoryEnvironment]()["WolframLanguage"], nested: `"construct"` keeps the arguments of an expression as their list, which a variable of the type `{Expressions}` among them joins.
- Where an expression is expected, a term evaluates as in the Wolfram Language: a symbol that names nothing stands for itself, a head that names nothing applied to arguments is that expression, `{a, b}` is the expression `List[a, b]`, and a natural number or a string is its atom, by a coercion; a constant computes, and [HoldForm]() keeps it from computing.
- [TypeTheoryFormalize]() types a built-in it has no precise signature for over [Expressions]().

## Basic Examples

An expression with head 7 and arguments 1 and 2:

```wl
wolfram = TypeTheoryEnvironment["WolframLanguage"];
TypeTheoryType["construct"[7, 1, 2], wolfram]
```

<!-- => Expressions -->
