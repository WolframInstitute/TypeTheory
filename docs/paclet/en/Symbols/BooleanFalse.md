---
Template: Symbol
Name: BooleanFalse
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/BooleanFalse
Keywords: [Boolean, false, Booleans, value, prelude]
SeeAlso: [BooleanTrue, BooleanNot, BooleanAnd, BooleanOr, FalseElimination]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[BooleanFalse]() is the Boolean false, a value of [Booleans]().

## Details & Options

- [BooleanFalse]() is the first constructor of [Booleans](), as `false` is of Lean's `Bool`, so the recursor of [Booleans]() takes the case for it first.
- [False]() stands for it where a Boolean is expected; elsewhere [False]() is the proposition with no proof.
- It shows as `false`.

## Basic Examples

The type of [BooleanFalse]():

```wl
TypeTheoryCheck[TypeTheoryTerm[BooleanFalse]]
```

<!-- => 𝔹 -->

---

The negation of true:

```wl
WeakHeadNormalForm[TypeTheoryTerm[Typed[Not[True], Booleans]]]
```

<!-- => false -->
