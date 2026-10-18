---
Template: Symbol
Name: BooleanTrue
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/BooleanTrue
Keywords: [Boolean, true, Booleans, value, prelude]
SeeAlso: [BooleanFalse, BooleanNot, BooleanAnd, BooleanOr, TrueIntroduction]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[BooleanTrue]() is the Boolean true, a value of [Booleans]().

## Details & Options

- [BooleanTrue]() is the second constructor of [Booleans](), after [BooleanFalse](), as `true` is of Lean's `Bool`.
- [True]() stands for it where a Boolean is expected; elsewhere [True]() is the proposition, which [TrueIntroduction]() proves.
- It shows as `true`.

## Basic Examples

The type of [BooleanTrue]():

```wl
TypeTheoryCheck[TypeTheoryTerm[BooleanTrue]]
```

<!-- => 𝔹 -->

---

[True]() written where a Boolean is expected is [BooleanTrue]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[BooleanTrue], TypeTheoryTerm[Typed[True, Booleans]]]
```

<!-- => True -->
