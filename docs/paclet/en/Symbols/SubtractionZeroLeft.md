---
Template: Symbol
Name: SubtractionZeroLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtractionZeroLeft
Keywords: [subtraction, zero, left, prelude, natural numbers]
SeeAlso: [SubtractionZeroRight, SubtractionSelf, Subtract]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtractionZeroLeft]()[*n*]</code> proves <code>0 - *n* == 0</code>: subtraction of natural numbers stops at `0`.

## Details & Options

- [SubtractionZeroLeft]() is a theorem of the prelude, proved by induction on *n*.

## Basic Examples

The statement of [SubtractionZeroLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionZeroLeft]]
```

<!-- => ∀_n∶ℕ 0 - n == 0 -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, SubtractionZeroLeft[n]]]]
```

<!-- => ∀_n∶ℕ 0 - n == 0 -->
