---
Template: Symbol
Name: AdditionZeroLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionZeroLeft
Keywords: [addition, zero, left, prelude, natural numbers]
SeeAlso: [AdditionZeroRight, AdditionCommutativity, AdditionSuccessorLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionZeroLeft]()[*n*]</code> proves <code>0 + *n* == *n*</code>.

## Details & Options

- [AdditionZeroLeft]() is a theorem of the prelude, proved by induction on *n* with the recursor of [NonNegativeIntegers](): `0 + n` does not compute to *n* while *n* is a variable.

## Basic Examples

The statement of [AdditionZeroLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionZeroLeft]]
```

<!-- => ∀_n∶ℕ 0 + n == n -->

---

An instance, at a successor:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, AdditionZeroLeft[n + 1]]]]
```

<!-- => ∀_n∶ℕ 0 + (n + 1) == n + 1 -->
