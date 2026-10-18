---
Template: Symbol
Name: MultiplicationZeroLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationZeroLeft
Keywords: [multiplication, zero, left, prelude, natural numbers]
SeeAlso: [MultiplicationZeroRight, MultiplicationCommutativity, AdditionZeroLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationZeroLeft]()[*n*]</code> proves <code>0 * *n* == 0</code>.

## Details & Options

- [MultiplicationZeroLeft]() is a theorem of the prelude, proved by induction on *n*.

## Basic Examples

The statement of [MultiplicationZeroLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationZeroLeft]]
```

<!-- => ∀_n∶ℕ 0 n == 0 -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, MultiplicationZeroLeft[n]]]]
```

<!-- => ∀_n∶ℕ 0 n == 0 -->
