---
Template: Symbol
Name: MultiplicationOneRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationOneRight
Keywords: [multiplication, one, right, prelude, natural numbers]
SeeAlso: [MultiplicationOneLeft, MultiplicationZeroRight, AdditionZeroLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationOneRight]()[*n*]</code> proves <code>*n* * 1 == *n*</code>.

## Details & Options

- [MultiplicationOneRight]() is a theorem of the prelude: `n * 1` computes to `0 + n`, and [AdditionZeroLeft]() proves the rest.

## Basic Examples

The statement of [MultiplicationOneRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationOneRight]]
```

<!-- => ∀_n∶ℕ n 1 == n -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, MultiplicationOneRight[n]]]]
```

<!-- => ∀_n∶ℕ n 1 == n -->
