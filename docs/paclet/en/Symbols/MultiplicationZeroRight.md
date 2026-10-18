---
Template: Symbol
Name: MultiplicationZeroRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationZeroRight
Keywords: [multiplication, zero, right, prelude, natural numbers]
SeeAlso: [MultiplicationZeroLeft, MultiplicationOneRight, Times]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationZeroRight]()[*n*]</code> proves <code>*n* * 0 == 0</code>.

## Details & Options

- [MultiplicationZeroRight]() is a theorem of the prelude that holds by computation: [Times]() recurses on its second argument.

## Basic Examples

The statement of [MultiplicationZeroRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationZeroRight]]
```

<!-- => ∀_n∶ℕ n 0 == 0 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationZeroRight[9]]]
```

<!-- => 9 × 0 == 0 -->
