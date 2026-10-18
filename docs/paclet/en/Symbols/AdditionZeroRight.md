---
Template: Symbol
Name: AdditionZeroRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionZeroRight
Keywords: [addition, zero, right, prelude, natural numbers]
SeeAlso: [AdditionZeroLeft, AdditionCommutativity, MultiplicationOneRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionZeroRight]()[*n*]</code> proves <code>*n* + 0 == *n*</code>.

## Details & Options

- [AdditionZeroRight]() is a theorem of the prelude. It holds by computation, since [Plus]() recurses on its second argument: its proof is <code>[EqualityReflexivity]()[*n*]</code>.

## Basic Examples

The statement of [AdditionZeroRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionZeroRight]]
```

<!-- => ∀_n∶ℕ n + 0 == n -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionZeroRight[7]]]
```

<!-- => 7 + 0 == 7 -->
