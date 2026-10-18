---
Template: Symbol
Name: SubtractionZeroRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtractionZeroRight
Keywords: [subtraction, zero, right, prelude, natural numbers]
SeeAlso: [SubtractionZeroLeft, SubtractionSuccessor, Subtract]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtractionZeroRight]()[*n*]</code> proves <code>*n* - 0 == *n*</code>.

## Details & Options

- [SubtractionZeroRight]() is a theorem of the prelude that holds by computation: [Subtract]() recurses on its second argument.
- `a - b` is read as <code>[Subtract]()[*a*, *b*]</code>.

## Basic Examples

The statement of [SubtractionZeroRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionZeroRight]]
```

<!-- => ∀_n∶ℕ n - 0 == n -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionZeroRight[6]]]
```

<!-- => 6 - 0 == 6 -->
