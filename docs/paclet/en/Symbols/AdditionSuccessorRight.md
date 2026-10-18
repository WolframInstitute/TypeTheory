---
Template: Symbol
Name: AdditionSuccessorRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionSuccessorRight
Keywords: [addition, successor, right, prelude, natural numbers]
SeeAlso: [AdditionSuccessorLeft, AdditionAssociativity, AdditionZeroRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionSuccessorRight]()[*m*, *n*]</code> proves <code>*m* + (*n* + 1) == *m* + *n* + 1</code>.

## Details & Options

- [AdditionSuccessorRight]() is a theorem of the prelude that holds by computation: [Plus]() recurses on its second argument.

## Basic Examples

The statement of [AdditionSuccessorRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionSuccessorRight]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + (n + 1) == (m + n) + 1 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionSuccessorRight[2, 3]]]
```

<!-- => 2 + (3 + 1) == (2 + 3) + 1 -->
