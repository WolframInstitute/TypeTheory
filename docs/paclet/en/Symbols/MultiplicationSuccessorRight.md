---
Template: Symbol
Name: MultiplicationSuccessorRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationSuccessorRight
Keywords: [multiplication, successor, right, prelude, natural numbers]
SeeAlso: [MultiplicationSuccessorLeft, MultiplicationDistributivityLeft, Times]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationSuccessorRight]()[*m*, *n*]</code> proves <code>*m* * (*n* + 1) == *m* * *n* + *m*</code>.

## Details & Options

- [MultiplicationSuccessorRight]() is a theorem of the prelude that holds by computation: it is how [Times]() is defined.

## Basic Examples

The statement of [MultiplicationSuccessorRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationSuccessorRight]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m (n + 1) == m n + m -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationSuccessorRight[3, 4]]]
```

<!-- => 3 (4 + 1) == 3 × 4 + 3 -->
