---
Template: Symbol
Name: SubtractionSuccessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtractionSuccessor
Keywords: [subtraction, successor, prelude, natural numbers]
SeeAlso: [SubtractionSelf, AdditionSubtractionCancellation, Subtract]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtractionSuccessor]()[*n*, *m*]</code> proves <code>(*n* + 1) - (*m* + 1) == *n* - *m*</code>.

## Details & Options

- [SubtractionSuccessor]() is a theorem of the prelude, proved by induction on *m*.

## Basic Examples

The statement of [SubtractionSuccessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionSuccessor]]
```

<!-- => ∀_n∶ℕ ∀_m∶ℕ (n + 1) - (m + 1) == n - m -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionSuccessor[7, 2]]]
```

<!-- => (7 + 1) - (2 + 1) == 7 - 2 -->
