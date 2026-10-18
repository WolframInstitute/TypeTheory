---
Template: Symbol
Name: SubtractionSelf
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtractionSelf
Keywords: [subtraction, self, prelude, natural numbers]
SeeAlso: [SubtractionSuccessor, SubtractionZeroLeft, AdditionSubtractionCancellation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtractionSelf]()[*n*]</code> proves <code>*n* - *n* == 0</code>.

## Details & Options

- [SubtractionSelf]() is a theorem of the prelude, proved by induction on *n* with [SubtractionSuccessor]().

## Basic Examples

The statement of [SubtractionSelf]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionSelf]]
```

<!-- => ∀_n∶ℕ n - n == 0 -->

---

For a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, NonNegativeIntegers]}, SubtractionSelf[n]]]]
```

<!-- => ∀_n∶ℕ n - n == 0 -->
