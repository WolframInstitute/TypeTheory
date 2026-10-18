---
Template: Symbol
Name: AdditionSubtractionCancellation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionSubtractionCancellation
Keywords: [addition, subtraction, cancellation, prelude, natural numbers]
SeeAlso: [SubtractionSelf, SubtractionSuccessor, AdditionCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionSubtractionCancellation]()[*n*, *m*]</code> proves <code>(*n* + *m*) - *m* == *n*</code>.

## Details & Options

- [AdditionSubtractionCancellation]() is a theorem of the prelude, proved by induction on *m* with [SubtractionSuccessor]().

## Basic Examples

The statement of [AdditionSubtractionCancellation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionSubtractionCancellation]]
```

<!-- => ∀_n∶ℕ ∀_m∶ℕ (n + m) - m == n -->

---

For variables:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals]}, AdditionSubtractionCancellation[x, y]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ (x + y) - y == x -->
