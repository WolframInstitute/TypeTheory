---
Template: Symbol
Name: MultiplicationCancellation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationCancellation
Keywords: [multiplication, cancellation, prelude, natural numbers]
SeeAlso: [AdditionSubtractionCancellation, MultiplicationCommutativity, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationCancellation]()[*k*, *a*, *b*, *h*]</code> proves <code>*a* == *b*</code> from a proof *h* of <code>(*k* + 1) *a* == (*k* + 1) *b*</code>.

## Details & Options

- [MultiplicationCancellation]() is a theorem of the prelude, proved by induction on *a* and cases on *b*, with [AdditionSubtractionCancellation]() and [SuccessorNotZero]().
- The factor is written `k + 1` so that it is positive: a factor of 0 makes any two numbers equal.
- The tactic `"PolynomialReduce"` of [TypeTheoryTactic]() uses it to clear the common denominator of the cofactors it finds.

## Basic Examples

The statement of [MultiplicationCancellation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationCancellation]]
```

<!-- => ∀_k∶ℕ ∀_a∶ℕ ∀_b∶ℕ (k + 1) a == (k + 1) b ⇒ a == b -->

---

A factor of 3 is 2 + 1 by computation:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Naturals], Typed[b, Naturals], Typed[h, 3 a == 3 b]}, MultiplicationCancellation[2, a, b, h]]]]
```

<!-- => ∀_a∶ℕ ∀_b∶ℕ 3 a == 3 b ⇒ a == b -->
