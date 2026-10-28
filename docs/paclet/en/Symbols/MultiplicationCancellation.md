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

## Scope

In a proof, it cancels a factor of 2 from a hypothesis, with *k* equal to 1:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, Implies[2 a == 2 b, a == b]], {
    TypeTheoryTactic["Introduce", a, b, h],
    TypeTheoryTactic["Exact", MultiplicationCancellation[1, a, b, h]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

A factor of 0 makes any two numbers equal, which is why the factor is written `k + 1`:

```wl
TypeTheoryProof[And[0 * 2 == 0 * 5, Not[2 == 5]], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

---

The tactic `"PolynomialReduce"` uses it to cancel the common factor 2:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[2 x == 2 y + 4, x == y + 2]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["PolynomialReduce"]
}]
```

<!-- => Proof complete -->

## Possible Issues

The first argument is *k*, one less than the factor, so a factor of 3 needs 2, and 3 does not check:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Naturals], Typed[b, Naturals], Typed[h, 3 a == 3 b]}, MultiplicationCancellation[3, a, b, h]]]]
```

<!-- => Failure["TypeMismatch", ...] -->
