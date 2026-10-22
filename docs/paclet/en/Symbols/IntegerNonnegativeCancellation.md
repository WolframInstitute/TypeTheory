---
Template: Symbol
Name: IntegerNonnegativeCancellation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerNonnegativeCancellation
Keywords: [integers, order, multiplication, cancellation, nonnegative, theorem, Lean]
SeeAlso: [IntegerNonnegativeScaling, IntegerLessEqualOfMultiple, IntegerLessEqualOfDifference]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerNonnegativeCancellation]()[*d*, *x*, *h*]</code> proves <code>0 <= *x*</code> from a proof *h* of <code>0 <= (*d* + 1) *x*</code>, for a natural number *d* and an integer *x*.

## Details & Options

- [IntegerNonnegativeCancellation]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers, as Lean's `nonneg_of_mul_nonneg_right`.
- The factor is `d + 1`, a positive natural number whatever `d` is.
- It is proved by induction on the class of *x*: for the pair (a, b), a positive multiple of the class is at least 0 only where `b <= a`.

## Basic Examples

The statement of [IntegerNonnegativeCancellation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerNonnegativeCancellation, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_d∶ℕ ∀_x∶ℤ 0 ≤ ↑(d + 1) x ⇒ 0 ≤ x -->

---

From `0 <= 2 x`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, Implies[0 <= 2 x, 0 <= x]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, h],
    TypeTheoryTactic["Exact", IntegerNonnegativeCancellation[1, x, h]]
}]
```

<!-- => Proof complete -->
