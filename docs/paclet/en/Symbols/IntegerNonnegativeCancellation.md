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

## Scope

`"Apply"` with `d` and `x` leaves `0 <= (d + 1) x` to prove, with the factor shown as `↑(d + 1)`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, Implies[0 <= 3 x, 0 <= x]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, h],
    TypeTheoryTactic["Apply", IntegerNonnegativeCancellation[2, x]]
}]
```

<!-- => Proof, 1 goal: x ∶ ℤ, h ∶ 0 ≤ 3 x ⊢ 0 ≤ ↑(2 + 1) x -->

`↑(2 + 1)` computes to 3, so the hypothesis proves it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, Implies[0 <= 3 x, 0 <= x]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, h],
    TypeTheoryTactic["Apply", IntegerNonnegativeCancellation[2, x]],
    TypeTheoryTactic["Exact", h]
}]
```

<!-- => Proof complete -->

## Applications

An integer whose double is a square is at least 0, with `"Change"` writing the factor `↑(1 + 1)` as 2 so that `"Rewrite"` finds the left side of the hypothesis:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[2 x == y y, 0 <= x]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["Apply", IntegerNonnegativeCancellation[1, x]],
    TypeTheoryTactic["Change", 0 <= 2 x],
    TypeTheoryTactic["Rewrite", h],
    TypeTheoryTactic["Exact", IntegerSquareNonnegative[y]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

[IntegerNonnegativeScaling]() goes the other way, so a positive factor can be traded for another:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, Implies[0 <= 2 x, 0 <= 5 x]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, h],
    TypeTheoryTactic["Exact", IntegerNonnegativeScaling[5, IntegerNonnegativeCancellation[1, x, h]]]
}]
```

<!-- => Proof complete -->
