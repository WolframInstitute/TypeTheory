---
Template: Symbol
Name: IntegerLessEqualOfDifference
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerLessEqualOfDifference
Keywords: [integers, order, subtraction, difference, theorem, Lean]
SeeAlso: [IntegerLessEqualOfMultiple, IntegerNonnegativeCancellation, IntegerLessEqualReflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerLessEqualOfDifference]()[*x*, *y*, *h*]</code> proves <code>*x* <= *y*</code> from a proof *h* of <code>0 <= *y* - *x*</code>, for integers *x* and *y*.

## Details & Options

- [IntegerLessEqualOfDifference]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers, as Lean's `sub_nonneg.mp`.
- `y - x` is 0 plus a natural number n, so `y` is `x` plus n.

## Basic Examples

The statement of [IntegerLessEqualOfDifference]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerLessEqualOfDifference, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ 0 ≤ y - x ⇒ x ≤ y -->

---

An inequality from its difference:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[0 <= y - x, x <= y]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["Exact", IntegerLessEqualOfDifference[x, y, h]]
}]
```

<!-- => Proof complete -->
