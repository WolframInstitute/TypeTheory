---
Template: Symbol
Name: IntegerLessEqualOfMultiple
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerLessEqualOfMultiple
Keywords: [integers, order, inequality, sum of squares, certificate, theorem, Lean]
SeeAlso: [IntegerLessEqualOfDifference, IntegerNonnegativeCancellation, IntegerSquareNonnegative, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerLessEqualOfMultiple]()[*d*, *s*, *e*, *h*]</code> proves <code>*x* <= *y*</code> from a proof *e* of <code>(*d* + 1) (*y* - *x*) == *s*</code> and a proof *h* of <code>0 <= *s*</code>, for a natural number *d* and integers *x*, *y* and *s*.

## Details & Options

- [IntegerLessEqualOfMultiple]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- *x* and *y* are implicit arguments, found from the goal or from the type of *e*.
- The tactic `"SumOfSquares"` of [TypeTheoryTactic]() proves an inequality with it: Wolfram finds *d* and a sum of squares *s*, `"Ring"` proves the equation *e*, and [IntegerSquareNonnegative](), [IntegerNonnegativeScaling]() and [IntegerNonnegativeAddition]() prove *h*.
- It is proved from [IntegerNonnegativeCancellation]() and [IntegerLessEqualOfDifference]().

## Basic Examples

The statement of [IntegerLessEqualOfMultiple]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerLessEqualOfMultiple, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_d∶ℕ ∀_{x∶ℤ} ∀_{y∶ℤ} ∀_s∶ℤ ↑(d + 1) (y - x) == s ⇒ 0 ≤ s ⇒ x ≤ y -->

---

`2 x y <= x x + y y`, since `x x + y y - 2 x y` is the square of `x - y`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, 2 x y <= x x + y y], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", IntegerLessEqualOfMultiple[0, (x - y) (x - y)]],
    TypeTheoryTactic["Ring"],
    TypeTheoryTactic["Exact", IntegerSquareNonnegative[x - y]]
}]
```

<!-- => Proof complete -->
