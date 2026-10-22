---
Template: Symbol
Name: IntegerSquareNonnegative
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerSquareNonnegative
Keywords: [integers, order, square, nonnegative, sum of squares, theorem, Lean]
SeeAlso: [IntegerNonnegativeAddition, IntegerNonnegativeScaling, IntegerLessEqualOfMultiple, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerSquareNonnegative]()[*z*]</code> proves <code>0 <= *z* *z*</code> for an integer *z*.

## Details & Options

- [IntegerSquareNonnegative]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers, as Lean's `mul_self_nonneg`.
- It is proved by induction on the class of *z*: for the pair (a, b), `a a + b b` is `a b + b a` plus the square of the difference of the larger and the smaller of a and b.
- The tactic `"SumOfSquares"` of [TypeTheoryTactic]() proves that a sum of squares is at least 0 with it.

## Basic Examples

The statement of [IntegerSquareNonnegative]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerSquareNonnegative, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_z∶ℤ 0 ≤ z z -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerSquareNonnegative[2 - 5], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 0 ≤ (2 - 5) (2 - 5) -->
