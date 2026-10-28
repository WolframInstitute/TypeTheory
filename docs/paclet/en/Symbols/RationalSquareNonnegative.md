---
Template: Symbol
Name: RationalSquareNonnegative
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalSquareNonnegative
Keywords: [rationals, order, square, nonnegative, theorem, Lean]
SeeAlso: [IntegerSquareNonnegative, RationalLessEqualReflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalSquareNonnegative]()[*x*]</code> proves <code>0 <= *x* *x*</code> for a rational *x*.

## Details & Options

- [RationalSquareNonnegative]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals, as Mathlib's `mul_self_nonneg`.
- It is proved by induction on the class of *x*: the square of the class of (a, b) is that of (a a, b b + b + b), and a a is a natural number by [IntegerSquareNonnegative]().

## Basic Examples

The statement of [RationalSquareNonnegative]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalSquareNonnegative, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ 0 ≤ x x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalSquareNonnegative[-1/2], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 0 ≤ (-(1/2)) (-(1/2)) -->

## Scope

An instance with a difference:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Rationals]}, RationalSquareNonnegative[x - 1/2]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ 0 ≤ (x - 1/2) (x - 1/2) -->

---

An integer is coerced to a rational:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Integers]}, RationalSquareNonnegative[a]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ 0 ≤ ↑a ↑a -->

## Properties and Relations

[IntegerSquareNonnegative](), which the law is proved from, states the same of an integer itself:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Integers]}, IntegerSquareNonnegative[a]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ 0 ≤ a a -->

## Possible Issues

`x^2` is a power, not the product `x x`, so `"Exact"` with the law does not prove `0 <= x^2`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, 0 <= x^2], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Exact", RationalSquareNonnegative[x]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->

`"SumOfSquares"` proves inequalities of integers and natural numbers only:

```wl
TypeTheoryProof[ForAll[{Typed[x, Rationals]}, 0 <= x^2], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["SumOfSquares"]
}]
```

<!-- => Failure["InequalityExpected", ...] -->
