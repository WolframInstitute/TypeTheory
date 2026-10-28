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

## Scope

An instance with a difference:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[y, Integers]}, IntegerSquareNonnegative[x - y]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ 0 ≤ (x - y) (x - y) -->

## Applications

An integer is at most itself plus a square, by [IntegerLessEqualOfMultiple]() with the square as the sum it needs:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[z, Integers]}, x <= x + z z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, z],
    TypeTheoryTactic["Apply", IntegerLessEqualOfMultiple[0, z z]],
    TypeTheoryTactic["Ring"],
    TypeTheoryTactic["Exact", IntegerSquareNonnegative[z]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"SumOfSquares"` proves inequalities with the law, here `2 x <= x^2 + 1` from the square of `x - 1`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, 2 x <= x^2 + 1], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["SumOfSquares"]
}]
```

<!-- => Proof complete -->

## Possible Issues

`x^2` is a power, not the product `x x`, so `"Exact"` with the law does not prove `0 <= x^2`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, 0 <= x^2], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Exact", IntegerSquareNonnegative[x]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->

`"SumOfSquares"` proves it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, 0 <= x^2], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["SumOfSquares"]
}]
```

<!-- => Proof complete -->
