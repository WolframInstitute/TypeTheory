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

## Scope

`"Apply"` turns an inequality into the statement that the difference of its sides is at least 0:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x <= x + y y], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", IntegerLessEqualOfDifference]
}]
```

<!-- => Proof, 1 goal: x ∶ ℤ, y ∶ ℤ ⊢ 0 ≤ (x + y y) - x -->

## Applications

An inequality whose difference is a square, given by a hypothesis:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, Implies[y - x == z z, x <= y]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z, h],
    TypeTheoryTactic["Apply", IntegerLessEqualOfDifference],
    TypeTheoryTactic["Rewrite", h],
    TypeTheoryTactic["Exact", IntegerSquareNonnegative[z]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`x <= y` means that `y` is `x` plus a natural number, so where that number is at hand, [ExistsIntroduction]() proves the inequality directly:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x <= x + 3], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Exact", ExistsIntroduction[3, EqualityReflexivity[x + 3]]]
}]
```

<!-- => Proof complete -->

## Possible Issues

`"Ring"` proves equations only, so it does not finish the difference that `"Apply"` leaves:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x <= x + y y], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", IntegerLessEqualOfDifference],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Failure["EquationExpected", ...] -->

`"SumOfSquares"` does:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x <= x + y y], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", IntegerLessEqualOfDifference],
    TypeTheoryTactic["SumOfSquares"]
}]
```

<!-- => Proof complete -->
