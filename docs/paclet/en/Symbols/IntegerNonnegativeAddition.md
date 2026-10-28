---
Template: Symbol
Name: IntegerNonnegativeAddition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerNonnegativeAddition
Keywords: [integers, order, addition, nonnegative, sum of squares, theorem, Lean]
SeeAlso: [IntegerSquareNonnegative, IntegerNonnegativeScaling, IntegerLessEqualOfMultiple]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerNonnegativeAddition]()[*hx*, *hy*]</code> proves <code>0 <= *x* + *y*</code> from proofs *hx* of <code>0 <= *x*</code> and *hy* of <code>0 <= *y*</code>, for integers *x* and *y*.

## Details & Options

- [IntegerNonnegativeAddition]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers, as Lean's `add_nonneg`.
- *x* and *y* are implicit arguments, found from the types of *hx* and *hy*.
- `0 <= x` means that `x` is 0 plus a natural number, so the sum is 0 plus the sum of the two natural numbers.

## Basic Examples

The statement of [IntegerNonnegativeAddition]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerNonnegativeAddition, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_{x∶ℤ} ∀_{y∶ℤ} 0 ≤ x ⇒ 0 ≤ y ⇒ 0 ≤ x + y -->

---

A sum of two squares is at least 0:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, 0 <= x x + y y], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Exact", IntegerNonnegativeAddition[IntegerSquareNonnegative[x], IntegerSquareNonnegative[y]]]
}]
```

<!-- => Proof complete -->

## Scope

`"Apply"` finds `x` and `y` from the goal and leaves a goal for each summand:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, 0 <= x x + y y], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", IntegerNonnegativeAddition]
}]
```

<!-- => Proof, 2 goals: x ∶ ℤ, y ∶ ℤ ⊢ 0 ≤ x x; x ∶ ℤ, y ∶ ℤ ⊢ 0 ≤ y y -->

## Applications

The summands can come from hypotheses, here with [IntegerNonnegativeScaling]() for a multiple of one:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, Implies[0 <= x, Implies[0 <= y, 0 <= 2 x + y]]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, hx, hy],
    TypeTheoryTactic["Exact", IntegerNonnegativeAddition[IntegerNonnegativeScaling[2, hx], hy]]
}]
```

<!-- => Proof complete -->

---

A sum of three squares is `(x x + y y) + z z`, so the law nests:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, 0 <= x x + y y + z z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Exact", IntegerNonnegativeAddition[IntegerNonnegativeAddition[IntegerSquareNonnegative[x], IntegerSquareNonnegative[y]], IntegerSquareNonnegative[z]]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"SumOfSquares"` builds such a proof itself:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, 0 <= x x + y y + z z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["SumOfSquares"]
}]
```

<!-- => Proof complete -->
