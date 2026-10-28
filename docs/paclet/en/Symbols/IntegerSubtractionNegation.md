---
Template: Symbol
Name: IntegerSubtractionNegation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerSubtractionNegation
Keywords: [integers, subtraction, negation, theorem, Lean]
SeeAlso: [IntegerAdditionNegation, IntegerAdditionZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerSubtractionNegation]()[*x*, *y*]</code> proves <code>*x* - *y* == *x* + -*y*</code> for integers *x* and *y*.

## Details & Options

- [IntegerSubtractionNegation]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- `x - y` is defined as `x + -y`, so the law holds by computation, as Lean's `Int.sub_eq_add_neg`. `"Rewrite"` with it turns a difference into a sum, to which the laws of addition apply.
- It is proved by `"Reflexivity"`.

## Basic Examples

The statement of [IntegerSubtractionNegation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerSubtractionNegation, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x - y == x + -y -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerSubtractionNegation[2, 5], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 2 - 5 == 2 + -5 -->

## Scope

On natural numbers the law is about the difference of their integers:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, IntegerSubtractionNegation[m, n]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ ↑m - ↑n == ↑m + -(↑n) -->

## Applications

`"Rewrite"` with the law turns a difference into a sum, and the laws of addition then prove `(x - y) + y == x`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x - y) + y == x], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", IntegerSubtractionNegation],
    TypeTheoryTactic["Rewrite", IntegerAdditionAssociativity],
    TypeTheoryTactic["Rewrite", IntegerAdditionCommutativity[-y, y]],
    TypeTheoryTactic["Rewrite", IntegerAdditionNegation],
    TypeTheoryTactic["Rewrite", IntegerAdditionZero]
}]
```

<!-- => Proof complete -->

## Properties and Relations

A difference of natural numbers stops at 0:

```wl
WeakHeadNormalForm[TypeTheoryTerm[2 - 5, TypeTheoryEnvironment["Integers"]]]
```

<!-- => 0 -->

The difference of their integers, a sum with a negation, does not, and `"Decide"` proves it equal to -3:

```wl
TypeTheoryProof[Typed[2 - 5, Integers] == -3, TypeTheoryEnvironment["Integers"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

Wolfram Language reads `x + -y` as `x - y`, so a statement of the law written that way has the same two sides:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x - y == x + -y], TypeTheoryEnvironment["Integers"]]
```

<!-- => Proof, 1 goal: ⊢ ∀_x∶ℤ ∀_y∶ℤ x - y == x - y -->

Wrapping the negation in [Typed]() keeps it a negation, and `"Reflexivity"` proves the law, which holds by computation:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x - y == x + Typed[-y, Integers]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->
