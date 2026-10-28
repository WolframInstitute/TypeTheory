---
Template: Symbol
Name: IntegerAdditionZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerAdditionZero
Keywords: [integers, addition, zero, identity, theorem, Lean]
SeeAlso: [IntegerAdditionNegation, IntegerMultiplicationOne, AdditionZeroRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerAdditionZero]()[*x*]</code> proves <code>*x* + 0 == *x*</code> for an integer *x*.

## Details & Options

- [IntegerAdditionZero]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.add_zero`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerAdditionZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionZero, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x + 0 == x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionZero[-7], TypeTheoryEnvironment["Integers"]]]
```

<!-- => -7 + 0 == -7 -->

## Scope

An instance with a product, `x y`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Integers], Typed[y, Integers]}, IntegerAdditionZero[x y]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x y + 0 == x y -->

## Applications

`"Rewrite"` removes a zero inside a larger term:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x + 0) y == x y], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", IntegerAdditionZero]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Zero on the left follows with [IntegerAdditionCommutativity]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, 0 + x == x], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Rewrite", IntegerAdditionCommutativity],
    TypeTheoryTactic["Exact", IntegerAdditionZero[x]]
}]
```

<!-- => Proof complete -->

## Possible Issues

For an integer variable `x + 0 == x` does not hold by computation, so `"Reflexivity"` does not prove it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers]}, x + 0 == x], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->

For a natural number it does, since addition computes by recursion on its second argument:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n + 0 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->
