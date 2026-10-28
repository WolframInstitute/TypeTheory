---
Template: Symbol
Name: IntegerDistributivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerDistributivity
Keywords: [integers, multiplication, addition, distributivity, theorem, Lean]
SeeAlso: [IntegerMultiplicationCommutativity, MultiplicationDistributivityLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerDistributivity]()[*x*, *y*, *z*]</code> proves <code>*x* (*y* + *z*) == *x* *y* + *x* *z*</code> for integers.

## Details & Options

- [IntegerDistributivity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.mul_add`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerDistributivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerDistributivity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x (y + z) == x y + x z -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerDistributivity[2, -1, 3], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 2 (-1 + 3) == 2 (-1) + 2 3 -->

## Scope

An instance with variables:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Integers]}, IntegerDistributivity[x, x, 1]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x (x + 1) == x x + x 1 -->

## Applications

With [IntegerMultiplicationOne](), `"Rewrite"` multiplies out `x (y + 1)`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x (y + 1) == x y + x], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", IntegerDistributivity],
    TypeTheoryTactic["Rewrite", IntegerMultiplicationOne]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"Ring"`, whose proofs are built from this law and the other laws of the integers, multiplies out products of sums:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (x + y) (x - y) == x^2 - y^2], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

## Possible Issues

The law multiplies a sum on the left, so `"Exact"` with it does not prove `(x + y) z == x z + y z`:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x + y) z == x z + y z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Exact", IntegerDistributivity[z, x, y]]
}]
```

<!-- => Failure["TypeMismatch", ...] -->

`"Ring"` proves it:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x + y) z == x z + y z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->
