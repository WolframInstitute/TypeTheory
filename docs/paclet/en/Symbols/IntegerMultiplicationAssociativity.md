---
Template: Symbol
Name: IntegerMultiplicationAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerMultiplicationAssociativity
Keywords: [integers, multiplication, associativity, theorem, Lean]
SeeAlso: [IntegerMultiplicationCommutativity, IntegerAdditionAssociativity, MultiplicationAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerMultiplicationAssociativity]()[*x*, *y*, *z*]</code> proves <code>(*x* *y*) *z* == *x* (*y* *z*)</code> for integers.

## Details & Options

- [IntegerMultiplicationAssociativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.mul_assoc`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerMultiplicationAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationAssociativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x y z == x (y z) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationAssociativity[2, -1, 3], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 2 (-1) 3 == 2 ((-1) 3) -->

## Scope

An instance with one variable three times:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Integers]}, IntegerMultiplicationAssociativity[x, x, x]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x x x == x (x x) -->

## Applications

`"Rewrite"` regroups a coefficient with the rest of a product:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (2 x) y == 2 (x y)], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", IntegerMultiplicationAssociativity]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"Ring"`, whose proofs are built from this law and the other laws of the integers, regroups products and multiplies their coefficients:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, (2 x) (3 y) == 6 (x y)], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

## Possible Issues

For integer variables the two sides are not equal by computation, so `"Reflexivity"` does not prove the law:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x y) z == x (y z)], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
