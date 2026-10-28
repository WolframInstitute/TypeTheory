---
Template: Symbol
Name: IntegerMultiplicationCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerMultiplicationCommutativity
Keywords: [integers, multiplication, commutativity, theorem, Lean]
SeeAlso: [IntegerMultiplicationAssociativity, IntegerAdditionCommutativity, MultiplicationCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerMultiplicationCommutativity]()[*x*, *y*]</code> proves <code>*x* *y* == *y* *x*</code> for integers *x* and *y*.

## Details & Options

- [IntegerMultiplicationCommutativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.mul_comm`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerMultiplicationCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationCommutativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x y == y x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationCommutativity[-2, 5], TypeTheoryEnvironment["Integers"]]]
```

<!-- => (-2) 5 == 5 (-2) -->

## Scope

A natural number factor is coerced to an integer:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals], Typed[x, Integers]}, IntegerMultiplicationCommutativity[n, x]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_n∶ℕ ∀_x∶ℤ ↑n x == x ↑n -->

## Applications

With [IntegerDistributivity](), which multiplies a sum on the left, the law multiplies a sum on the right:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers], Typed[z, Integers]}, (x + y) z == x z + y z], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y, z],
    TypeTheoryTactic["Rewrite", IntegerMultiplicationCommutativity[x + y, z]],
    TypeTheoryTactic["Rewrite", IntegerDistributivity],
    TypeTheoryTactic["Rewrite", IntegerMultiplicationCommutativity[z, x]],
    TypeTheoryTactic["Rewrite", IntegerMultiplicationCommutativity[z, y]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

An instance of literals is decided by `"Decide"`, since [IntegerEqualityDecidable]() decides equations of integers:

```wl
TypeTheoryProof[Typed[(-2) 5, Integers] == 5 (-2), TypeTheoryEnvironment["Integers"], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->

## Possible Issues

For integer variables the two sides are not equal by computation, so `"Reflexivity"` does not prove the law:

```wl
TypeTheoryProof[ForAll[{Typed[x, Integers], Typed[y, Integers]}, x y == y x], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
