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
