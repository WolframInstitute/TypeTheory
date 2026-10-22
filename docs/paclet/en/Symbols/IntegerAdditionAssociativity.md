---
Template: Symbol
Name: IntegerAdditionAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerAdditionAssociativity
Keywords: [integers, addition, associativity, theorem, Lean]
SeeAlso: [IntegerAdditionCommutativity, IntegerMultiplicationAssociativity, AdditionAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerAdditionAssociativity]()[*x*, *y*, *z*]</code> proves <code>(*x* + *y*) + *z* == *x* + (*y* + *z*)</code> for integers.

## Details & Options

- [IntegerAdditionAssociativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.add_assoc`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerAdditionAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionAssociativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ ∀_z∶ℤ x + y + z == x + (y + z) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionAssociativity[1, -2, 3], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 1 + -2 + 3 == 1 + (-2 + 3) -->
