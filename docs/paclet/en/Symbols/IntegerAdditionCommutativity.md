---
Template: Symbol
Name: IntegerAdditionCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerAdditionCommutativity
Keywords: [integers, addition, commutativity, theorem, Lean]
SeeAlso: [IntegerAdditionAssociativity, IntegerMultiplicationCommutativity, AdditionCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerAdditionCommutativity]()[*x*, *y*]</code> proves <code>*x* + *y* == *y* + *x*</code> for integers *x* and *y*.

## Details & Options

- [IntegerAdditionCommutativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.add_comm`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerAdditionCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionCommutativity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x + y == y + x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionCommutativity[-2, 5], TypeTheoryEnvironment["Integers"]]]
```

<!-- => -2 + 5 == 5 + -2 -->
