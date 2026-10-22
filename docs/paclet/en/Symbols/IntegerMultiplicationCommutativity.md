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
