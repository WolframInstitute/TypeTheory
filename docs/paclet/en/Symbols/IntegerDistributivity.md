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
