---
Template: Symbol
Name: RationalDistributivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalDistributivity
Keywords: [rationals, multiplication, addition, distributivity, theorem, Lean]
SeeAlso: [RationalMultiplicationCommutativity, RationalAdditionAssociativity, IntegerDistributivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalDistributivity]()[*x*, *y*, *z*]</code> proves <code>*x* (*y* + *z*) == *x* *y* + *x* *z*</code> for rationals *x*, *y* and *z*.

## Details & Options

- [RationalDistributivity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.mul_add`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalDistributivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalDistributivity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ ∀_z∶ℚ x (y + z) == x y + x z -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalDistributivity[2, 3, 5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 2 (3 + 5) == 2 3 + 2 5 -->
