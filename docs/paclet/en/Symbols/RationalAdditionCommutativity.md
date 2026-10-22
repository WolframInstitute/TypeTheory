---
Template: Symbol
Name: RationalAdditionCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalAdditionCommutativity
Keywords: [rationals, addition, commutativity, theorem, Lean]
SeeAlso: [RationalAdditionAssociativity, RationalMultiplicationCommutativity, IntegerAdditionCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalAdditionCommutativity]()[*x*, *y*]</code> proves <code>*x* + *y* == *y* + *x*</code> for rationals *x* and *y*.

## Details & Options

- [RationalAdditionCommutativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.add_comm`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalAdditionCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionCommutativity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ x + y == y + x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionCommutativity[1/2, -3], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 1/2 + -3 == -3 + 1/2 -->
