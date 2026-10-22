---
Template: Symbol
Name: RationalAdditionAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalAdditionAssociativity
Keywords: [rationals, addition, associativity, theorem, Lean]
SeeAlso: [RationalAdditionCommutativity, RationalMultiplicationAssociativity, IntegerAdditionAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalAdditionAssociativity]()[*x*, *y*, *z*]</code> proves <code>(*x* + *y*) + *z* == *x* + (*y* + *z*)</code> for rationals *x*, *y* and *z*.

## Details & Options

- [RationalAdditionAssociativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.add_assoc`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalAdditionAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionAssociativity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ ∀_z∶ℚ x + y + z == x + (y + z) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionAssociativity[1/2, 1/3, 1/6], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 1/2 + 1/3 + 1/6 == 1/2 + (1/3 + 1/6) -->
