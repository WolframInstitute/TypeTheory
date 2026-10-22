---
Template: Symbol
Name: RationalMultiplicationAssociativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalMultiplicationAssociativity
Keywords: [rationals, multiplication, associativity, theorem, Lean]
SeeAlso: [RationalMultiplicationCommutativity, RationalAdditionAssociativity, IntegerMultiplicationAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalMultiplicationAssociativity]()[*x*, *y*, *z*]</code> proves <code>(*x* *y*) *z* == *x* (*y* *z*)</code> for rationals *x*, *y* and *z*.

## Details & Options

- [RationalMultiplicationAssociativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.mul_assoc`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalMultiplicationAssociativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationAssociativity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ ∀_z∶ℚ x y z == x (y z) -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationAssociativity[2, 3, 5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 2 3 5 == 2 (3 5) -->
