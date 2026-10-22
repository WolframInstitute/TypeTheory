---
Template: Symbol
Name: RationalMultiplicationCommutativity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalMultiplicationCommutativity
Keywords: [rationals, multiplication, commutativity, theorem, Lean]
SeeAlso: [RationalMultiplicationAssociativity, RationalAdditionCommutativity, IntegerMultiplicationCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalMultiplicationCommutativity]()[*x*, *y*]</code> proves <code>*x* *y* == *y* *x*</code> for rationals *x* and *y*.

## Details & Options

- [RationalMultiplicationCommutativity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.mul_comm`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalMultiplicationCommutativity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationCommutativity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ x y == y x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationCommutativity[2/3, 5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 2 5/3 == 5 2/3 -->
