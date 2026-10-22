---
Template: Symbol
Name: RationalMultiplicationOne
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalMultiplicationOne
Keywords: [rationals, multiplication, one, identity, theorem, Lean]
SeeAlso: [RationalAdditionZero, RationalMultiplicationInverse, IntegerMultiplicationOne]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalMultiplicationOne]()[*x*]</code> proves <code>*x* * 1 == *x*</code> for a rational *x*.

## Details & Options

- [RationalMultiplicationOne]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Lean's `Rat.mul_one`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalMultiplicationOne]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationOne, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x 1 == x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalMultiplicationOne[7], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 7 1 == 7 -->
