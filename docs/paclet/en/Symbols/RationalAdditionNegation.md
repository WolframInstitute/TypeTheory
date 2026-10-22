---
Template: Symbol
Name: RationalAdditionNegation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalAdditionNegation
Keywords: [rationals, addition, negation, inverse, theorem, Lean]
SeeAlso: [RationalAdditionZero, RationalSubtractionNegation, IntegerAdditionNegation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalAdditionNegation]()[*x*]</code> proves <code>*x* + -*x* == 0</code> for a rational *x*.

## Details & Options

- [RationalAdditionNegation]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- It is a law of the rationals as a commutative ring, as Mathlib's `add_neg_cancel`.
- It is proved by `"Induction"` on each rational, a class of pairs of an integer and a natural number, [QuotientSoundness](), which leaves an equation of integers of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [RationalAdditionNegation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionNegation, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x + -x == 0 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalAdditionNegation[3/4], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 3/4 + -(3/4) == 0 -->
