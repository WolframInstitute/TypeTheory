---
Template: Symbol
Name: RationalSubtractionNegation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalSubtractionNegation
Keywords: [rationals, subtraction, negation, theorem, Lean]
SeeAlso: [RationalAdditionNegation, RationalAdditionZero, IntegerSubtractionNegation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalSubtractionNegation]()[*x*, *y*]</code> proves <code>*x* - *y* == *x* + -*y*</code> for rationals *x* and *y*.

## Details & Options

- [RationalSubtractionNegation]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- `x - y` is defined as `x + -y`, so the law holds by computation, as Lean's `Rat.sub_eq_add_neg`. `"Rewrite"` with it turns a difference into a sum, to which the laws of addition apply.
- It is proved by `"Reflexivity"`.

## Basic Examples

The statement of [RationalSubtractionNegation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalSubtractionNegation, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ ∀_y∶ℚ x - y == x + -y -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalSubtractionNegation[1/2, 1/3], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 1/2 - 1/3 == 1/2 + -(1/3) -->
