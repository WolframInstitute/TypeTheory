---
Template: Symbol
Name: RationalOfIntegerAddition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalOfIntegerAddition
Keywords: [rationals, integers, coercion, addition, theorem, Lean]
SeeAlso: [RationalOfIntegerMultiplication, IntegerOfNaturalAddition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalOfIntegerAddition]()[*a*, *b*]</code> proves that the rational of <code>*a* + *b*</code> is the sum of the rationals of the integers *a* and *b*.

## Details & Options

- [RationalOfIntegerAddition]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- The integers are rationals by the coercion `"rationalOfInteger"`, which shows as `↑`; the law says it keeps their sums, as Mathlib's `Int.cast_add`.
- It is proved by [QuotientSoundness]() and `"Ring"`: the two sides are classes of pairs whose relation is an identity of the integers.

## Basic Examples

The statement of [RationalOfIntegerAddition]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalOfIntegerAddition, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ ∀_b∶ℤ ↑(a + b) == ↑a + ↑b -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalOfIntegerAddition[2, -5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ↑(2 + -5) == 2 + -5 -->
