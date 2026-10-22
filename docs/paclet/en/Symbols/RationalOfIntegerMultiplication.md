---
Template: Symbol
Name: RationalOfIntegerMultiplication
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalOfIntegerMultiplication
Keywords: [rationals, integers, coercion, multiplication, theorem, Lean]
SeeAlso: [RationalOfIntegerAddition, IntegerOfNaturalMultiplication]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalOfIntegerMultiplication]()[*a*, *b*]</code> proves that the rational of <code>*a* *b*</code> is the product of the rationals of the integers *a* and *b*.

## Details & Options

- [RationalOfIntegerMultiplication]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- The integers are rationals by the coercion `"rationalOfInteger"`, which shows as `↑`; the law says it keeps their products, as Mathlib's `Int.cast_mul`.
- It is proved by [QuotientSoundness]() and `"Ring"`.

## Basic Examples

The statement of [RationalOfIntegerMultiplication]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalOfIntegerMultiplication, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ ∀_b∶ℤ ↑(a b) == ↑a ↑b -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalOfIntegerMultiplication[2, -5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ↑(2 (-5)) == 2 (-5) -->
