---
Template: Symbol
Name: RationalInverseZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalInverseZero
Keywords: [rationals, inverse, zero, division by zero, theorem, Lean]
SeeAlso: [RationalMultiplicationInverse, RationalAdditionZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

[RationalInverseZero]() proves <code>0^-1 == 0</code> for the rationals.

## Details & Options

- [RationalInverseZero]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- The inverse is a function on all rationals, so 0 has one too, 0, as Lean's `Rat.inv_zero`; so does any division by 0. [RationalMultiplicationInverse]() is about the rationals that are not 0.
- It holds by computation, and is proved by `"Reflexivity"`.
- The inverse <code>*x*^-1</code> shows as <code>1/*x*</code>, as <code>[Power]()[*x*, -1]</code> does, so the statement shows as `1/0 == 0`.

## Basic Examples

The statement of [RationalInverseZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalInverseZero, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => 1/0 == 0 -->
