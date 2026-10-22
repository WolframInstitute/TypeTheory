---
Template: Symbol
Name: RationalLessEqualReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalLessEqualReflexivity
Keywords: [rationals, order, reflexivity, theorem, Lean]
SeeAlso: [RationalAdditionZero, RationalSquareNonnegative, IntegerLessEqualReflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalLessEqualReflexivity]()[*x*]</code> proves <code>*x* <= *x*</code> for a rational *x*.

## Details & Options

- [RationalLessEqualReflexivity]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- `x <= y` means that `y` is `x` plus a rational n / (d + 1) for natural numbers n and d, here 0 / 1, as Lean's `Rat.le_refl`.
- It is proved from [RationalAdditionZero]().

## Basic Examples

The statement of [RationalLessEqualReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalLessEqualReflexivity, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_x∶ℚ x ≤ x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalLessEqualReflexivity[-2/3], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => (-2)/3 ≤ (-2)/3 -->
