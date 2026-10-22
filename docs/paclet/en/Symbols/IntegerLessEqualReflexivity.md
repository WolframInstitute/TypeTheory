---
Template: Symbol
Name: IntegerLessEqualReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerLessEqualReflexivity
Keywords: [integers, order, reflexivity, theorem, Lean]
SeeAlso: [IntegerAdditionZero, LessEqualReflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerLessEqualReflexivity]()[*x*]</code> proves <code>*x* <= *x*</code> for an integer *x*.

## Details & Options

- [IntegerLessEqualReflexivity]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- `x <= y` means that `y` is `x` plus a natural number, here 0, as Lean's `Int.le_refl`.
- It is proved from [IntegerAdditionZero]().

## Basic Examples

The statement of [IntegerLessEqualReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerLessEqualReflexivity, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x ≤ x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerLessEqualReflexivity[-4], TypeTheoryEnvironment["Integers"]]]
```

<!-- => -4 ≤ -4 -->
