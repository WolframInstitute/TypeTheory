---
Template: Symbol
Name: IntegerSubtractionNegation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerSubtractionNegation
Keywords: [integers, subtraction, negation, theorem, Lean]
SeeAlso: [IntegerAdditionNegation, IntegerAdditionZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerSubtractionNegation]()[*x*, *y*]</code> proves <code>*x* - *y* == *x* + -*y*</code> for integers *x* and *y*.

## Details & Options

- [IntegerSubtractionNegation]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- `x - y` is defined as `x + -y`, so the law holds by computation, as Lean's `Int.sub_eq_add_neg`. `"Rewrite"` with it turns a difference into a sum, to which the laws of addition apply.
- It is proved by `"Reflexivity"`.

## Basic Examples

The statement of [IntegerSubtractionNegation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerSubtractionNegation, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ ∀_y∶ℤ x - y == x + -y -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerSubtractionNegation[2, 5], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 2 - 5 == 2 + -5 -->
