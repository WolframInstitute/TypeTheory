---
Template: Symbol
Name: IntegerAdditionNegation
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerAdditionNegation
Keywords: [integers, addition, negation, inverse, theorem, Lean]
SeeAlso: [IntegerAdditionZero, IntegerSubtractionNegation]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerAdditionNegation]()[*x*]</code> proves <code>*x* + -*x* == 0</code> for an integer *x*.

## Details & Options

- [IntegerAdditionNegation]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.add_right_neg`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerAdditionNegation]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionNegation, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x + -x == 0 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionNegation[4], TypeTheoryEnvironment["Integers"]]]
```

<!-- => 4 + -4 == 0 -->
