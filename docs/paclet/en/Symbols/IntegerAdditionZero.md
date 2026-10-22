---
Template: Symbol
Name: IntegerAdditionZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerAdditionZero
Keywords: [integers, addition, zero, identity, theorem, Lean]
SeeAlso: [IntegerAdditionNegation, IntegerMultiplicationOne, AdditionZeroRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerAdditionZero]()[*x*]</code> proves <code>*x* + 0 == *x*</code> for an integer *x*.

## Details & Options

- [IntegerAdditionZero]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.add_zero`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerAdditionZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionZero, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x + 0 == x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerAdditionZero[-7], TypeTheoryEnvironment["Integers"]]]
```

<!-- => -7 + 0 == -7 -->
