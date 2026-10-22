---
Template: Symbol
Name: IntegerMultiplicationOne
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerMultiplicationOne
Keywords: [integers, multiplication, one, identity, theorem, Lean]
SeeAlso: [IntegerAdditionZero, MultiplicationOneRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerMultiplicationOne]()[*x*]</code> proves <code>*x* * 1 == *x*</code> for an integer *x*.

## Details & Options

- [IntegerMultiplicationOne]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- It is a law of the integers as a commutative ring, as Lean's `Int.mul_one`.
- It is proved by `"Induction"` on each integer, a class of pairs of natural numbers, [QuotientSoundness](), which leaves an equation of the pairs, and `"Ring"`, which proves it.

## Basic Examples

The statement of [IntegerMultiplicationOne]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationOne, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_x∶ℤ x 1 == x -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerMultiplicationOne[-7], TypeTheoryEnvironment["Integers"]]]
```

<!-- => (-7) 1 == -7 -->
