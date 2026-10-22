---
Template: Symbol
Name: IntegerOfNaturalAddition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerOfNaturalAddition
Keywords: [integers, natural numbers, coercion, addition, theorem, Lean]
SeeAlso: [IntegerOfNaturalMultiplication, IntegerAdditionCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerOfNaturalAddition]()[*m*, *n*]</code> proves that the integer of <code>*m* + *n*</code> is the sum of the integers of the natural numbers *m* and *n*.

## Details & Options

- [IntegerOfNaturalAddition]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- The natural numbers are integers by the coercion `"integerOfNatural"`, which shows as `↑`; the law says it keeps their sums, as Lean's `Nat.cast_add`.
- It is proved by [QuotientSoundness]() and `"Ring"`: the two sides are classes of pairs with the same difference.

## Basic Examples

The statement of [IntegerOfNaturalAddition]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerOfNaturalAddition, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ ↑(m + n) == ↑m + ↑n -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerOfNaturalAddition[2, 3], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ↑(2 + 3) == 2 + 3 -->
