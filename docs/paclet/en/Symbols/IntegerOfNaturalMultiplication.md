---
Template: Symbol
Name: IntegerOfNaturalMultiplication
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerOfNaturalMultiplication
Keywords: [integers, natural numbers, coercion, multiplication, theorem, Lean]
SeeAlso: [IntegerOfNaturalAddition, IntegerMultiplicationCommutativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerOfNaturalMultiplication]()[*m*, *n*]</code> proves that the integer of <code>*m* *n*</code> is the product of the integers of the natural numbers *m* and *n*.

## Details & Options

- [IntegerOfNaturalMultiplication]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers.
- The natural numbers are integers by the coercion `"integerOfNatural"`, which shows as `↑`; the law says it keeps their products, as Lean's `Nat.cast_mul`.
- It is proved by [QuotientSoundness]() and `"Ring"`: the two sides are classes of pairs with the same difference.

## Basic Examples

The statement of [IntegerOfNaturalMultiplication]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerOfNaturalMultiplication, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ ↑(m n) == ↑m ↑n -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerOfNaturalMultiplication[2, 3], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ↑(2 3) == 2 3 -->
