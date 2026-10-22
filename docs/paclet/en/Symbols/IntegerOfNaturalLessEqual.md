---
Template: Symbol
Name: IntegerOfNaturalLessEqual
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IntegerOfNaturalLessEqual
Keywords: [integers, natural numbers, coercion, order, theorem, Lean]
SeeAlso: [IntegerOfNaturalAddition, IntegerOfNaturalMultiplication, IntegerLessEqualOfMultiple]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheIntegers]
---

## Usage

<code>[IntegerOfNaturalLessEqual]()[*m*, *n*, *h*]</code> proves <code>*m* <= *n*</code> for natural numbers *m* and *n* from a proof *h* of <code>*m* <= *n*</code> of their integers.

## Details & Options

- [IntegerOfNaturalLessEqual]() is a theorem of <code>[TypeTheoryEnvironment]()["Integers"]</code>, the prelude with the integers, as Lean's `Int.ofNat_le.mp`.
- The natural numbers are integers by the coercion `"integerOfNatural"`, which shows as `↑`.
- The tactic `"SumOfSquares"` of [TypeTheoryTactic]() proves an inequality of natural numbers with it, as the inequality of their integers.

## Basic Examples

The statement of [IntegerOfNaturalLessEqual]():

```wl
TypeTheoryCheck[TypeTheoryTerm[IntegerOfNaturalLessEqual, TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ ↑m ≤ ↑n ⇒ m ≤ n -->

---

An inequality of natural numbers from that of their integers:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, Implies[Typed[m, Integers] <= n, m <= n]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m, n, h],
    TypeTheoryTactic["Exact", IntegerOfNaturalLessEqual[m, n, h]]
}]
```

<!-- => Proof complete -->
