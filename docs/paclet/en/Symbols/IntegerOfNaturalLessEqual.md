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

## Scope

`"Apply"` turns an inequality of natural numbers into one of their integers:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m <= m + 1], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Apply", IntegerOfNaturalLessEqual]
}]
```

<!-- => Proof, 1 goal: m ∶ ℕ ⊢ ↑m ≤ ↑(m + 1) -->

`"SumOfSquares"` proves that one:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m <= m + 1], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Apply", IntegerOfNaturalLessEqual],
    TypeTheoryTactic["SumOfSquares"]
}]
```

<!-- => Proof complete -->

## Applications

`"SumOfSquares"` applies the law itself, proving an inequality of natural numbers as that of their integers:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals]}, 4 a b <= (a + b)^2], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", a, b],
    TypeTheoryTactic["SumOfSquares"]
}]
```

<!-- => Proof complete -->

## Possible Issues

A difference of natural numbers stops at 0, so `"Apply"` leaves the integer of `m - n`, which is not `↑m - ↑n`:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m - n <= m], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Apply", IntegerOfNaturalLessEqual]
}]
```

<!-- => Proof, 1 goal: m ∶ ℕ, n ∶ ℕ ⊢ ↑(m - n) ≤ ↑m -->

`"SumOfSquares"` takes it as an atom, and finds no sum of squares:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m - n <= m], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["SumOfSquares"]
}]
```

<!-- => Failure["NoSumOfSquares", ...] -->
