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

## Scope

An instance with a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, IntegerOfNaturalAddition[n, 1]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_n∶ℕ ↑(n + 1) == ↑n + 1 -->

## Applications

`"Rewrite"` with the law splits the integer of a sum, so that the laws of the integers apply to its parts:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals], Typed[x, Integers]}, "integerOfNatural"[m + n] + x == m + (n + x)], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m, n, x],
    TypeTheoryTactic["Rewrite", IntegerOfNaturalAddition],
    TypeTheoryTactic["Rewrite", IntegerAdditionAssociativity]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"Ring"` takes the integer of a sum apart with the law, here inside a power:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, "integerOfNatural"[(m + n)^2] == m^2 + 2 m n + n^2], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

## Possible Issues

`Typed[m + n, Integers]` is the sum of the integers of `m` and `n`, not the integer of their sum, which is written with the coercion `"integerOfNatural"`:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, Typed[m + n, Integers] == m + n], TypeTheoryEnvironment["Integers"]]
```

<!-- => Proof, 1 goal: ⊢ ∀_m∶ℕ ∀_n∶ℕ ↑m + ↑n == ↑m + ↑n -->
