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

## Scope

An instance with a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[n, Naturals]}, IntegerOfNaturalMultiplication[n, n]], TypeTheoryEnvironment["Integers"]]]
```

<!-- => ∀_n∶ℕ ↑(n n) == ↑n ↑n -->

## Applications

`"Rewrite"` with the law turns the integer of a product into a product of integers, here a square, which [IntegerSquareNonnegative]() bounds:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0 <= "integerOfNatural"[n n]], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Rewrite", IntegerOfNaturalMultiplication],
    TypeTheoryTactic["Exact", IntegerSquareNonnegative[n]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

`"Ring"` takes the integer of a product apart with the law:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals], Typed[x, Integers]}, "integerOfNatural"[m n] x == n (m x)], TypeTheoryEnvironment["Integers"], {
    TypeTheoryTactic["Introduce", m, n, x],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->

## Possible Issues

`Typed[m n, Integers]` is the product of the integers of `m` and `n`, not the integer of their product, which is written with the coercion `"integerOfNatural"`:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, Typed[m n, Integers] == m n], TypeTheoryEnvironment["Integers"]]
```

<!-- => Proof, 1 goal: ⊢ ∀_m∶ℕ ∀_n∶ℕ ↑m ↑n == ↑m ↑n -->
