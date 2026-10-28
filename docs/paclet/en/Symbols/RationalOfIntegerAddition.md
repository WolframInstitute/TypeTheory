---
Template: Symbol
Name: RationalOfIntegerAddition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RationalOfIntegerAddition
Keywords: [rationals, integers, coercion, addition, theorem, Lean]
SeeAlso: [RationalOfIntegerMultiplication, IntegerOfNaturalAddition]
RelatedGuides: [TypeTheory]
RelatedTutorials: [TheRationals]
---

## Usage

<code>[RationalOfIntegerAddition]()[*a*, *b*]</code> proves that the rational of <code>*a* + *b*</code> is the sum of the rationals of the integers *a* and *b*.

## Details & Options

- [RationalOfIntegerAddition]() is a theorem of <code>[TypeTheoryEnvironment]()["Rationals"]</code>, the environment of the integers with the rationals.
- The integers are rationals by the coercion `"rationalOfInteger"`, which shows as `↑`; the law says it keeps their sums, as Mathlib's `Int.cast_add`.
- It is proved by [QuotientSoundness]() and `"Ring"`: the two sides are classes of pairs whose relation is an identity of the integers.

## Basic Examples

The statement of [RationalOfIntegerAddition]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalOfIntegerAddition, TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ ∀_b∶ℤ ↑(a + b) == ↑a + ↑b -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[RationalOfIntegerAddition[2, -5], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ↑(2 + -5) == 2 + -5 -->

## Scope

An instance with a variable:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Integers]}, RationalOfIntegerAddition[a, 1]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_a∶ℤ ↑(a + 1) == ↑a + 1 -->

---

Natural numbers are rationals by way of the integers, so their coercion shows as `↑↑`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, RationalOfIntegerAddition[m, n]], TypeTheoryEnvironment["Rationals"]]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ ↑(↑m + ↑n) == ↑↑m + ↑↑n -->

## Applications

`"Rewrite"` with the law splits the rational of a sum, so that the laws of the rationals apply to its parts:

```wl
TypeTheoryProof[ForAll[{Typed[a, Integers], Typed[b, Integers], Typed[x, Rationals]}, "rationalOfInteger"[a + b] + x == a + (b + x)], TypeTheoryEnvironment["Rationals"], {
    TypeTheoryTactic["Introduce", a, b, x],
    TypeTheoryTactic["Rewrite", RationalOfIntegerAddition],
    TypeTheoryTactic["Rewrite", RationalAdditionAssociativity]
}]
```

<!-- => Proof complete -->

## Possible Issues

`Typed[a + b, Rationals]` is the sum of the rationals of `a` and `b`, not the rational of their sum, which is written with the coercion `"rationalOfInteger"`:

```wl
TypeTheoryProof[ForAll[{Typed[a, Integers], Typed[b, Integers]}, Typed[a + b, Rationals] == a + b], TypeTheoryEnvironment["Rationals"]]
```

<!-- => Proof, 1 goal: ⊢ ∀_a∶ℤ ∀_b∶ℤ ↑a + ↑b == ↑a + ↑b -->
