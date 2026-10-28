---
Template: Symbol
Name: LessEqualTotality
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualTotality
Keywords: [order, totality, trichotomy, inequality, prelude, natural numbers]
SeeAlso: [LessEqualAntisymmetry, LessEqualDecidable, AdditionMonotonicity, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualTotality]()[*m*, *n*]</code> proves <code>[Or]()[*m* <= *n*, *n* < *m*]</code>.

## Details & Options

- [LessEqualTotality]() is a theorem of the prelude, proved by induction on *m* and cases on *n*.
- The tactic `"LinearArithmetic"` of [TypeTheoryTactic]() splits on it, and refutes the case it does not want.

## Basic Examples

The statement of [LessEqualTotality]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualTotality]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ (m ≤ n ∨ n < m) -->

---

For 3 and 5:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualTotality[3, 5]]]
```

<!-- => 3 ≤ 5 ∨ 5 < 3 -->

## Scope

Compared with 0, a number is at most 0 or greater than 0:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals]}, LessEqualTotality[x, 0]]]]
```

<!-- => ∀_x∶ℕ (x ≤ 0 ∨ 0 < x) -->

## Applications

The recursor of [Or]() splits on it, here to prove that of any two numbers one is at most the other:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, Or[m <= n, n <= m]], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Exact", InductiveRecursor[Or][
        Function[{Typed[s, Or[m <= n, n < m]]}, Or[m <= n, n <= m]],
        Function[{Typed[g, m <= n]}, OrIntroductionLeft[g]],
        Function[{Typed[g, n < m]}, OrIntroductionRight[LessEqualTransitivity[LessEqualStep[LessEqualReflexivity], g]]],
        LessEqualTotality[m, n]
    ]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The tactic `"LinearArithmetic"` splits on it, and refutes the case it does not want:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x + y <= 3, Implies[y <= x, y <= 1]]], {
    TypeTheoryTactic["Introduce", x, y, h, k],
    TypeTheoryTactic["LinearArithmetic"]
}]
```

<!-- => Proof complete -->

---

The tactic `"Decide"` proves an instance with literals by computing which side holds:

```wl
TypeTheoryProof[Or[3 <= 5, 5 < 3], {TypeTheoryTactic["Decide"]}]
```

<!-- => Proof complete -->
