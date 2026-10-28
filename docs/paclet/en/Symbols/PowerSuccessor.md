---
Template: Symbol
Name: PowerSuccessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PowerSuccessor
Keywords: [power, successor, prelude, natural numbers]
SeeAlso: [PowerZero, PowerAddition, Power]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PowerSuccessor]()[*m*, *n*]</code> proves <code>*m*^(*n* + 1) == *m*^*n* * *m*</code>.

## Details & Options

- [PowerSuccessor]() is a theorem of the prelude that holds by computation: it is how [Power]() is defined.

## Basic Examples

The statement of [PowerSuccessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerSuccessor]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m^(n + 1) == m^n m -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[PowerSuccessor[2, 3]]]
```

<!-- => 2^(3 + 1) == 2^3 × 2 -->

## Scope

The tactic `"Reflexivity"` proves it, since it is how powers compute:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m^(n + 1) == m^n * m], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

---

The tactic `"Rewrite"` with it, then with [MultiplicationCommutativity](), puts the new factor first:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m^(n + 1) == m * m^n], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Rewrite", PowerSuccessor[m, n]],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[m^n, m]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Applied again and again, it turns a power with a literal exponent into a product, so `m^3` is `1 * m * m * m` by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[m, Naturals]}, m^3]], TypeTheoryTerm[Function[{Typed[m, Naturals]}, 1 * m * m * m]]]
```

<!-- => True -->

---

The tactic `"Ring"` expands a power by a literal, so it proves that `m^3` is `m m m`:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m^3 == m * m * m], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->
