---
Template: Symbol
Name: MultiplicationSuccessorLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationSuccessorLeft
Keywords: [multiplication, successor, left, prelude, natural numbers]
SeeAlso: [MultiplicationSuccessorRight, MultiplicationCommutativity, MultiplicationDistributivityRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationSuccessorLeft]()[*m*, *n*]</code> proves <code>(*m* + 1) * *n* == *m* * *n* + *n*</code>.

## Details & Options

- [MultiplicationSuccessorLeft]() is a theorem of the prelude, proved by induction on *n* with [AdditionAssociativity]() and [AdditionCommutativity]().

## Basic Examples

The statement of [MultiplicationSuccessorLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationSuccessorLeft]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ (m + 1) n == m n + n -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationSuccessorLeft[3, 4]]]
```

<!-- => (3 + 1) 4 == 3 × 4 + 4 -->

## Scope

The tactic `"Rewrite"` splits off the last summand, and [AdditionCommutativity]() moves it to the front:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, (m + 1) * n == n + m * n], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Rewrite", MultiplicationSuccessorLeft[m, n]],
    TypeTheoryTactic["Rewrite", AdditionCommutativity[m * n, n]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

[MultiplicationSuccessorRight]() holds by computation, but this law does not, as [DefinitionallyEqualQ]() shows:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, (m + 1) * n]],
    TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, m * n + n]]
]
```

<!-- => False -->

---

The tactic `"Ring"` proves it without naming the law:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, (m + 1) * n == m * n + n], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->
