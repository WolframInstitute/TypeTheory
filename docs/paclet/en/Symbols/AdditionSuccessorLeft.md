---
Template: Symbol
Name: AdditionSuccessorLeft
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionSuccessorLeft
Keywords: [addition, successor, left, prelude, natural numbers]
SeeAlso: [AdditionSuccessorRight, AdditionCommutativity, AdditionZeroLeft]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionSuccessorLeft]()[*m*, *n*]</code> proves <code>*m* + 1 + *n* == *m* + *n* + 1</code>.

## Details & Options

- [AdditionSuccessorLeft]() is a theorem of the prelude, proved by induction on *n*.

## Basic Examples

The statement of [AdditionSuccessorLeft]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionSuccessorLeft]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + 1 + n == m + n + 1 -->

---

For variables:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, AdditionSuccessorLeft[m, n]]]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + 1 + n == m + n + 1 -->

## Scope

The tactic `"Rewrite"` moves the successor out of the sum, and [AdditionCommutativity]() finishes the proof:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m + 1 + n == n + m + 1], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Rewrite", AdditionSuccessorLeft[m, n]],
    TypeTheoryTactic["Rewrite", AdditionCommutativity[m, n]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

[AdditionSuccessorRight]() holds by computation, but this law does not, since the two sides are not definitionally equal while *n* is a variable:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, m + 1 + n]],
    TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, m + n + 1]]
]
```

<!-- => False -->

---

When *n* is a literal, the two sides compute to the same term, and `"Reflexivity"` proves the instance:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals]}, m + 1 + 2 == m + 2 + 1], {
    TypeTheoryTactic["Introduce", m],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

---

The tactic `"Ring"` proves it without naming the law:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m + 1 + n == m + n + 1], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Ring"]
}]
```

<!-- => Proof complete -->
