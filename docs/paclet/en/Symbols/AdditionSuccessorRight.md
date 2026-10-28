---
Template: Symbol
Name: AdditionSuccessorRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionSuccessorRight
Keywords: [addition, successor, right, prelude, natural numbers]
SeeAlso: [AdditionSuccessorLeft, AdditionAssociativity, AdditionZeroRight]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionSuccessorRight]()[*m*, *n*]</code> proves <code>*m* + (*n* + 1) == *m* + *n* + 1</code>.

## Details & Options

- [AdditionSuccessorRight]() is a theorem of the prelude that holds by computation: [Plus]() recurses on its second argument.

## Basic Examples

The statement of [AdditionSuccessorRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionSuccessorRight]]
```

<!-- => ∀_m∶ℕ ∀_n∶ℕ m + (n + 1) == m + n + 1 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionSuccessorRight[2, 3]]]
```

<!-- => 2 + (3 + 1) == 2 + 3 + 1 -->

## Scope

The tactic `"Reflexivity"` proves it, since the two sides compute to the same term:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m + (n + 1) == m + n + 1], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

---

The tactic `"Rewrite"` with it, then with [AdditionCommutativity](), proves a reordered sum:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m + (n + 1) == n + m + 1], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Rewrite", AdditionSuccessorRight[m, n]],
    TypeTheoryTactic["Rewrite", AdditionCommutativity[m, n]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The two sides are definitionally equal as functions of *m* and *n*:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, m + (n + 1)]],
    TypeTheoryTerm[Function[{Typed[m, Naturals], Typed[n, Naturals]}, m + n + 1]]
]
```

<!-- => True -->

---

With the successor on the left, the sides are not equal by computation, which is why [AdditionSuccessorLeft]() is proved by induction:

```wl
TypeTheoryProof[ForAll[{Typed[m, Naturals], Typed[n, Naturals]}, m + 1 + n == m + n + 1], {
    TypeTheoryTactic["Introduce", m, n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Failure["NotReflexive", ...] -->
