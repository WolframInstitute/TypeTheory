---
Template: Symbol
Name: SubtractionSuccessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtractionSuccessor
Keywords: [subtraction, successor, prelude, natural numbers]
SeeAlso: [SubtractionSelf, AdditionSubtractionCancellation, Subtract]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtractionSuccessor]()[*n*, *m*]</code> proves <code>(*n* + 1) - (*m* + 1) == *n* - *m*</code>.

## Details & Options

- [SubtractionSuccessor]() is a theorem of the prelude, proved by induction on *m*.

## Basic Examples

The statement of [SubtractionSuccessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionSuccessor]]
```

<!-- => ∀_n∶ℕ ∀_m∶ℕ (n + 1) - (m + 1) == n - m -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionSuccessor[7, 2]]]
```

<!-- => (7 + 1) - (2 + 1) == 7 - 2 -->

## Scope

The tactic `"Rewrite"` removes the two successors inside a goal, and the goal closes:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, (x + 1) - (y + 1) + y == x - y + y], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Rewrite", SubtractionSuccessor[x, y]]
}]
```

<!-- => Proof complete -->

---

The tactic `"Apply"` finds *n* and *m* from the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, (x + 1) - (y + 1) == x - y], {
    TypeTheoryTactic["Introduce", x, y],
    TypeTheoryTactic["Apply", SubtractionSuccessor]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Subtraction recurses on its second argument with [NaturalNumberPredecessor](), so `n - (m + 1)` is the predecessor of `n - m` by computation:

```wl
DefinitionallyEqualQ[
    TypeTheoryTerm[Function[{Typed[n, Naturals], Typed[m, Naturals]}, n - (m + 1)]],
    TypeTheoryTerm[Function[{Typed[n, Naturals], Typed[m, Naturals]}, NaturalNumberPredecessor[n - m]]]
]
```

<!-- => True -->

---

When *m* is a literal, the two sides compute to the same term, and `"Reflexivity"` proves the instance:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, (n + 1) - (2 + 1) == n - 2], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->
