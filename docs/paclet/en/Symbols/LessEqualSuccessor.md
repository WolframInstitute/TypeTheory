---
Template: Symbol
Name: LessEqualSuccessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualSuccessor
Keywords: [less, equal, successor, prelude, natural numbers]
SeeAlso: [LessEqualPredecessor, LessEqualStep, LessEqualTransitivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualSuccessor]()[*h*]</code> proves <code>*n* + 1 <= *m* + 1</code> from a proof *h* of <code>*n* <= *m*</code>.

## Details & Options

- [LessEqualSuccessor]() is a theorem of the prelude, proved with the recursor of [LessEqual]().
- *n* and *m* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [LessEqualSuccessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualSuccessor]]
```

<!-- => ∀_{n∶ℕ} ∀_{m∶ℕ} n ≤ m ⇒ n + 1 ≤ m + 1 -->

---

For variables:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, LessEqualSuccessor[h]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x ≤ y ⇒ x + 1 ≤ y + 1 -->

## Scope

The tactic `"Apply"` leaves the inequality without the successors as the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, x + 1 <= y + 1]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["Apply", LessEqualSuccessor]
}]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, h ∶ x ≤ y ⊢ x ≤ y -->

---

`x < y + 1` unfolds to `x + 1 <= y + 1`, so it proves a strict inequality:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, LessEqualSuccessor[h]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, x < y + 1]]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

[AdditionMonotonicity]() with [LessEqualReflexivity]() proves the same statement:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, AdditionMonotonicity[h, LessEqualReflexivity]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, x + 1 <= y + 1]]]
]
```

<!-- => Success["TypeChecked", ...] -->

---

The tactic `"LinearArithmetic"` proves it too:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, x + 1 <= y + 1]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["LinearArithmetic"]
}]
```

<!-- => Proof complete -->
