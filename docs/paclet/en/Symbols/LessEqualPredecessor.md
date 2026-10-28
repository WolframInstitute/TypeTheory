---
Template: Symbol
Name: LessEqualPredecessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualPredecessor
Keywords: [less, equal, predecessor, prelude, natural numbers]
SeeAlso: [LessEqualSuccessor, PredecessorLessEqual, LessIrreflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualPredecessor]()[*h*]</code> proves <code>*n* <= *m*</code> from a proof *h* of <code>*n* + 1 <= *m* + 1</code>.

## Details & Options

- [LessEqualPredecessor]() is a theorem of the prelude, proved with the recursor of [LessEqual]() and [PredecessorLessEqual]().
- *n* and *m* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [LessEqualPredecessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualPredecessor]]
```

<!-- => ∀_{n∶ℕ} ∀_{m∶ℕ} n + 1 ≤ m + 1 ⇒ n ≤ m -->

---

From `x + 1 <= 5`, `x <= 4`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[h, x + 1 <= 5]}, LessEqualPredecessor[h]]]]
```

<!-- => ∀_x∶ℕ x + 1 ≤ 5 ⇒ x ≤ 4 -->

## Scope

The tactic `"Apply"` leaves the inequality of the successors as the goal:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x + 1 <= y + 1, x <= y]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["Apply", LessEqualPredecessor]
}]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, h ∶ x + 1 ≤ y + 1 ⊢ x + 1 ≤ y + 1 -->

---

`x < y + 1` unfolds to `x + 1 <= y + 1`, so it turns a strict inequality into an inequality:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x < y + 1]}, LessEqualPredecessor[h]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x < y + 1 ⇒ x ≤ y -->

## Properties and Relations

It undoes [LessEqualSuccessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, LessEqualPredecessor[LessEqualSuccessor[h]]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x ≤ y ⇒ x ≤ y -->

## Possible Issues

`1 + x` is not a successor by computation, since addition recurses on its second argument, so a proof of `1 + x <= 1 + y` does not fit:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, 1 + x <= 1 + y]}, LessEqualPredecessor[h]]]]
```

<!-- => Failure["TypeMismatch", ...] -->
