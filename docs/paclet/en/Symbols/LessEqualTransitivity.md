---
Template: Symbol
Name: LessEqualTransitivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualTransitivity
Keywords: [less, equal, transitivity, prelude, natural numbers]
SeeAlso: [LessEqualAntisymmetry, LessEqualReflexivity, EqualityTransitivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualTransitivity]()[*h1*, *h2*]</code> proves <code>*a* <= *c*</code> from proofs *h1* of <code>*a* <= *b*</code> and *h2* of <code>*b* <= *c*</code>.

## Details & Options

- [LessEqualTransitivity]() is a theorem of the prelude, proved with the recursor of [LessEqual]() on *h2*.
- *a*, *b* and *c* are implicit arguments, found from the types of *h1* and *h2*.

## Basic Examples

The statement of [LessEqualTransitivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualTransitivity]]
```

<!-- => ∀_{a∶ℕ} ∀_{b∶ℕ} ∀_{c∶ℕ} a ≤ b ⇒ b ≤ c ⇒ a ≤ c -->

---

From `0 <= 2` and `2 <= 5`, `0 <= 5`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualTransitivity[LessEqualZero[2], LessEqualAddition[2, 3]]], TypeTheoryTerm[0 <= 5]]
```

<!-- => Success["TypeChecked", ...] -->

## Scope

The tactic `"Apply"` leaves a goal for each inequality, and one for the number between them:

```wl
proof = TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, Implies[x <= y, Implies[y <= z, x <= z]]], {
    TypeTheoryTactic["Introduce", x, y, z, h1, h2],
    TypeTheoryTactic["Apply", LessEqualTransitivity]
}]
```

<!-- => Proof, 3 goals: x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h1 ∶ x ≤ y, h2 ∶ y ≤ z ⊢ x ≤ ?m; the same hypotheses ⊢ ?m ≤ z; the same hypotheses ⊢ ℕ -->

Solving the first goal with `h1` makes the number between them `y`:

```wl
proof = TypeTheoryTactic["Exact", h1][proof]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h1 ∶ x ≤ y, h2 ∶ y ≤ z ⊢ y ≤ z -->

The other hypothesis proves the last goal:

```wl
TypeTheoryTactic["Exact", h2][proof]
```

<!-- => Proof complete -->

---

A strict inequality first gives a strict inequality, since `x < y` is `x + 1 <= y`:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals], Typed[h1, x < y], Typed[h2, y <= z]}, LessEqualTransitivity[h1, h2]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, Implies[x < y, Implies[y <= z, x < z]]]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

The tactic `"LinearArithmetic"` chains inequalities too:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, Implies[x <= y, Implies[y <= z, x <= z]]], {
    TypeTheoryTactic["Introduce", x, y, z, h1, h2],
    TypeTheoryTactic["LinearArithmetic"]
}]
```

<!-- => Proof complete -->
