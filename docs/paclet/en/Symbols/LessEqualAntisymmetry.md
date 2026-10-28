---
Template: Symbol
Name: LessEqualAntisymmetry
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualAntisymmetry
Keywords: [less, equal, antisymmetry, prelude, natural numbers]
SeeAlso: [LessEqualTransitivity, LessIrreflexivity, LessEqualReflexivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualAntisymmetry]()[*h1*, *h2*]</code> proves <code>*a* == *b*</code> from proofs *h1* of <code>*a* <= *b*</code> and *h2* of <code>*b* <= *a*</code>.

## Details & Options

- [LessEqualAntisymmetry]() is a theorem of the prelude, proved with the recursor of [LessEqual](), [LessIrreflexivity]() and [FalseElimination]().
- *a* and *b* are implicit arguments, found from the types of *h1* and *h2*.

## Basic Examples

The statement of [LessEqualAntisymmetry]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAntisymmetry]]
```

<!-- => ∀_{a∶ℕ} ∀_{b∶ℕ} a ≤ b ⇒ b ≤ a ⇒ a == b -->

---

From `x <= 3` and `3 <= x`, `x == 3`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[h1, x <= 3], Typed[h2, 3 <= x]}, LessEqualAntisymmetry[h1, h2]]]]
```

<!-- => ∀_x∶ℕ x ≤ 3 ⇒ 3 ≤ x ⇒ x == 3 -->

## Scope

The tactic `"Apply"` leaves a goal for each inequality:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, Implies[y <= x, x == y]]], {
    TypeTheoryTactic["Introduce", x, y, h1, h2],
    TypeTheoryTactic["Apply", LessEqualAntisymmetry]
}]
```

<!-- => Proof, 2 goals: x ∶ ℕ, y ∶ ℕ, h1 ∶ x ≤ y, h2 ∶ y ≤ x ⊢ x ≤ y; x ∶ ℕ, y ∶ ℕ, h1 ∶ x ≤ y, h2 ∶ y ≤ x ⊢ y ≤ x -->

---

With [LessEqualZero](), a number that is at most 0 is 0:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[h, x <= 0]}, LessEqualAntisymmetry[h, LessEqualZero[x]]]]]
```

<!-- => ∀_x∶ℕ x ≤ 0 ⇒ x == 0 -->

## Properties and Relations

The tactic `"LinearArithmetic"` also proves an equation from the two inequalities:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, Implies[y <= x, x == y]]], {
    TypeTheoryTactic["Introduce", x, y, h1, h2],
    TypeTheoryTactic["LinearArithmetic"]
}]
```

<!-- => Proof complete -->

---

The order of the two proofs gives the order of the sides of the equation:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h1, x <= y], Typed[h2, y <= x]}, LessEqualAntisymmetry[h2, h1]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x ≤ y ⇒ y ≤ x ⇒ y == x -->
