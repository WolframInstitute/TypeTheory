---
Template: Symbol
Name: MultiplicationMonotonicity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationMonotonicity
Keywords: [multiplication, monotonicity, inequality, prelude, natural numbers]
SeeAlso: [AdditionMonotonicity, LessEqualTotality, MultiplicationCancellation, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationMonotonicity]()[*k*, *h*]</code> proves <code>*a* *k* <= *b* *k*</code> from a proof *h* of <code>*a* <= *b*</code>.

## Details & Options

- [MultiplicationMonotonicity]() is a theorem of the prelude, proved by induction on *k* with [AdditionMonotonicity]().
- *a* and *b* are implicit arguments, found from the type of *h*.
- The tactic `"LinearArithmetic"` of [TypeTheoryTactic]() multiplies inequalities with it.

## Basic Examples

The statement of [MultiplicationMonotonicity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationMonotonicity]]
```

<!-- => ∀_{a ∶ ℕ} ∀_{b ∶ ℕ} ∀_k∶ℕ a ≤ b ⇒ a k ≤ b k -->

---

An inequality multiplied by 3:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, MultiplicationMonotonicity[3, h]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x ≤ y ⇒ x 3 ≤ y 3 -->

## Scope

The tactic `"Apply"` finds *k* from the goal and leaves the inequality to multiply:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals], Typed[z, Naturals]}, Implies[x <= y, x * z <= y * z]], {
    TypeTheoryTactic["Introduce", x, y, z, h],
    TypeTheoryTactic["Apply", MultiplicationMonotonicity]
}]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, z ∶ ℕ, h ∶ x ≤ y ⊢ x ≤ y -->

## Applications

Square both sides of an inequality, chaining two products with [LessEqualTransitivity]() and swapping the factors of one with [MultiplicationCommutativity]():

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, x * x <= y * y]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["Apply", LessEqualTransitivity],
    TypeTheoryTactic["Exact", MultiplicationMonotonicity[x, h]],
    TypeTheoryTactic["Rewrite", MultiplicationCommutativity[y, x]],
    TypeTheoryTactic["Exact", MultiplicationMonotonicity[y, h]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

The tactic `"LinearArithmetic"` multiplies inequalities with it, here by 3 on the left:

```wl
TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, 3 x <= 3 y]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["LinearArithmetic"]
}]
```

<!-- => Proof complete -->

## Possible Issues

The factor multiplies on the right, so the result is `x * 3 <= y * 3`, which is not `3 x <= 3 y` by computation:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, MultiplicationMonotonicity[3, h]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, 3 x <= 3 y]]]
]
```

<!-- => Failure["TypeMismatch", ...] -->
