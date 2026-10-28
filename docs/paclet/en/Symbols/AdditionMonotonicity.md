---
Template: Symbol
Name: AdditionMonotonicity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/AdditionMonotonicity
Keywords: [addition, monotonicity, inequality, prelude, natural numbers]
SeeAlso: [MultiplicationMonotonicity, LessEqualTotality, LessEqualTransitivity, TypeTheoryTactic]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[AdditionMonotonicity]()[*h1*, *h2*]</code> proves <code>*a* + *c* <= *b* + *d*</code> from proofs *h1* of <code>*a* <= *b*</code> and *h2* of <code>*c* <= *d*</code>.

## Details & Options

- [AdditionMonotonicity]() is a theorem of the prelude, proved by induction on *h2* and then on *h1*, with [AdditionSuccessorLeft]().
- *a*, *b*, *c* and *d* are implicit arguments, found from the types of *h1* and *h2*.
- The tactic `"LinearArithmetic"` of [TypeTheoryTactic]() adds inequalities with it.

## Basic Examples

The statement of [AdditionMonotonicity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[AdditionMonotonicity]]
```

<!-- => ∀_{a ∶ ℕ} ∀_{b ∶ ℕ} ∀_{c ∶ ℕ} ∀_{d ∶ ℕ} a ≤ b ⇒ c ≤ d ⇒ a + c ≤ b + d -->

---

An inequality added to itself:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, AdditionMonotonicity[h, h]]]]
```

<!-- => ∀_x∶ℕ ∀_y∶ℕ x ≤ y ⇒ x + x ≤ y + y -->

## Scope

The tactic `"Apply"` leaves a goal for each inequality:

```wl
proof = TypeTheoryProof[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, x + 2 <= y + 3]], {
    TypeTheoryTactic["Introduce", x, y, h],
    TypeTheoryTactic["Apply", AdditionMonotonicity]
}]
```

<!-- => Proof, 2 goals: x ∶ ℕ, y ∶ ℕ, h ∶ x ≤ y ⊢ x ≤ y; x ∶ ℕ, y ∶ ℕ, h ∶ x ≤ y ⊢ 2 ≤ 3 -->

The hypothesis proves the first:

```wl
proof = TypeTheoryTactic["Assumption"][proof]
```

<!-- => Proof, 1 goal: x ∶ ℕ, y ∶ ℕ, h ∶ x ≤ y ⊢ 2 ≤ 3 -->

The tactic `"Decide"` proves the second, an inequality of literals:

```wl
TypeTheoryTactic["Decide"][proof]
```

<!-- => Proof complete -->

---

With [LessEqualReflexivity]() as the first proof, it adds the same number to both sides of an inequality:

```wl
TypeTheoryCheck[
    TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, AdditionMonotonicity[LessEqualReflexivity, h]]],
    TypeTheoryTerm[ForAll[{Typed[x, Naturals], Typed[y, Naturals]}, Implies[x <= y, 2 + x <= 2 + y]]]
]
```

<!-- => Success["TypeChecked", ...] -->

## Properties and Relations

The tactic `"LinearArithmetic"` adds inequalities with it:

```wl
TypeTheoryProof[ForAll[{Typed[a, Naturals], Typed[b, Naturals], Typed[c, Naturals], Typed[d, Naturals]}, Implies[a <= b, Implies[c <= d, a + c <= b + d]]], {
    TypeTheoryTactic["Introduce", a, b, c, d, h1, h2],
    TypeTheoryTactic["LinearArithmetic"]
}]
```

<!-- => Proof complete -->

## Possible Issues

Without a statement to check against, nothing fixes the number that [LessEqualReflexivity]() compares with itself:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, Naturals], Typed[y, Naturals], Typed[h, x <= y]}, AdditionMonotonicity[h, LessEqualReflexivity]]]]
```

<!-- => Failure["UnsolvedImplicitArgument", ...] -->
