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
