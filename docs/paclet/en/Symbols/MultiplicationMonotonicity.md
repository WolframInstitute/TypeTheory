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
