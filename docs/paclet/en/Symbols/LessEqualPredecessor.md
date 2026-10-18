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
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[x, NonNegativeIntegers], Typed[h, x + 1 <= 5]}, LessEqualPredecessor[h]]]]
```

<!-- => ∀_x∶ℕ x + 1 ≤ 5 ⇒ x ≤ 4 -->
