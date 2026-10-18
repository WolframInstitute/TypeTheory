---
Template: Symbol
Name: LessEqualReflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualReflexivity
Keywords: [less, equal, reflexivity, prelude, natural numbers]
SeeAlso: [LessEqualStep, LessEqualZero, LessEqualTransitivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

[LessEqualReflexivity]() proves <code>*n* <= *n*</code>.

## Details & Options

- [LessEqual]() is an inductive family of the prelude, as Lean's `Nat.le`: <code>*m* <= *n*</code> when *n* is *m*, or the successor of a number at least *m*. [LessEqualReflexivity]() and [LessEqualStep]() are its constructors.
- *n* is an implicit argument, found from the type the proof is expected to have.

## Basic Examples

The statement of [LessEqualReflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualReflexivity]]
```

<!-- => ∀_{n∶ℕ} n ≤ n -->

---

A proof of `3 <= 3`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualReflexivity], TypeTheoryTerm[3 <= 3]]
```

<!-- => True -->
