---
Template: Symbol
Name: LessEqualStep
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualStep
Keywords: [less, equal, step, prelude, natural numbers]
SeeAlso: [LessEqualReflexivity, LessEqualAddition, LessEqualTransitivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualStep]()[*h*]</code> proves <code>*n* <= *m* + 1</code> from a proof *h* of <code>*n* <= *m*</code>.

## Details & Options

- [LessEqualStep]() is the second constructor of [LessEqual](), as Lean's `Nat.le.step`.
- *n* and *m* are implicit arguments, found from the type of *h*.

## Basic Examples

The statement of [LessEqualStep]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualStep]]
```

<!-- => ∀_{n∶ℕ} ∀_{m∶ℕ} n ≤ m ⇒ n ≤ m + 1 -->

---

`3 <= 5`, two steps up from `3 <= 3`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualStep[LessEqualStep[LessEqualReflexivity]]], TypeTheoryTerm[3 <= 5]]
```

<!-- => Success["TypeChecked", ...] -->
