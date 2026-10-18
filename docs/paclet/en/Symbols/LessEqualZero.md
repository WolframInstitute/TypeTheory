---
Template: Symbol
Name: LessEqualZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualZero
Keywords: [less, equal, zero, prelude, natural numbers]
SeeAlso: [LessEqualReflexivity, LessEqualStep, SuccessorNotLessEqualZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualZero]()[*n*]</code> proves <code>0 <= *n*</code>.

## Details & Options

- [LessEqualZero]() is a theorem of the prelude, proved by induction on *n*: <code>[LessEqualStep]()[*h*]</code> at each successor.

## Basic Examples

The statement of [LessEqualZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualZero]]
```

<!-- => ∀_n∶ℕ 0 ≤ n -->

---

`7 >= 0` is <code>[GreaterEqual]()[7, 0]</code>, which unfolds to `0 <= 7`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualZero[7]], TypeTheoryTerm[7 >= 0]]
```

<!-- => True -->
