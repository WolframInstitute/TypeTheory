---
Template: Symbol
Name: LessEqualAddition
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessEqualAddition
Keywords: [less, equal, addition, prelude, natural numbers]
SeeAlso: [LessEqualZero, LessEqualStep, Less]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessEqualAddition]()[*n*, *m*]</code> proves <code>*n* <= *n* + *m*</code>.

## Details & Options

- [LessEqualAddition]() is a theorem of the prelude, proved by induction on *m*.
- <code>*n* < *m*</code> is <code>[Less]()[*n*, *m*]</code>, which unfolds to <code>*n* + 1 <= *m*</code>, so [LessEqualAddition]() also proves strict inequalities.

## Basic Examples

The statement of [LessEqualAddition]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAddition]]
```

<!-- => ∀_n∶ℕ ∀_m∶ℕ n ≤ n + m -->

---

`3 < 6` unfolds to `4 <= 6`:

```wl
TypeTheoryCheck[TypeTheoryTerm[LessEqualAddition[4, 2]], TypeTheoryTerm[3 < 6]]
```

<!-- => True -->
