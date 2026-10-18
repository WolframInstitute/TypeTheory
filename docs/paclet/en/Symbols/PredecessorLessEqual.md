---
Template: Symbol
Name: PredecessorLessEqual
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/PredecessorLessEqual
Keywords: [predecessor, less, equal, prelude, natural numbers]
SeeAlso: [NaturalNumberPredecessor, LessEqualPredecessor, LessEqualStep]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[PredecessorLessEqual]()[*n*]</code> proves <code>[NaturalNumberPredecessor]()[*n*] <= *n*</code>.

## Details & Options

- [PredecessorLessEqual]() is a theorem of the prelude, proved by cases on *n* with the recursor of [NonNegativeIntegers]().

## Basic Examples

The statement of [PredecessorLessEqual]():

```wl
TypeTheoryCheck[TypeTheoryTerm[PredecessorLessEqual]]
```

<!-- => ∀_n∶ℕ n - 1 ≤ n -->

---

So `5 <= 6`:

```wl
TypeTheoryCheck[TypeTheoryTerm[PredecessorLessEqual[6]], TypeTheoryTerm[5 <= 6]]
```

<!-- => True -->
