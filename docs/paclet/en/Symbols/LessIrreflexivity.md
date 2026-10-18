---
Template: Symbol
Name: LessIrreflexivity
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LessIrreflexivity
Keywords: [less, irreflexivity, prelude, natural numbers]
SeeAlso: [LessEqualAntisymmetry, SuccessorNotLessEqualZero, Less]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LessIrreflexivity]()[*n*]</code> proves <code>[Not]()[*n* < *n*]</code>.

## Details & Options

- [LessIrreflexivity]() is a theorem of the prelude, proved by induction on *n* with [SuccessorNotLessEqualZero]() and [LessEqualPredecessor]().

## Basic Examples

The statement of [LessIrreflexivity]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LessIrreflexivity]]
```

<!-- => ∀_n∶ℕ ¬n < n -->

---

With it, `3 <= 2` is false: it would make `2 < 2`:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[h, 3 <= 2]}, LessIrreflexivity[2][LessEqualTransitivity[h, LessEqualReflexivity]]]], TypeTheoryTerm[Not[3 <= 2]]]
```

<!-- => True -->
