---
Template: Symbol
Name: SuccessorNotLessEqualZero
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SuccessorNotLessEqualZero
Keywords: [successor, not, less, equal, zero, prelude, natural numbers]
SeeAlso: [SuccessorNotZero, LessIrreflexivity, LessEqualZero]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SuccessorNotLessEqualZero]()[*n*]</code> proves <code>[Not]()[*n* + 1 <= 0]</code>.

## Details & Options

- [SuccessorNotLessEqualZero]() is a theorem of the prelude, proved with the recursor of [LessEqual]() and [SuccessorNotZero]().

## Basic Examples

The statement of [SuccessorNotLessEqualZero]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorNotLessEqualZero]]
```

<!-- => ∀_n∶ℕ ¬n + 1 ≤ 0 -->

---

So `3 <= 0` is false:

```wl
TypeTheoryCheck[TypeTheoryTerm[SuccessorNotLessEqualZero[2]], TypeTheoryTerm[Not[3 <= 0]]]
```

<!-- => Success["TypeChecked", ...] -->
