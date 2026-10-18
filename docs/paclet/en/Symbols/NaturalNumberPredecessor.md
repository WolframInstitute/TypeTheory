---
Template: Symbol
Name: NaturalNumberPredecessor
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/NaturalNumberPredecessor
Keywords: [natural, number, predecessor, prelude, natural numbers]
SeeAlso: [NaturalNumberSuccessor, NaturalNumberZero, PredecessorLessEqual, SuccessorInjectivity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[NaturalNumberPredecessor]()[*n*]</code> is the natural number before *n*, and `0` before `0`.

## Details & Options

- [NaturalNumberPredecessor]() is a definition of the prelude, by the recursor of [NonNegativeIntegers](): the predecessor of `0` is `0`, and of <code>*k* + 1</code> is *k*.
- [Subtract]() is defined from it: <code>*m* - (*n* + 1)</code> is the predecessor of <code>*m* - *n*</code>.

## Basic Examples

The statement of [NaturalNumberPredecessor]():

```wl
TypeTheoryCheck[TypeTheoryTerm[NaturalNumberPredecessor]]
```

<!-- => ℕ → ℕ -->

---

The number before 10:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[10]]]
```

<!-- => 9 -->
