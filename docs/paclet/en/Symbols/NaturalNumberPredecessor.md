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

## Scope

At a successor of a variable it computes, so the number before `n + 1` is *n* by `"Reflexivity"`:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, NaturalNumberPredecessor[n + 1] == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

---

At a literal it computes, however large the literal:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[10^20]]]
```

<!-- => 99999999999999999999 -->

## Properties and Relations

Subtracting 1 is the predecessor by computation, which is why the predecessor of *n* shows as `n - 1`:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n - 1]], TypeTheoryTerm[NaturalNumberPredecessor]]
```

<!-- => True -->

## Possible Issues

The predecessor of 0 is 0, so adding 1 back gives 1, not 0:

```wl
WeakHeadNormalForm[TypeTheoryTerm[NaturalNumberPredecessor[0] + 1]]
```

<!-- => 1 -->
