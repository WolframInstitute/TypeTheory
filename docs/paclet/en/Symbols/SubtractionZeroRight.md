---
Template: Symbol
Name: SubtractionZeroRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/SubtractionZeroRight
Keywords: [subtraction, zero, right, prelude, natural numbers]
SeeAlso: [SubtractionZeroLeft, SubtractionSuccessor, Subtract]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[SubtractionZeroRight]()[*n*]</code> proves <code>*n* - 0 == *n*</code>.

## Details & Options

- [SubtractionZeroRight]() is a theorem of the prelude that holds by computation: [Subtract]() recurses on its second argument.
- `a - b` is read as <code>[Subtract]()[*a*, *b*]</code>.

## Basic Examples

The statement of [SubtractionZeroRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionZeroRight]]
```

<!-- => ∀_n∶ℕ n - 0 == n -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[SubtractionZeroRight[6]]]
```

<!-- => 6 - 0 == 6 -->

## Scope

The tactic `"Reflexivity"` proves it, since `n - 0` computes to *n*:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n - 0 == n], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Subtracting 0 is the identity function by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n - 0]], TypeTheoryTerm[Function[{Typed[n, Naturals]}, n]]]
```

<!-- => True -->

---

Subtracting 1 is [NaturalNumberPredecessor]() by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n - 1]], TypeTheoryTerm[NaturalNumberPredecessor]]
```

<!-- => True -->

## Possible Issues

On the left, 0 does not compute away, so `0 - n` is not 0 by computation and needs [SubtractionZeroLeft]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, 0 - n]], TypeTheoryTerm[Function[{Typed[n, Naturals]}, 0]]]
```

<!-- => False -->
