---
Template: Symbol
Name: MultiplicationZeroRight
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MultiplicationZeroRight
Keywords: [multiplication, zero, right, prelude, natural numbers]
SeeAlso: [MultiplicationZeroLeft, MultiplicationOneRight, Times]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MultiplicationZeroRight]()[*n*]</code> proves <code>*n* * 0 == 0</code>.

## Details & Options

- [MultiplicationZeroRight]() is a theorem of the prelude that holds by computation: [Times]() recurses on its second argument.

## Basic Examples

The statement of [MultiplicationZeroRight]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationZeroRight]]
```

<!-- => ∀_n∶ℕ n 0 == 0 -->

---

An instance:

```wl
TypeTheoryCheck[TypeTheoryTerm[MultiplicationZeroRight[9]]]
```

<!-- => 9 × 0 == 0 -->

## Scope

The tactic `"Reflexivity"` proves it, since `n * 0` computes to 0:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, n * 0 == 0], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Reflexivity"]
}]
```

<!-- => Proof complete -->

---

Since `0^(n + 1)` computes to `0^n * 0`, an instance proves that a positive power of 0 is 0:

```wl
TypeTheoryProof[ForAll[{Typed[n, Naturals]}, 0^(n + 1) == 0], {
    TypeTheoryTactic["Introduce", n],
    TypeTheoryTactic["Exact", MultiplicationZeroRight[0^n]]
}]
```

<!-- => Proof complete -->

## Properties and Relations

Multiplying by 0 on the right is the constant function 0 by computation:

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, n * 0]], TypeTheoryTerm[Function[{Typed[n, Naturals]}, 0]]]
```

<!-- => True -->

## Possible Issues

On the left, 0 does not compute away, so it needs [MultiplicationZeroLeft]():

```wl
DefinitionallyEqualQ[TypeTheoryTerm[Function[{Typed[n, Naturals]}, 0 * n]], TypeTheoryTerm[Function[{Typed[n, Naturals]}, 0]]]
```

<!-- => False -->
