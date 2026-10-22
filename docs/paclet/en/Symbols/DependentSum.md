---
Template: Symbol
Name: DependentSum
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DependentSum
Keywords: [dependent sum, sigma type, pair, cubical type theory]
SeeAlso: [DependentPair, TypeTheoryCubical, Equivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[DependentSum]()[*A*, *B*]</code> is the dependent sum Σ *x* : *A*, *B*[*x*] of the cubical environment, whose elements are the pairs <code>[DependentPair]()[*a*, *b*]</code>.

## Details & Options

- It is a structure: <code>*p*[[1]]</code> and <code>*p*[[2]]</code> are the fields of a pair *p*.
- [TypeTheoryCubical]() names it, and the kernel writes the equivalences of Glue types with it.
- It is a constant of <code>[TypeTheoryEnvironment]()["Cubical"]</code>.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its declaration:

```wl
cubical[DependentSum]
```

<!-- => inductive DependentSum : ∀_A∶Type u (A→Type v)→Type (max u v) ; | DependentPair : ∀_{A∶Type u} ∀_{B∶A→Type v} ∀_a∶A B[a]→DependentSum[A,B] -->
