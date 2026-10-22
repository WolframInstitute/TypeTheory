---
Template: Symbol
Name: Fiber
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/Fiber
Keywords: [fiber, equivalence, cubical type theory]
SeeAlso: [IsContractible, IsEquivalence, Equivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[Fiber]()[*f*, *y*]</code> is the type of the elements *x* with a path from *f*[*x*] to *y*: <code>[DependentSum]()[*A*, [Function]()[{*x*}, Path[*B*, *f*[*x*], *y*]]]</code>.

## Details & Options

- An equivalence is a function whose fibers are contractible, [IsContractible]().
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its definition:

```wl
cubical[Fiber]
```

<!-- => definition Fiber : ∀_{A∶Type u} ∀_{B∶Type u} (A→B)→B→Type u := {A∶Type u} {B∶Type u} (f∶A→B) (y∶B)↦DependentSum[A,(x∶A)↦f[x]≡y] -->
