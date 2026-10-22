---
Template: Symbol
Name: IsContractible
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/IsContractible
Keywords: [contractible, center, equivalence, cubical type theory]
SeeAlso: [Fiber, IsEquivalence]
RelatedGuides: [TypeTheory]
RelatedTutorials: [CubicalTypeTheory]
---

## Usage

<code>[IsContractible]()[*X*]</code> is the type of an element *c* of *X*, its center, with a path from *c* to every element.

## Details & Options

- The kernel writes the same type for the fibers of the equivalences of Glue types, and transport in a Glue type uses their centers.
- It is a definition of <code>[TypeTheoryEnvironment]()["Cubical"]</code>; terms that use it name that environment.

## Basic Examples

The cubical environment:

```wl
cubical = TypeTheoryEnvironment["Cubical"]
```

<!-- => TypeTheoryEnvironment summary box: 34 constants -->

Its definition:

```wl
cubical[IsContractible]
```

<!-- => definition IsContractible : Type u → Type u := (A ∶ Type u) ↦ DependentSum[A, (c ∶ A) ↦ ∀_z∶A c ≡ z] -->
