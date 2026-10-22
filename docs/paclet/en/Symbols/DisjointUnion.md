---
Template: Symbol
Name: DisjointUnion
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/DisjointUnion
Keywords: [disjoint union, sum, coproduct, prelude, inductive type]
SeeAlso: [LeftInjection, RightInjection, CartesianProduct, Option]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[DisjointUnion]()[*α*, *β*]</code> is the type of the elements of *α* and of *β*, each tagged with its side.

## Details & Options

- [DisjointUnion]() is an inductive type of the prelude, with the constructors [LeftInjection]() and [RightInjection](), as Lean's `Sum`.
- For *α* in `Type u` and *β* in `Type v`, <code>[DisjointUnion]()[*α*, *β*]</code> is in `Type (max u v)`.

## Basic Examples

The type of [DisjointUnion]():

```wl
TypeTheoryCheck[TypeTheoryTerm[DisjointUnion]]
```

<!-- => Type u → Type v → Type (max u v) -->

---

A natural number on the left of a disjoint union with the Booleans:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[LeftInjection[2], DisjointUnion[Naturals, Booleans]]]]
```

<!-- => DisjointUnion[ℕ, 𝔹] -->
