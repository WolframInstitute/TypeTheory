---
Template: Symbol
Name: LeftInjection
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/LeftInjection
Keywords: [disjoint union, sum, injection, constructor, prelude]
SeeAlso: [DisjointUnion, RightInjection, Pair]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[LeftInjection]()[*x*]</code> is *x* on the left side of <code>[DisjointUnion]()[*α*, *β*]</code>.

## Details & Options

- [LeftInjection]() is the first constructor of [DisjointUnion]().
- *α* is found from the type of *x*; *β* is found from the expected type.

## Basic Examples

The statement of [LeftInjection]():

```wl
TypeTheoryCheck[TypeTheoryTerm[LeftInjection]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} α → DisjointUnion[α, β] -->

---

2 on the left:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[LeftInjection[2], DisjointUnion[Naturals, Booleans]]]]
```

<!-- => DisjointUnion[ℕ, 𝔹] -->
