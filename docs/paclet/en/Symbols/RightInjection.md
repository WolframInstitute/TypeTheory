---
Template: Symbol
Name: RightInjection
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/RightInjection
Keywords: [disjoint union, sum, injection, constructor, prelude]
SeeAlso: [DisjointUnion, LeftInjection, Pair]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[RightInjection]()[*y*]</code> is *y* on the right side of <code>[DisjointUnion]()[*α*, *β*]</code>.

## Details & Options

- [RightInjection]() is the second constructor of [DisjointUnion]().
- *β* is found from the type of *y*; *α* is found from the expected type.

## Basic Examples

The statement of [RightInjection]():

```wl
TypeTheoryCheck[TypeTheoryTerm[RightInjection]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} β → DisjointUnion[α, β] -->

---

The Boolean `"true"` on the right:

```wl
TypeTheoryCheck[TypeTheoryTerm[Typed[RightInjection["true"], DisjointUnion[Naturals, Booleans]]]]
```

<!-- => DisjointUnion[ℕ, 𝔹] -->
