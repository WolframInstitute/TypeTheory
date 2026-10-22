---
Template: Symbol
Name: MapJoin
Context: WolframInstitute`TypeTheory`
Paclet: WolframInstitute/TypeTheory
URI: WolframInstitute/TypeTheory/ref/MapJoin
Keywords: [list, map, join, prelude]
SeeAlso: [LengthMap, MapComposition, JoinAssociativity]
RelatedGuides: [TypeTheory]
RelatedTutorials: [ThePrelude]
---

## Usage

<code>[MapJoin]()[*f*, *a*, *b*]</code> proves <code>[Map]()[*f*, [Join]()[*a*, *b*]] == [Join]()[[Map]()[*f*, *a*], [Map]()[*f*, *b*]]</code>.

## Details & Options

- [MapJoin]() is a theorem of the prelude, proved by recursion on *a*.

## Basic Examples

The statement of [MapJoin]():

```wl
TypeTheoryCheck[TypeTheoryTerm[MapJoin]]
```

<!-- => ∀_{α ∶ Type u} ∀_{β ∶ Type v} ∀_f∶α → β ∀_a∶Lists[α] ∀_b∶Lists[α] f /@ Join[a, b] == Join[f /@ a, f /@ b] -->

---

For adding 1 to each natural number:

```wl
TypeTheoryCheck[TypeTheoryTerm[Function[{Typed[a, Lists[Naturals]], Typed[b, Lists[Naturals]]}, MapJoin[Function[{Typed[n, Naturals]}, n + 1], a, b]]]]
```

<!-- => ∀_a∶Lists[ℕ] ∀_b∶Lists[ℕ] ((n ∶ ℕ) ↦ n + 1) /@ Join[a, b] == Join[((n ∶ ℕ) ↦ n + 1) /@ a, ((n ∶ ℕ) ↦ n + 1) /@ b] -->
